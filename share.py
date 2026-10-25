"""Shareable session codes: a whole game in one string instead of a file.

The existing seed already round-trips a puzzle through
`base64(urlsafe) ∘ zlib ∘ json`, but it carries the board and the solution as
JSON, which costs ~376 characters before a single move is added. Adding a
50-move history as JSON pushes that past 800 characters, which nobody pastes
into a chat window.

Two changes fix that:

* **Regenerate, don't ship.** Generation is deterministic from the seed, so a
  code for an app-generated puzzle only needs the 12-character identity plus
  the moves. The board and solution are rebuilt on the other side.
* **Binary the moves.** A move needs row, column, value and kind -- four
  nibbles, two bytes. JSON spends ~195 bytes describing what fits in two.

The result is ~4 bytes per move instead of ~195, which puts a full session
around 300 characters and a placements-only trace under 60.

A share code is deliberately *forward-only*. It records what happened, not the
opposite move, because the recipient replays rather than undoes. Undo history
is rebuilt locally from the replayed state.
"""

import base64
import hashlib
import json
import struct
import zlib
from dataclasses import dataclass

MAGIC = "SK1"
FORMAT_VERSION = 1

#: Stable difficulty identifiers. These are positional, so entries may only be
#: appended -- reordering them would invalidate every code already shared.
DIFFICULTY_IDS = ("Easy", "Medium", "Hard", "Expert")

KIND_CODES = {"place": 0, "erase": 1, "note_add": 2, "note_remove": 3, "hint": 4, "solver": 5, "given": 6}
KIND_NAMES = {value: key for key, value in KIND_CODES.items()}

FLAG_CORRECT = 0b1
FLAG_LAST_OF_GROUP = 0b10

MAX_ELAPSED_DELTA = 255
MAX_MOVES = 4096

# Named so the field order is readable rather than positional guesswork.
# Ten fields, 18 bytes, in this order:
#   version, flags, size, box_rows, box_cols, difficulty_id  (six uint8)
#   seed                                                      (uint64)
#   move_count                                                (uint16)
#   reserved, checksum                                        (two uint8)
HEADER = struct.Struct(">6BQH2B")

#: The wire format's fixed size. Guarded by a test rather than an ``assert``:
#: ``python -O`` strips asserts, so an assert here would let a changed struct
#: layout through in exactly the build most likely to ship.
HEADER_SIZE = 18
_HEADER_FIELDS = (
    "version",
    "flags",
    "size",
    "box_rows",
    "box_cols",
    "difficulty_id",
    "seed",
    "move_count",
    "reserved",
    "checksum",
)

#: Variant ids, packed into the high bits of `flags` (bit 0 is `explicit_board`,
#: so bits 1-3 are free). The `reserved` byte looks like the obvious home and is
#: not: `CHECKSUM_SLICE` spans the last two header bytes and the struct declares
#: those as `reserved, checksum`, so the 16-bit checksum already writes over
#: `reserved` on every encode. Bits 0 is `explicit`; the rest is the variant id.
VARIANT_IDS = ("standard", "diagonal", "anti_diagonal", "killer", "odd_even")
_VARIANT_SHIFT = 1


def _variant_id(variant: str) -> int:
    return VARIANT_IDS.index(variant) if variant in VARIANT_IDS else 0


def _variant_from_flags(flags: int) -> str:
    value = flags >> _VARIANT_SHIFT
    return VARIANT_IDS[value] if 0 <= value < len(VARIANT_IDS) else "standard"
MOVE = struct.Struct(">BBBB")


class ShareError(ValueError):
    """Raised when a share code cannot be trusted or understood."""


@dataclass(frozen=True)
class SharedSession:
    """A decoded session: where the puzzle came from, and what was played."""

    difficulty: str = "Medium"
    size: int = 9
    box_rows: int = 3
    box_cols: int = 3
    seed: int = 0
    board: tuple = ()
    solution: tuple = ()
    explicit_board: bool = False
    moves: tuple = ()
    variant: str = "standard"

    @property
    def is_replayable(self):
        """True when the puzzle can be regenerated rather than shipped."""
        return not self.explicit_board and bool(self.seed)


def encode_moves(moves, placements_only=False):
    """Pack a MoveLog's moves into a tight byte string.

    Each move costs four bytes: row/column, value/kind, flags, and the seconds
    elapsed since the previous move (saturating, which is ample for a human
    pace and keeps the encoding fixed-width).
    """
    packed = bytearray()
    previous_elapsed = 0
    for move in moves:
        if placements_only and move.kind in {"note_add", "note_remove"}:
            continue
        kind = KIND_CODES.get(move.kind)
        if kind is None:
            raise ShareError(f"Unsupported move kind: {move.kind}")
        if not (0 <= move.row < 16 and 0 <= move.col < 16):
            raise ShareError("Move is outside the encodable range")
        if not 0 <= move.value < 16:
            raise ShareError("Move value is outside the encodable range")
        elapsed = max(0, int(move.elapsed) - previous_elapsed)
        previous_elapsed = int(move.elapsed)
        flags = FLAG_CORRECT if move.correct else 0
        if move.group:
            flags |= FLAG_LAST_OF_GROUP
        packed += MOVE.pack(
            (move.row << 4) | move.col,
            (move.value << 4) | kind,
            flags,
            min(MAX_ELAPSED_DELTA, elapsed),
        )
    return bytes(packed)


def decode_moves(blob, expected=None):
    """Unpack the binary move stream back into Move objects."""
    from moves import Move  # local import: moves.py must not depend on this module

    if len(blob) % MOVE.size:
        raise ShareError("Move data is truncated")
    out: list = []
    for offset in range(0, len(blob), MOVE.size):
        rowcol, value_kind, flags, delta = MOVE.unpack_from(blob, offset)
        kind = KIND_NAMES.get(value_kind & 0x0F)
        if kind is None:
            raise ShareError("Move data contains an unknown technique marker")
        out.append(
            Move(
                row=rowcol >> 4,
                col=rowcol & 0x0F,
                value=value_kind >> 4,
                previous=0,
                kind=kind,
                correct=bool(flags & FLAG_CORRECT),
                elapsed=(out[-1].elapsed if out else 0) + delta,
                group=1 if flags & FLAG_LAST_OF_GROUP else 0,
            )
        )
    if expected is not None and len(out) != expected:
        raise ShareError(f"Expected {expected} moves but found {len(out)}")
    return tuple(out)


def _checksum(payload):
    return int.from_bytes(hashlib.sha256(payload).digest()[:2], "big")


#: Byte offsets of the reserved and checksum fields inside the packed header.
CHECKSUM_SLICE = slice(HEADER.size - 2, HEADER.size)


def _checksum_over(body):
    """Checksum of a body with the checksum field treated as zero."""
    return _checksum(bytes(body[: CHECKSUM_SLICE.start]) + b"\x00\x00" + bytes(body[CHECKSUM_SLICE.stop:]))


def encode_session(
    difficulty="Medium",
    size=9,
    box_rows=3,
    box_cols=3,
    seed=0,
    moves=(),
    board=None,
    solution=None,
    variant="standard",
    placements_only=False,
):
    """Produce a share code.

    When `board`/`solution` are omitted the code relies on regenerating the
    puzzle from `seed`. Pass them explicitly for imported or hand-made
    puzzles, which have no generation seed.
    """
    if difficulty not in DIFFICULTY_IDS:
        difficulty = "Medium"
    explicit = board is not None and solution is not None
    packed = encode_moves(moves, placements_only=placements_only)
    if len(packed) // MOVE.size > MAX_MOVES:
        raise ShareError("Too many moves to share")

    flags = 0b1 if explicit else 0
    flags |= _variant_id(variant) << _VARIANT_SHIFT
    body = bytearray(HEADER.pack(
        FORMAT_VERSION,
        flags,
        int(size) & 0xFF,
        int(box_rows) & 0xFF,
        int(box_cols) & 0xFF,
        DIFFICULTY_IDS.index(difficulty),
        int(seed) & 0xFFFFFFFFFFFFFFFF,
        min(MAX_MOVES, len(packed) // MOVE.size),
        0,
        0,
    ))
    if explicit:
        for grid in (board, solution):
            for row in grid:
                if len(row) != size:
                    raise ShareError("Board dimensions do not match the declared size")
                for value in row:
                    if not 0 <= int(value) < 16:
                        raise ShareError("Board contains a value that cannot be encoded")
                body.extend(bytes(int(v) & 0xFF for v in row))
    body.extend(packed)

    # The last two header bytes hold the checksum; compute it with those bytes
    # treated as zero, then write it in.
    checksum = _checksum_over(body)
    body[CHECKSUM_SLICE.start] = (checksum >> 8) & 0xFF
    body[CHECKSUM_SLICE.stop - 1] = checksum & 0xFF
    return MAGIC + base64.urlsafe_b64encode(zlib.compress(bytes(body), 9)).decode("ascii").rstrip("=")


def decode_session(code):
    """Parse and validate a share code."""
    if not isinstance(code, str):
        raise ShareError("Share code must be text")
    text = code.strip()
    if not text.startswith(MAGIC):
        raise ShareError("This does not look like a Sudoku Pro session code")
    payload = text[len(MAGIC):]
    padding = "=" * (-len(payload) % 4)
    try:
        raw = zlib.decompress(base64.urlsafe_b64decode(payload + padding))
    except Exception as error:
        raise ShareError("Share code is corrupt or incomplete") from error
    if len(raw) < HEADER.size:
        raise ShareError("Share code is too short to be valid")

    header = dict(zip(_HEADER_FIELDS, HEADER.unpack_from(raw, 0), strict=True))
    version = header["version"]
    flags = header["flags"]
    size = header["size"]
    box_rows = header["box_rows"]
    box_cols = header["box_cols"]
    difficulty_id = header["difficulty_id"]
    seed = header["seed"]
    move_count = header["move_count"]
    # The 16-bit checksum spans the last two header bytes, big-endian.
    checksum = (raw[CHECKSUM_SLICE.start] << 8) | raw[CHECKSUM_SLICE.stop - 1]
    if version != FORMAT_VERSION:
        raise ShareError(f"Share code uses unsupported format version {version}")
    if _checksum_over(raw) != checksum:
        raise ShareError("Share code failed its checksum; it was probably altered in transit")

    cursor = HEADER.size
    board: tuple = ()
    solution: tuple = ()
    explicit = bool(flags & 0b1)
    if explicit:
        needed = size * size * 2
        if len(raw) < cursor + needed:
            raise ShareError("Share code is missing its board data")
        blob = raw[cursor:cursor + needed]
        half = size * size
        board = tuple(tuple(blob[r * size:(r + 1) * size]) for r in range(size))
        solution = tuple(tuple(blob[half + r * size: half + (r + 1) * size]) for r in range(size))
        cursor += needed

    packed = raw[cursor:]
    if len(packed) != move_count * MOVE.size:
        raise ShareError("Share code move count does not match its payload")
    moves = decode_moves(packed, expected=move_count)
    return SharedSession(
        difficulty=DIFFICULTY_IDS[difficulty_id] if difficulty_id < len(DIFFICULTY_IDS) else "Medium",
        size=size,
        box_rows=box_rows,
        box_cols=box_cols,
        seed=seed,
        board=board,
        solution=solution,
        variant=_variant_from_flags(flags),
        explicit_board=explicit,
        moves=moves,
    )


def to_json(session):
    """A human-readable rendering, for pasting into a bug report or notes."""
    return json.dumps(
        {
            "format": "sudoku-pro-session",
            "version": FORMAT_VERSION,
            "difficulty": session.difficulty,
            "size": session.size,
            "box_rows": session.box_rows,
            "box_cols": session.box_cols,
            "seed": session.seed,
            "regeneratable": session.is_replayable,
            "moves": [
                {
                    "cell": f"r{m.row + 1}c{m.col + 1}",
                    "value": m.value,
                    "kind": m.kind,
                    "correct": m.correct,
                    "elapsed": m.elapsed,
                }
                for m in session.moves
            ],
        },
        indent=2,
    )


def describe(code):
    """One-line summary of a code, without decoding the moves in full."""
    session = decode_session(code)
    wrong = sum(1 for move in session.moves if not move.correct)
    source = "regenerated from seed" if session.is_replayable else "carries its own board"
    return f"{session.difficulty} {session.size}x{session.size}, {len(session.moves)} moves, {wrong} mistake(s), {source}"
