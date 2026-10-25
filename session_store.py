import json
import os
import re
import shutil
import tempfile
from datetime import datetime, timezone
from pathlib import Path

APP_VERSION = "1.0"
SCHEMA_VERSION = 2


class SessionStore:
    def __init__(self, data_dir, filename="sudoku_save.json"):
        self.data_dir = Path(data_dir)
        self.path = self.data_dir / filename
        self.backup_path = self.data_dir / f"{filename}.bak"
        self.history_dir = self.data_dir / "savepoints"
        self.history_dir.mkdir(parents=True, exist_ok=True)

    def save(self, session):
        payload = self._envelope(session)
        if self.path.exists():
            shutil.copy2(self.path, self.backup_path)
        self._atomic_json(self.path, payload)
        if not self.backup_path.exists():
            shutil.copy2(self.path, self.backup_path)
        return payload

    def load(self):
        for path in (self.path, self.backup_path):
            payload = self.read(path)
            if payload is not None:
                return payload
        return None

    @classmethod
    def migrate(cls, payload):
        """Wrap a v1 save -- a bare session with no envelope -- in one.

        The first version wrote the session fields at the top level, so
        ``schema_version`` was a sibling of ``board`` rather than a parent of
        it. Those files are still on disk and have to keep working; a rewrite
        would silently drop a player's game.
        """
        if not isinstance(payload, dict):
            return None
        if isinstance(payload.get("session"), dict):
            return payload if cls._validate_envelope(payload) else None
        if isinstance(payload.get("board"), list):
            # v1: the session *is* the document.
            wrapped = {
                "app_version": payload.get("app_version", APP_VERSION),
                "schema_version": SCHEMA_VERSION,
                "saved_at": datetime.now(timezone.utc).isoformat(),
                "session": {key: value for key, value in payload.items()
                            if key not in ("app_version", "schema_version", "saved_at")},
            }
            return wrapped if cls._validate_envelope(wrapped) else None
        return None

    def read(self, path):
        """One save file, migrated to the current envelope, or None."""
        try:
            return self.migrate(json.loads(Path(path).read_text(encoding="utf-8")))
        except (FileNotFoundError, OSError, json.JSONDecodeError, TypeError, ValueError):
            return None

    def create_savepoint(self, name, session):
        safe_name = re.sub(r"[^A-Za-z0-9 _-]", "", str(name)).strip() or "savepoint"
        path = self.history_dir / f"{safe_name}.json"
        payload = self._envelope(session)
        payload["savepoint_name"] = safe_name
        payload["saved_at"] = datetime.now(timezone.utc).isoformat()
        self._atomic_json(path, payload)
        return path

    def list_savepoints(self):
        return sorted(self.history_dir.glob("*.json"), key=lambda path: path.stat().st_mtime, reverse=True)

    def restore_savepoint(self, path):
        session = self.migrate(json.loads(Path(path).read_text(encoding="utf-8")))
        if session is None:
            raise ValueError("Savepoint is invalid")
        self.save(session["session"])
        return session["session"]

    def export_backup(self, path):
        loaded = self.load()
        if loaded is None:
            raise ValueError("No valid saved session to export")
        self._atomic_json(Path(path), self._envelope(loaded["session"]))

    def import_backup(self, path):
        session = self.migrate(json.loads(Path(path).read_text(encoding="utf-8")))
        if session is None:
            raise ValueError("Backup is invalid")
        self.save(session["session"])
        return session["session"]

    def _envelope(self, session):
        return {
            "app_version": APP_VERSION,
            "schema_version": SCHEMA_VERSION,
            "saved_at": datetime.now(timezone.utc).isoformat(),
            "session": session,
        }

    @staticmethod
    def _validate_envelope(payload):
        return isinstance(payload, dict) and payload.get("schema_version") == SCHEMA_VERSION and isinstance(payload.get("session"), dict) and isinstance(payload["session"].get("board"), list) and len(payload["session"]["board"]) <= 100

    def _atomic_json(self, path, payload):
        path = Path(path)
        path.parent.mkdir(parents=True, exist_ok=True)
        temporary = None
        try:
            with tempfile.NamedTemporaryFile("w", encoding="utf-8", dir=path.parent, prefix=path.name + ".", suffix=".tmp", delete=False) as handle:
                temporary = Path(handle.name)
                json.dump(payload, handle, indent=2)
                handle.flush()
                os.fsync(handle.fileno())
            os.replace(temporary, path)
            temporary = None
        finally:
            if temporary is not None:
                temporary.unlink(missing_ok=True)


#: The tag on the delimited form of the puzzle text. The compact form has no
#: tag, because every file written before a board needed one looks exactly like
#: this and has to keep loading.
PLAIN_TAG = "v2"

#: Board sizes the text format accepts. Kept in step with the generator in
#: main.py; `tests/test_session_store.py` asserts the two agree.
PLAIN_SIZES = (4, 6, 8, 9, 10, 12, 15, 16)

#: Separates cells in the delimited form, and the notes within one cell.
CELL_SEPARATOR = ";"
VALUE_SEPARATOR = ","

_BLANKS = "0."


def _blank(digits):
    return digits[0] if digits else "0"


def puzzle_to_plain(board, digits="0", separator=""):
    """A board as text.

    A value above 9 is two characters wide, so a board that contains one cannot
    be written as one character per cell -- the reader would have no way to know
    where a cell ended. Those boards get the delimited `v2` form instead. Every
    board whose digits all fit in one character keeps the original compact form,
    so a 9x9 is written exactly as it always was and existing files load
    unchanged.
    """
    size = len(board)
    values = [value for row in board for value in row]
    if any(not isinstance(value, int) or not 0 <= value <= size for value in values):
        raise ValueError("Board contains a value outside the board's range")
    blank = _blank(digits)
    if all(value <= 9 for value in values):
        # The original expression, kept verbatim: every saved file starts with
        # exactly this.
        return separator.join(str(value).replace("0", blank) for value in values)
    body = VALUE_SEPARATOR.join(str(value) for value in values)
    return f"{PLAIN_TAG}:{size}:{body}"


def puzzle_from_plain(text):
    """Read a board back from `puzzle_to_plain`, in either form."""
    raw = str(text).strip()
    if raw[: len(PLAIN_TAG) + 1].upper() == f"{PLAIN_TAG.upper()}:":
        return _board_from_delimited(raw)
    return _board_from_compact(raw)


def _board_from_compact(text):
    """One character per cell: the format every existing file uses."""
    values = [character for character in str(text).strip() if not character.isspace()]
    total = len(values)
    if total == 0 or int(total ** 0.5) ** 2 != total:
        raise ValueError("Puzzle text does not describe a square board")
    size = int(total ** 0.5)
    if size not in PLAIN_SIZES:
        raise ValueError(f"Unsupported board size ({size})")
    allowed = set(_BLANKS + "123456789")
    if any(character not in allowed for character in values):
        raise ValueError("Puzzle text contains invalid characters")
    return [
        [
            0 if character in _BLANKS else int(character)
            for character in values[row * size:(row + 1) * size]
        ]
        for row in range(size)
    ]


def _board_from_delimited(text):
    """`v2:16:5,3,4,...` -- explicit size, then every value."""
    parts = text.split(":", 2)
    if len(parts) != 3:
        raise ValueError("Delimited puzzle text is malformed")
    try:
        size = int(parts[1])
    except ValueError:
        raise ValueError("Delimited puzzle text has no board size") from None
    if size not in PLAIN_SIZES:
        raise ValueError(f"Unsupported board size ({size})")
    cells = parts[2].split(VALUE_SEPARATOR)
    if len(cells) != size * size:
        raise ValueError(
            f"Delimited puzzle text has {len(cells)} values, expected {size * size}"
        )
    board = []
    for row in range(size):
        parsed_row = []
        for cell in cells[row * size:(row + 1) * size]:
            cell = cell.strip()
            if cell in _BLANKS or cell == "":
                parsed_row.append(0)
                continue
            try:
                value = int(cell)
            except ValueError:
                raise ValueError("Puzzle text contains invalid characters") from None
            if not 0 <= value <= size:
                raise ValueError("Puzzle text contains an out-of-range value")
            parsed_row.append(value)
        board.append(parsed_row)
    return board


def puzzle_with_notes(board, notes, size=9):
    """A board and its pencil marks as text.

    One line per row of notes. Cells within a row are separated by `;` and the
    values inside one cell by `,`. The old version joined both with `,` and
    dropped the cell boundary, so a cell holding {2, 4} next to one holding {5}
    and a cell holding nothing all wrote as `2,4,5` -- unreadable. The `;`
    keeps an empty cell as an empty field.
    """
    if len(board) != size or any(len(row) != size for row in board) or len(notes) != size or any(len(row) != size for row in notes):
        raise ValueError("Board and notes dimensions do not match")
    lines = [puzzle_to_plain(board)]
    for row in notes:
        lines.append(CELL_SEPARATOR.join(
            VALUE_SEPARATOR.join(str(value) for value in sorted(cell))
            for cell in row
        ))
    return "\n".join(lines)


def notes_from_plain(text):
    """The pencil marks written by `puzzle_with_notes`, read back.

    Returns None when the text carries no notes at all, which is the normal
    case for a board that came from `puzzle_to_plain` rather than from
    `puzzle_with_notes`.
    """
    lines = [line for line in str(text).splitlines() if line.strip()]
    if len(lines) <= 1:
        return None
    board = puzzle_from_plain(lines[0])
    size = len(board)
    if len(lines) - 1 != size:
        raise ValueError(
            f"Note text has {len(lines) - 1} rows, expected {size}"
        )
    rows = []
    for line in lines[1:]:
        cells = line.split(CELL_SEPARATOR)
        if len(cells) != size:
            raise ValueError(
                f"A note row has {len(cells)} cells, expected {size}"
            )
        parsed: list = []
        for cell in cells:
            if not cell.strip():
                parsed.append(set())
                continue
            values = set()
            for piece in cell.split(VALUE_SEPARATOR):
                piece = piece.strip()
                if not piece:
                    continue
                try:
                    value = int(piece)
                except ValueError:
                    raise ValueError("Note text contains an invalid value") from None
                if not 1 <= value <= size:
                    raise ValueError("Note text contains an out-of-range value")
                values.add(value)
            parsed.append(values)
        rows.append(parsed)
    return rows


def parse_import_lines(text):
    puzzles = []
    errors = []
    for line_number, line in enumerate(str(text).splitlines(), start=1):
        if not line.strip() or line.lstrip().startswith("#"):
            continue
        try:
            puzzles.append(puzzle_from_plain(line.split("#", 1)[0].strip()))
        except ValueError as error:
            errors.append((line_number, str(error)))
    return puzzles, errors
