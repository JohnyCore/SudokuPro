"""Move recording, notation, and variation history for Sudoku Pro.

The undo stack in the main window used to store opaque full-board snapshots,
which meant the application could not answer the only question a player
actually asks: "what just happened, and can I go back to it?". This module
records each cell mutation as a structured, reversible `Move` and keeps a
branching log so an abandoned line can be inspected instead of silently
discarded.

Notation
--------
Sudoku has no single standard, and the shorthand some players use
(``E2``, ``H2``) collides visually with chess notation and is ambiguous about
which axis is which. These styles are all supported so the move list can be
read the way you think:

* ``rc``           -- ``r2c1``   explicit row and column (the default)
* ``rcb``          -- ``r2c1 b2`` row, column, and containing box
* ``alphanumeric`` -- ``B7``     column letter + row number
* ``grid``         -- ``12``     1-based reading-order index
"""

from dataclasses import dataclass, field, replace

KIND_PLACE = "place"
KIND_ERASE = "erase"
KIND_NOTE_ADD = "note_add"
KIND_NOTE_REMOVE = "note_remove"
KIND_HINT = "hint"
KIND_SOLVER = "solver"
KIND_GIVEN = "given"

#: Kinds that write into the notes grid rather than the value grid.
NOTE_KINDS = frozenset({KIND_NOTE_ADD, KIND_NOTE_REMOVE})

#: Kinds the engine produced rather than the player.
ENGINE_KINDS = frozenset({KIND_HINT, KIND_SOLVER})

NOTATION_STYLES = ("rc", "rcb", "alphanumeric", "grid")
DEFAULT_NOTATION = "rc"


def _column_letters(index):
    """Convert a zero-based column index into spreadsheet-style letters."""
    letters = ""
    index += 1
    while index:
        index, remainder = divmod(index - 1, 26)
        letters = chr(ord("A") + remainder) + letters
    return letters


def box_index(row, col, size=9, box_rows=3, box_cols=3):
    """1-based containing box number, counted left to right then top down."""
    if box_rows <= 0 or box_cols <= 0:
        return 1
    boxes_per_row = max(1, size // box_cols)
    return (row // box_rows) * boxes_per_row + (col // box_cols) + 1


def format_cell(row, col, size=9, style=DEFAULT_NOTATION, box_rows=3, box_cols=3):
    """Render a cell in the requested notation style."""
    if style == "rc":
        return f"r{row + 1}c{col + 1}"
    if style == "rcb":
        return f"r{row + 1}c{col + 1} b{box_index(row, col, size, box_rows, box_cols)}"
    if style == "grid":
        return str(row * size + col + 1)
    if style != "alphanumeric":
        raise ValueError(f"Unknown notation style: {style}")
    return f"{_column_letters(col)}{row + 1}"


@dataclass(frozen=True)
class Move:
    """A single reversible cell mutation.

    Every field needed to invert the mutation is captured, so undo and redo
    are exact rather than approximate. In particular `previous_notes` and
    `removed_notes` cover the two non-obvious ways notes change: toggling a
    candidate, and auto-eliminating conflicting pencil marks in peer cells.
    """

    row: int
    col: int
    value: int
    previous: int
    kind: str = KIND_PLACE
    correct: bool = True
    technique: str = ""
    elapsed: int = 0
    group: int = 0
    previous_notes: tuple = ()
    removed_notes: tuple = ()
    previous_mistakes: int = 0
    previous_hint_count: int = 0
    #: Play time in seconds, to a tenth, when the move was made.
    #:
    #: `elapsed` above is the whole-second tick counter the MM:SS clock is built
    #: on, so it cannot say "0.3s". This is sampled from a monotonic clock at
    #: the moment of the move and is used only for the move list's timings, so
    #: that a fast Sudoku move is not rounded to a whole second -- which was
    #: most of them. Zero means "not measured", and the reader falls back to
    #: differencing `elapsed`.
    stamp: float = 0.0
    #: This mutation came from a hint rather than from the player's own
    #: reasoning.
    #:
    #: A separate flag rather than a `kind` of its own, so a hint stays
    #: invertible by the same code path as the move it stands in for. A hint that
    #: places a digit is still a placement, and one that eliminates a candidate
    #: is still a note removal; only the colouring and the filter need to know a
    #: hint produced it.
    from_hint: bool = False

    @property
    def is_note(self):
        return self.kind in NOTE_KINDS

    def cell(self, size=9, style=DEFAULT_NOTATION):
        return format_cell(self.row, self.col, size, style)

    def describe(self, size=9, style=DEFAULT_NOTATION):
        """Human-readable one-line summary for the move list and tooltips."""
        where = self.cell(size, style)
        if self.kind == KIND_PLACE:
            return f"{where}  {self.value}"
        if self.kind == KIND_ERASE:
            return f"{where}  cleared"
        if self.kind == KIND_NOTE_ADD:
            return f"{where}  +{self.value} pencil"
        if self.kind == KIND_NOTE_REMOVE:
            return f"{where}  -{self.value} pencil"
        if self.kind == KIND_HINT:
            return f"{where}  {self.value} (hint)"
        if self.kind == KIND_SOLVER:
            return f"{where}  {self.value} (solver)"
        if self.kind == KIND_GIVEN:
            return f"{where}  {self.value} (given)"
        return f"{where}  {self.value}"

    def tag(self):
        """Short marker used for colouring and filtering the move list."""
        if self.from_hint or self.kind == KIND_HINT:
            return "hint"
        if not self.correct:
            return "error"
        if self.kind == KIND_SOLVER:
            return "solver"
        if self.kind in NOTE_KINDS:
            return "candidate"
        return "move"
#: A move has to take at least this many seconds before "slow" means anything,
#: however the rest of the puzzle was played.
SLOW_MOVE_FLOOR = 30

#: ...and it has to be this many times the median move, so the slow ones stand
#: out from the player's own pace rather than against an absolute standard.
SLOW_MOVE_FACTOR = 3

#: Below this many timed rows a median says nothing useful.
TIMING_MINIMUM_ROWS = 5


def _with_deltas(rows):
    """Return `rows` with each one's chess-clock delta filled in.

    `Move.elapsed` is the clock reading when the move was made, so it climbs
    across the log. The figure a player wants -- how long this one took -- is the
    step between two readings, and it has to be differenced rather than shown
    raw, or every row would carry a bigger number than the one before it.

    The precise `stamp` is preferred where it is there. Two rows can share an
    `elapsed` while differing by most of a second, and differencing whole seconds
    would report that as 0. Where the stamps are missing -- an older save file,
    or moves recorded before the clock had anything to say -- this falls back to
    the integer difference rather than showing nothing.

    `MoveRow` is frozen, so this rebuilds rather than assigning in place.
    """
    previous_stamp = None
    previous_elapsed = 0
    filled = []
    for row in rows:
        if row.stamp > 0:
            # Measured from the previous stamped row, or from the start of play
            # for the first one -- which is what the very first move's timing
            # means, and reading it off `elapsed` instead reported 0 because the
            # whole-second counter had not ticked yet.
            delta = row.stamp - (previous_stamp or 0.0)
            previous_stamp = row.stamp
        else:
            delta = float(max(0, row.elapsed - previous_elapsed))
        filled.append(replace(row, delta=round(delta, 1)))
        previous_elapsed = row.elapsed
    return filled


def slow_threshold(rows):
    """Seconds after which a row is drawn as a stall.

    `None` when there are too few timed rows for a median to mean anything --
    better to mark nothing than to mark whichever single slow move happens to
    exist.
    """
    timed = [row.delta for row in rows if row.delta > 0]
    if len(timed) < TIMING_MINIMUM_ROWS:
        return None
    ordered = sorted(timed)
    middle = len(ordered) // 2
    if len(ordered) % 2:
        median = ordered[middle]
    else:
        median = (ordered[middle - 1] + ordered[middle]) / 2
    return max(SLOW_MOVE_FLOOR, SLOW_MOVE_FACTOR * median)


def _single_row(index, move):
    """One move as one row."""
    return MoveRow(
        index=index,
        end_index=index + 1,
        row=move.row,
        col=move.col,
        kind=move.kind,
        # An erase carries 0, and dropping it here is what left the row reading
        # "r6c8 b6: " with nothing after the colon.
        values=() if move.kind == KIND_ERASE else (move.value,),
        correct=move.correct,
        technique=move.technique,
        elapsed=move.elapsed,
        cells=((move.row, move.col),),
        stamp=move.stamp,
        from_hint=move.from_hint,
    )


@dataclass(frozen=True)
class MoveRow:
    """One line in the move list.

    A player who ticks five candidates into a cell has made five moves but wants
    to read one line. `MoveRow` collapses a run of consecutive pencil-mark
    changes on the same cell into a single entry carrying the *net* set of
    marks, which is the thing they actually did.
    """

    index: int
    end_index: int
    row: int = -1
    col: int = -1
    kind: str = KIND_PLACE
    values: tuple = ()
    correct: bool = True
    technique: str = ""
    elapsed: int = 0
    cells: tuple = ()
    #: The precise play-time reading this row ends on, when there was one.
    stamp: float = 0.0
    #: True when a hint produced this row, for its colour and its filter.
    from_hint: bool = False

    #: Seconds between the end of the previous row and the end of this one --
    #: the chess-clock reading. `elapsed` is cumulative, so this is what has to
    #: be differenced to answer "how long did this one take".
    delta: float = 0.0

    @property
    def cell(self):
        return None if self.row < 0 else (self.row, self.col)

    @property
    def is_pencil_run(self):
        return self.kind in NOTE_KINDS

    def tag(self):
        """Colour/filter tag, matching Move.tag for non-pencil rows."""
        if self.from_hint or self.kind == KIND_HINT:
            return "hint"
        if not self.correct:
            return "error"
        if self.kind == KIND_SOLVER:
            return "solver"
        if self.is_pencil_run:
            return "candidate"
        return "move"

    def describe(self, size=9, style=DEFAULT_NOTATION):
        """Compact one-liner: `r7c5: +1+2+3`, `r7c5: 5`, `r7c5: cleared`.

        Nothing here marks a hint. The row is already tinted for one and the
        filter picks them out, and at 180-320px wide the panel cannot spare the
        characters -- spelling it out made every hint row wide enough to push
        the timing column off the edge.
        """
        where = format_cell(self.row, self.col, size, style)
        if self.is_pencil_run:
            # One keystroke is one row, so the sign is the whole point: "+3" is
            # a mark going on, "-3" is one coming off. A run of marks used to be
            # netted into "+1+2+3", which is what produced the useless
            # "pencil cleared" rows the panel was full of.
            sign = "-" if self.kind == KIND_NOTE_REMOVE else "+"
            joined = sign + sign.join(str(value) for value in self.values)
            return f"{where}: {joined}" if self.values else f"{where}: pencil"
        if self.kind == KIND_ERASE:
            return f"{where}: Erased"
        if self.kind == KIND_PLACE:
            return f"{where}: {self.values[0] if self.values else ''}"
        suffix = {"hint": " (hint)", "solver": " (solver)", "given": " (given)"}.get(self.kind, "")
        value = self.values[0] if self.values else ""
        return f"{where}: {value}{suffix}".rstrip()


@dataclass
class MoveLog:
    """A branching record of every move made on one puzzle.

    `cursor` is the number of moves currently applied to the board, so
    `moves[:cursor]` is the live line and `moves[cursor:]` is the redo future.
    Making a move while the cursor is behind the end stores the abandoned tail
    in `variations` instead of discarding it.
    """

    moves: list = field(default_factory=list)
    cursor: int = 0
    variations: list = field(default_factory=list)
    limit: int = 1000
    _group: int = 0

    def next_group(self):
        self._group += 1
        return self._group

    @property
    def current_group(self):
        return self._group

    def record(self, move):
        """Append a move, preserving any redo future as a variation."""
        if self.cursor < len(self.moves):
            self._stash_variation()
        self.moves.append(move)
        self.cursor = len(self.moves)
        self._trim()
        return move

    def _stash_variation(self):
        abandoned = tuple(self.moves[self.cursor:])
        if abandoned:
            self.variations.append((self.cursor, abandoned))
            self.moves = self.moves[: self.cursor]

    def _trim(self):
        overflow = len(self.moves) - self.limit
        if overflow > 0:
            del self.moves[:overflow]
            self.cursor = max(0, self.cursor - overflow)
            self.variations = [
                (position - overflow, line) for position, line in self.variations if position > overflow
            ]

    def can_undo(self):
        return self.cursor > 0

    def can_redo(self):
        return self.cursor < len(self.moves)

    def peek_undo(self):
        return self.moves[self.cursor - 1] if self.can_undo() else None

    def peek_redo(self):
        return self.moves[self.cursor] if self.can_redo() else None

    def _group_start(self, index):
        """First index of the action containing `index`, or `index` itself."""
        group = self.moves[index].group
        if not group:
            return index
        start = index
        while start > 0 and self.moves[start - 1].group == group:
            start -= 1
        return start

    def undo(self):
        """Step back one *action* and return its moves, newest first.

        A single action can produce many moves: filling six selected cells, or
        applying a training step that writes candidates across a dozen. Those
        are one thing the player did, so undo should take them back together
        rather than one keystroke at a time.
        """
        if not self.can_undo():
            return ()
        end = self.cursor
        start = self._group_start(end - 1)
        self.cursor = start
        return tuple(reversed(self.moves[start:end]))

    def redo(self):
        """Step forward one action and return its moves in order."""
        if not self.can_redo():
            return ()
        end = self._group_start(self.cursor)
        group = self.moves[self.cursor].group
        if group:
            while end < len(self.moves) and self.moves[end].group == group:
                end += 1
        else:
            end += 1
        moves = tuple(self.moves[self.cursor:end])
        self.cursor = end
        return moves

    def goto(self, index):
        """Return the sequence of moves needed to reach `index`, or None.

        The list is ordered so the caller can replay it against the board.
        Moving backwards yields the moves in reverse (each already inverted by
        `apply_inverse`), moving forwards yields them in order.
        """
        index = max(0, min(int(index), len(self.moves)))
        if index < self.cursor:
            return list(reversed(self.moves[index:self.cursor]))
        if index > self.cursor:
            return list(self.moves[self.cursor:index])
        return []

    def jump_to(self, index):
        self.cursor = max(0, min(int(index), len(self.moves)))

    def applied(self):
        return self.moves[: self.cursor]

    def rows(self):
        """One row per move: exactly what the player did, in order.

        This used to collapse each keystroke's pencil marks into a single net
        line -- "+1+2+3", or "pencil cleared" when they cancelled out -- on the
        reasoning that five ticks are one thought. The panel said otherwise: a
        list of "pencil cleared" rows is unreadable, it hides which digit was
        added or taken away, and the rows are short enough that one per keystroke
        costs nothing. Collapsing also made the "Candidates" filter and the move
        timings lie about how much work a puzzle was.
        """
        return _with_deltas([_single_row(index, move)
                             for index, move in enumerate(self.moves)])

    def filtered_rows(self, kind="all"):
        """Rows matching a filter."""
        if kind == "all":
            return list(self.rows())
        wanted = {
            "errors": lambda row: not row.correct,
            "hints": lambda row: row.from_hint or row.kind == KIND_HINT,
            "candidates": lambda row: row.is_pencil_run,
        }.get(kind)
        if wanted is None:
            raise ValueError(f"Unknown move filter: {kind}")
        return [row for row in self.rows() if wanted(row)]

    def clear(self):
        self.moves.clear()
        self.variations.clear()
        self.cursor = 0
        self._group = 0

    def stats(self):
        return {
            "total": len(self.moves),
            "rows": len(self.rows()),
            "applied": self.cursor,
            "errors": sum(1 for move in self.moves if not move.correct),
            "hints": sum(1 for move in self.moves if move.kind == KIND_HINT),
            "candidates": sum(1 for move in self.moves if move.kind in NOTE_KINDS),
            "variations": len(self.variations),
        }

    def to_dict(self):
        return {
            "moves": [_move_to_dict(move) for move in self.moves],
            "cursor": self.cursor,
            "variations": [[position, [_move_to_dict(move) for move in line]] for position, line in self.variations],
            "group": self._group,
        }

    @classmethod
    def from_dict(cls, payload):
        log = cls()
        if not isinstance(payload, dict):
            return log
        for item in _as_list(payload.get("moves")):
            if isinstance(item, dict):
                log.moves.append(_move_from_dict(item))
        for entry in _as_list(payload.get("variations")):
            if not isinstance(entry, (list, tuple)) or len(entry) != 2:
                continue
            position, line = entry
            log.variations.append(
                (int(position), tuple(_move_from_dict(item) for item in _as_list(line) if isinstance(item, dict)))
            )
        log.cursor = max(0, min(int(payload.get("cursor", len(log.moves)) or 0), len(log.moves)))
        log._group = int(payload.get("group", 0) or 0)
        return log


def _as_list(value):
    """Coerce untrusted persisted data into a list without exploding."""
    return value if isinstance(value, list) else []


def _move_to_dict(move):
    return {
        "row": move.row,
        "col": move.col,
        "value": move.value,
        "previous": move.previous,
        "kind": move.kind,
        "correct": move.correct,
        "technique": move.technique,
        "elapsed": move.elapsed,
        "group": move.group,
        # previous_notes is a flat tuple of digits for the single affected
        # cell, unlike removed_notes which is a list of (row, col, value).
        "previous_notes": list(move.previous_notes),
        "removed_notes": [list(item) for item in move.removed_notes],
        "previous_mistakes": move.previous_mistakes,
        "previous_hint_count": move.previous_hint_count,
        "stamp": move.stamp,
        "from_hint": bool(move.from_hint),
    }


def _move_from_dict(item):
    return Move(
        row=int(item.get("row", 0)),
        col=int(item.get("col", 0)),
        value=int(item.get("value", 0)),
        previous=int(item.get("previous", 0)),
        kind=item.get("kind", KIND_PLACE),
        correct=bool(item.get("correct", True)),
        technique=item.get("technique", ""),
        elapsed=int(item.get("elapsed", 0)),
        group=int(item.get("group", 0)),
        previous_notes=tuple(int(notes) for notes in _as_list(item.get("previous_notes"))),
        removed_notes=tuple(tuple(int(part) for part in entry) for entry in _as_list(item.get("removed_notes")) if isinstance(entry, (list, tuple))),
        previous_mistakes=int(item.get("previous_mistakes", 0)),
        previous_hint_count=int(item.get("previous_hint_count", 0)),
        stamp=float(item.get("stamp", 0.0) or 0.0),
        from_hint=bool(item.get("from_hint", False)),
    )


def apply_forward(state, move):
    """Apply a move to a GameState-like object (board + notes)."""
    if move.kind in NOTE_KINDS:
        notes = state.notes[move.row][move.col]
        if move.kind == KIND_NOTE_ADD:
            notes.add(move.value)
        else:
            notes.discard(move.value)
    else:
        state.board[move.row][move.col] = move.value
        if move.value:
            state.notes[move.row][move.col].clear()
        for row, col, value in move.removed_notes:
            if 0 <= row < len(state.notes) and 0 <= col < len(state.notes[row]):
                state.notes[row][col].discard(value)
    # Monotonic, and deliberately so. The mistake and hint counters record what
    # the player did during this puzzle; replaying a move cannot un-do it.
    state.mistakes = max(
        state.mistakes, move.previous_mistakes + (0 if move.correct else 1))
    state.hint_count = max(state.hint_count, move.previous_hint_count)


def apply_inverse(state, move):
    """Revert a move to the board and notes it had before.

    The mistake and hint counters are left alone. They used to be restored from
    `previous_mistakes`/`previous_hint_count`, which handed back a mistake or a
    spent hint every time a player undid, redid, or scrubbed the move list --
    so a three-mistake limit could be reset one keystroke at a time and a
    one-hint challenge could be farmed indefinitely. A mistake that was entered
    was entered, whether or not the entry was then taken back. Replay can only
    raise them, never lower them.
    """
    if move.kind in NOTE_KINDS:
        state.notes[move.row][move.col] = set(move.previous_notes)
    else:
        state.board[move.row][move.col] = move.previous
        if move.previous:
            state.notes[move.row][move.col].clear()
        for row, col, value in move.removed_notes:
            if 0 <= row < len(state.notes) and 0 <= col < len(state.notes[row]):
                state.notes[row][col].add(value)
