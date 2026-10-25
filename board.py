from dataclasses import dataclass
from enum import Enum


class ValidationStatus(str, Enum):
    VALID = "valid"
    INCOMPLETE = "incomplete"
    INVALID = "invalid"


@dataclass(frozen=True)
class ValidationResult:
    status: ValidationStatus
    errors: tuple[str, ...] = ()
    missing_cells: tuple[tuple[int, int], ...] = ()

    @property
    def is_valid(self):
        return self.status == ValidationStatus.VALID

    @property
    def is_incomplete(self):
        return self.status == ValidationStatus.INCOMPLETE

    @property
    def is_invalid(self):
        return self.status == ValidationStatus.INVALID

    def __bool__(self):
        return self.is_valid


class CellSource(str, Enum):
    EMPTY = "empty"
    GIVEN = "given"
    USER = "user"
    HINT = "hint"
    SOLUTION = "solution"


@dataclass(frozen=True)
class Selection:
    cells: tuple[tuple[int, int], ...]
    size: int

    def __post_init__(self):
        if self.size <= 0:
            raise ValueError("Board size must be positive")
        normalized = []
        for row, col in self.cells:
            cell = clip_cell((row, col), self.size)
            if cell is not None and cell not in normalized:
                normalized.append(cell)
        object.__setattr__(self, "cells", tuple(normalized))

    @classmethod
    def create(cls, cells, size, wrap=False):
        selected = []
        for cell in cells:
            normalized = normalize_cell(cell, size, wrap)
            if normalized is not None and normalized not in selected:
                selected.append(normalized)
        return cls(tuple(selected), size)

    @property
    def active(self):
        return self.cells[-1] if self.cells else None

    def move(self, row_delta, col_delta, wrap=False, extend=False):
        if not self.cells:
            return self
        moved = normalize_cell((self.active[0] + row_delta, self.active[1] + col_delta), self.size, wrap)
        if moved is None or moved == self.active:
            return self
        if extend and moved not in self.cells:
            return Selection(self.cells + (moved,), self.size)
        return Selection((moved,), self.size)

    def toggle(self, cell, wrap=False):
        normalized = normalize_cell(cell, self.size, wrap)
        if normalized is None:
            return self
        if normalized in self.cells:
            return Selection(tuple(item for item in self.cells if item != normalized), self.size)
        return Selection(self.cells + (normalized,), self.size)

    def clipped(self):
        return Selection(self.cells, self.size)


def clip_cell(cell, size):
    row, col = cell
    if 0 <= row < size and 0 <= col < size:
        return (row, col)
    return None


def wrap_cell(cell, size):
    row, col = cell
    return (row % size, col % size)


def normalize_cell(cell, size, wrap=False):
    if wrap:
        return wrap_cell(cell, size)
    return clip_cell(cell, size)


def grid_to_rc(index, size=9):
    if index < 0:
        raise ValueError("Grid index cannot be negative")
    if index >= size * size:
        raise ValueError("Grid index is outside the board")
    return divmod(index, size)


def rc_to_grid(row, col, size=9):
    if row < 0 or col < 0 or row >= size or col >= size:
        raise ValueError("Coordinates are outside the board")
    return row * size + col


def notation_to_rc(notation):
    if len(notation) < 2:
        raise ValueError("Notation must contain a row and column")
    letters = ""
    digits = ""
    for character in notation.strip().upper():
        if character.isalpha() and not digits:
            letters += character
        elif character.isdigit():
            digits += character
        else:
            raise ValueError("Invalid Sudoku notation")
    if not letters or not digits:
        raise ValueError("Notation must contain a row and column")
    col = 0
    for character in letters:
        col = col * 26 + ord(character) - ord("A") + 1
    return (int(digits) - 1, col - 1)


def rc_to_notation(row, col):
    if row < 0 or col < 0:
        raise ValueError("Coordinates cannot be negative")
    letters = ""
    col += 1
    while col:
        col, remainder = divmod(col - 1, 26)
        letters = chr(ord("A") + remainder) + letters
    return f"{letters}{row + 1}"


@dataclass(frozen=True)
class Board:
    size: int
    box_rows: int
    box_cols: int
    values: tuple[tuple[int, ...], ...]
    sources: tuple[tuple[CellSource, ...], ...]
    notes: tuple[tuple[frozenset[int], ...], ...]

    def __post_init__(self):
        if self.size <= 0 or self.box_rows <= 0 or self.box_cols <= 0:
            raise ValueError("Board dimensions must be positive")
        if self.size % self.box_rows or self.size % self.box_cols:
            raise ValueError("Box dimensions must evenly divide the board")
        if len(self.values) != self.size or len(self.sources) != self.size or len(self.notes) != self.size:
            raise ValueError("Board grids must have matching dimensions")
        normalized_values = tuple(tuple(row) for row in self.values)
        normalized_sources = tuple(tuple(source) for source in self.sources)
        normalized_notes = tuple(tuple(frozenset(cell) for cell in row) for row in self.notes)
        for row in range(self.size):
            if len(normalized_values[row]) != self.size or len(normalized_sources[row]) != self.size or len(normalized_notes[row]) != self.size:
                raise ValueError("Board rows must have matching dimensions")
            for col in range(self.size):
                value = normalized_values[row][col]
                source = normalized_sources[row][col]
                notes = normalized_notes[row][col]
                if not isinstance(value, int) or not 0 <= value <= self.size:
                    raise ValueError("Board values must be between zero and the board size")
                if not isinstance(source, CellSource):
                    raise ValueError("Board sources must be CellSource values")
                if source == CellSource.EMPTY and value:
                    raise ValueError("A non-empty cell must have a source")
                if source != CellSource.EMPTY and not value:
                    raise ValueError("An empty cell must use the empty source")
                if not notes.issubset(set(range(1, self.size + 1))):
                    raise ValueError("Notes must be valid board values")
        if self.validate().is_invalid:
            raise ValueError("Board contains duplicate values in a unit")
        object.__setattr__(self, "values", normalized_values)
        object.__setattr__(self, "sources", normalized_sources)
        object.__setattr__(self, "notes", normalized_notes)

    @classmethod
    def empty(cls, size=9, box_rows=3, box_cols=3):
        return cls(
            size,
            box_rows,
            box_cols,
            tuple(tuple(0 for _ in range(size)) for _ in range(size)),
            tuple(tuple(CellSource.EMPTY for _ in range(size)) for _ in range(size)),
            tuple(tuple(frozenset() for _ in range(size)) for _ in range(size)),
        )

    @classmethod
    def _lenient(cls, size, box_rows, box_cols, values, sources, notes):
        """Build a board without rejecting duplicate values inside a unit.

        Incremental edits (with_value/with_note) must be allowed to create a
        temporarily conflicting board: the caller is mid-edit and validate()
        is what surfaces the conflict to the user. Strict rejection stays on
        the constructor path so untrusted input (from_grids) is still refused.
        """
        board = object.__new__(cls)
        object.__setattr__(board, "size", size)
        object.__setattr__(board, "box_rows", box_rows)
        object.__setattr__(board, "box_cols", box_cols)
        object.__setattr__(board, "values", tuple(tuple(row) for row in values))
        object.__setattr__(board, "sources", tuple(tuple(row) for row in sources))
        object.__setattr__(board, "notes", tuple(tuple(frozenset(cell) for cell in row) for row in notes))
        return board

    @classmethod
    def from_grids(cls, values, box_rows=3, box_cols=3, sources=None, notes=None):
        size = len(values)
        normalized_sources = sources or tuple(
            tuple(CellSource.GIVEN if value else CellSource.EMPTY for value in row)
            for row in values
        )
        normalized_notes = notes or tuple(tuple(set() for _ in row) for row in values)
        return cls(size, box_rows, box_cols, tuple(tuple(row) for row in values), tuple(tuple(row) for row in normalized_sources), tuple(tuple(row) for row in normalized_notes))

    def validate(self, require_complete=False, variant=None, cages=None):
        errors = []
        missing = []
        for row in range(self.size):
            for col in range(self.size):
                if not self.values[row][col]:
                    missing.append((row, col))
        for row in range(self.size):
            seen: dict = {}
            for col in range(self.size):
                value = self.values[row][col]
                if value and value in seen:
                    errors.append(f"row {row + 1} repeats value {value} at columns {seen[value] + 1} and {col + 1}")
                elif value:
                    seen[value] = col
        for col in range(self.size):
            seen = {}
            for row in range(self.size):
                value = self.values[row][col]
                if value and value in seen:
                    errors.append(f"column {col + 1} repeats value {value} at rows {seen[value] + 1} and {row + 1}")
                elif value:
                    seen[value] = row
        for box_index, unit in enumerate(self.units()[2 * self.size:]):
            # Its own name, not a second `seen`: the row loop above maps a
            # value to a row index and this one maps it to a (row, col) pair,
            # so sharing the name made the two indistinguishable by eye.
            seen_cells: dict = {}
            for row, col in unit:
                value = self.values[row][col]
                if value and value in seen_cells:
                    other_row, other_col = seen_cells[value]
                    errors.append(f"box {box_index + 1} repeats value {value} at ({other_row + 1},{other_col + 1}) and ({row + 1},{col + 1})")
                elif value:
                    seen_cells[value] = (row, col)
        if variant in {"diagonal", "diagonal_anti"}:
            for name, coordinates in (("main diagonal", [(index, index) for index in range(self.size)]), ("anti-diagonal", [(index, self.size - index - 1) for index in range(self.size)])):
                if name == "anti-diagonal" and variant == "diagonal":
                    continue
                values = [self.values[row][col] for row, col in coordinates if self.values[row][col]]
                if len(values) != len(set(values)):
                    errors.append(f"{name} repeats a value")
        if variant == "odd_even":
            filled = [(row, col, self.values[row][col]) for row in range(self.size) for col in range(self.size) if self.values[row][col]]
            if filled:
                first_row, first_col, first_value = filled[0]
                first_parity = first_value % 2
                for row, col, value in filled:
                    expected_parity = first_parity if (row + col - first_row - first_col) % 2 == 0 else 1 - first_parity
                    if value % 2 != expected_parity:
                        errors.append(f"cell ({row + 1},{col + 1}) violates odd/even parity")
            parity_origin = (filled[0][0] + filled[0][1]) % 2 if filled else 0
            parity_is_odd = (filled[0][2] % 2 == 1) if filled else True
            for row, col in missing:
                expected_odd = ((row + col) % 2 == parity_origin) == parity_is_odd
                candidates = {value for value in range(1, self.size + 1) if (value % 2 == 1) == expected_odd}
                if not candidates:
                    errors.append(f"cell ({row + 1},{col + 1}) has no valid odd/even candidate")
        if cages is not None:
            cage_error = validate_cages(cages, self.size, self.values if require_complete else None)
            if cage_error:
                errors.append(cage_error)
        if errors:
            return ValidationResult(ValidationStatus.INVALID, tuple(errors), tuple(missing))
        if missing:
            return ValidationResult(ValidationStatus.INCOMPLETE, tuple(f"cell ({row + 1},{col + 1}) is empty" for row, col in missing), tuple(missing))
        return ValidationResult(ValidationStatus.VALID, (), ())

    def units(self):
        result: list = []
        result.extend(tuple((row, col) for col in range(self.size)) for row in range(self.size))
        result.extend(tuple((row, col) for row in range(self.size)) for col in range(self.size))
        boxes_per_row = self.size // self.box_cols
        for box_index in range(boxes_per_row * (self.size // self.box_rows)):
            start_row = (box_index // boxes_per_row) * self.box_rows
            start_col = (box_index % boxes_per_row) * self.box_cols
            result.append(tuple((row, col) for row in range(start_row, start_row + self.box_rows) for col in range(start_col, start_col + self.box_cols)))
        return tuple(result)

    def unit_for(self, row, col):
        cell = (row, col)
        return tuple(unit for unit in self.units() if cell in unit)

    def with_value(self, row, col, value, source=CellSource.USER):
        if source == CellSource.GIVEN and self.sources[row][col] == CellSource.GIVEN:
            raise ValueError("Givens cannot be replaced")
        if value < 0 or value > self.size:
            raise ValueError("Value is outside the board range")
        values = [list(board_row) for board_row in self.values]
        sources = [list(source_row) for source_row in self.sources]
        values[row][col] = value
        sources[row][col] = CellSource.EMPTY if value == 0 else source
        notes = [list(note_row) for note_row in self.notes]
        if value:
            notes[row][col] = frozenset()
        return Board._lenient(self.size, self.box_rows, self.box_cols, tuple(tuple(row_values) for row_values in values), tuple(tuple(row_sources) for row_sources in sources), tuple(tuple(row_notes) for row_notes in notes))

    def with_note(self, row, col, value, enabled=True):
        if not 1 <= value <= self.size:
            raise ValueError("Note is outside the board range")
        if self.values[row][col]:
            raise ValueError("A filled cell cannot contain notes")
        notes = [list(note_row) for note_row in self.notes]
        notes[row][col] = frozenset(set(notes[row][col]) ^ {value}) if enabled else frozenset()
        return Board._lenient(self.size, self.box_rows, self.box_cols, self.values, self.sources, tuple(tuple(row_notes) for row_notes in notes))

def validate_cages(cages, size, solution=None):
    if not isinstance(cages, list):
        return "cages must be a list"
    covered = set()
    for index, cage in enumerate(cages, start=1):
        if not isinstance(cage, dict) or not isinstance(cage.get("cells"), list) or not cage["cells"]:
            return f"cage {index} is malformed"
        if not isinstance(cage.get("sum"), int) or cage["sum"] <= 0:
            return f"cage {index} has an invalid sum"
        cells = set()
        for cell in cage["cells"]:
            if not isinstance(cell, (list, tuple)) or len(cell) != 2 or not all(isinstance(value, int) for value in cell):
                return f"cage {index} has a malformed cell"
            coordinate = (cell[0], cell[1])
            if not (0 <= coordinate[0] < size and 0 <= coordinate[1] < size):
                return f"cage {index} references a cell outside the board"
            if coordinate in covered:
                return f"cage {index} overlaps another cage"
            covered.add(coordinate)
            cells.add(coordinate)
        if len(cells) > 1 and any(not any(abs(row - other_row) + abs(col - other_col) == 1 for other_row, other_col in cells) for row, col in cells):
            return f"cage {index} is not connected"
        if solution is not None and sum(solution[row][col] for row, col in cells) != cage["sum"]:
            return f"cage {index} sum does not match the solution"
    if len(covered) != size * size:
        return "cages do not cover the whole board"
    return None


def validate_solution(solution, givens=None, box_rows=3, box_cols=3, variant=None, cages=None):
    board = solution if isinstance(solution, Board) else Board.from_grids(solution, box_rows=box_rows, box_cols=box_cols)
    result = board.validate(require_complete=True, variant=variant, cages=cages)
    if result.is_invalid or result.is_incomplete:
        return result
    if givens is not None:
        given_board = givens if isinstance(givens, Board) else Board.from_grids(givens, box_rows=box_rows, box_cols=box_cols)
        result = validate_givens_preserved(given_board, board)
        if result.is_invalid:
            return result
    return result


def validate_givens_preserved(givens, solved):
    if not isinstance(givens, Board) or not isinstance(solved, Board):
        return ValidationResult(ValidationStatus.INVALID, ("givens and solved board must be Board objects",))
    errors = []
    for row in range(givens.size):
        for col in range(givens.size):
            if givens.sources[row][col] == CellSource.GIVEN and givens.values[row][col] != solved.values[row][col]:
                errors.append(f"given at ({row + 1},{col + 1}) changed from {givens.values[row][col]} to {solved.values[row][col]}")
    return ValidationResult(ValidationStatus.INVALID if errors else ValidationStatus.VALID, tuple(errors))
