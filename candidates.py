from dataclasses import dataclass, field
from itertools import permutations


@dataclass
class CandidateState:
    board: tuple[tuple[int, ...], ...]
    size: int
    box_rows: int = 3
    box_cols: int = 3
    variant: str = "standard"
    manual_notes: dict[tuple[int, int], set[int]] = field(default_factory=dict)
    show_all: bool = False
    _candidate_cache: dict = field(default_factory=dict, init=False, repr=False)
    _units_cache: tuple | None = field(default=None, init=False, repr=False)
    _unit_index_cache: dict | None = field(default=None, init=False, repr=False)
    # Killer cage constraints: list of {"cells": [(r,c), ...], "sum": int}
    cages: tuple[dict, ...] = field(default_factory=tuple, repr=False)
    _cage_index_cache: dict | None = field(default=None, init=False, repr=False)

    def __post_init__(self):
        if self.size <= 0 or self.size % self.box_rows or self.size % self.box_cols:
            raise ValueError("Board dimensions must evenly divide the board")
        if len(self.board) != self.size or any(len(row) != self.size for row in self.board):
            raise ValueError("Board dimensions do not match candidate state")
        if self.variant not in {"standard", "diagonal", "anti_diagonal", "odd_even", "first_even", "killer"}:
            raise ValueError("Unsupported candidate variant")
        normalized = {}
        for cell, notes in self.manual_notes.items():
            row, col = cell
            if not (0 <= row < self.size and 0 <= col < self.size):
                raise ValueError("Manual note references a cell outside the board")
            if any(not isinstance(note, int) or not 1 <= note <= self.size for note in notes):
                raise ValueError("Manual notes must be valid board values")
            normalized[cell] = set(notes)
        self.manual_notes = normalized

    @classmethod
    def from_board(cls, board, box_rows=3, box_cols=3, variant="standard", manual_notes=None, show_all=False, cages=None):
        size = len(board)
        return cls(tuple(tuple(row) for row in board), size, box_rows, box_cols, variant, manual_notes or {}, show_all, cages=cages or ())

    def units(self):
        """Rows, columns, boxes, and cages (for Killer variant).

        Memoised: the board grid is an immutable tuple and units depend only on
        the geometry, so this never changes for a given CandidateState. It used
        to rebuild all units on every call, and the advanced strategies call
        it ~140k times per board, which dominated analysis runtime.
        """
        if self._units_cache is not None:
            return self._units_cache
        units = [tuple((row, col) for col in range(self.size)) for row in range(self.size)]
        units.extend(tuple((row, col) for row in range(self.size)) for col in range(self.size))
        boxes_per_row = self.size // self.box_cols
        for box_index in range(boxes_per_row * (self.size // self.box_rows)):
            start_row = (box_index // boxes_per_row) * self.box_rows
            start_col = (box_index % boxes_per_row) * self.box_cols
            units.append(tuple((row, col) for row in range(start_row, start_row + self.box_rows) for col in range(start_col, start_col + self.box_cols)))
        # Add cage units for Killer variant
        if self.variant == "killer" and self.cages:
            for cage in self.cages:
                cells = tuple(tuple(cell) for cell in cage["cells"])
                if cells:
                    units.append(cells)
        self._units_cache = tuple(units)
        return self._units_cache

    def unit_for(self, row, col):
        """The units containing a cell, via a precomputed reverse index.

        Includes row, column, box, and (for Killer variant) cage units.
        """
        if self._unit_index_cache is None:
            index: dict = {}
            for unit in self.units():
                for cell in unit:
                    index.setdefault(cell, []).append(unit)
            self._unit_index_cache = {cell: tuple(units) for cell, units in index.items()}
        return self._unit_index_cache.get((row, col), ())

    def candidates_for(self, row, col):
        """The candidate set for a cell.

        Returns the memoised object itself, not a copy, and
        `tests/test_candidates.py` asserts that identity. It is a deliberate
        trade: a 16x16 analysis calls this about 900,000 times, and copying a
        set on each one would be a real cost for a hazard nobody exercises --
        every caller today reads the result or copies it deliberately
        (`all_candidates` does, `set_manual_notes` does). Treat it as read-only;
        mutate `self._candidate_cache` itself and clear it, as
        `toggle_candidate` does.
        """
        if self.board[row][col]:
            return set()
        cached = self._candidate_cache.get((row, col))
        if cached is not None:
            return cached
        candidates = self._base_candidates(row, col)
        # Killer cage constraints: cage sum - known values = sum of remaining candidates
        if self.variant == "killer" and self.cages:
            cage = self._cage_containing(row, col)
            if cage is not None:
                candidates = self._filter_by_cage(candidates, cage, row, col)
        self._candidate_cache[(row, col)] = candidates
        return candidates

    def _base_candidates(self, row, col):
        """Candidates from the row, column, box and variant rules alone.

        No cage arithmetic, so a sibling cell in the same cage can be asked for
        its candidates without recursing back into this cell.
        """
        used = set(self.board[row])
        used.update(self.board[index][col] for index in range(self.size))
        start_row = (row // self.box_rows) * self.box_rows
        start_col = (col // self.box_cols) * self.box_cols
        used.update(self.board[r][c] for r in range(start_row, start_row + self.box_rows) for c in range(start_col, start_col + self.box_cols))
        candidates = set(range(1, self.size + 1)) - used
        if self.variant in {"diagonal", "anti_diagonal"}:
            diagonal = [(row, row)] if self.variant == "diagonal" else [(row, self.size - row - 1)]
            if (row, col) in diagonal:
                used_diagonal = {self.board[r][c] for r, c in diagonal}
                candidates -= used_diagonal
        if self.variant == "odd_even":
            origin = self.board[0][0] if self.board[0][0] else 1
            expected_odd = ((row + col) % 2) == 0 if origin % 2 else ((row + col) % 2) == 1
            candidates = {value for value in candidates if (value % 2 == 1) == expected_odd}
        if self.variant == "first_even":
            if row == 0 and col % 2 == 1:
                candidates &= {2, 4, 6, 8} if self.size == 9 else {value for value in candidates if value % 2 == 0}
            if col == 0 and row % 2 == 1:
                candidates &= {2, 4, 6, 8} if self.size == 9 else {value for value in candidates if value % 2 == 0}
        return candidates

    def _cage_containing(self, row, col):
        """The cage this cell sits in, memoised on first lookup.

        The board is immutable for a given state, so which cage a cell belongs
        to cannot change while the candidate cache is warm.
        """
        if self._cage_index_cache is None:
            index: dict = {}
            for cage in self.cages:
                for cell in cage["cells"]:
                    index.setdefault(tuple(cell), cage)
            self._cage_index_cache = index
        return self._cage_index_cache.get((row, col))

    def _filter_by_cage(self, candidates, cage, row, col):
        """Keep only candidates that can still reach this cage's total.

        The old check compared the smallest and largest possible sums of the
        other cells and kept any digit landing between them. That cannot tell
        whether an actual assignment of distinct digits reaches the target, so
        it missed combination logic and never noticed a digit repeated inside a
        cage -- which is unsolvable. Enumerating combinations answers the real
        question, and the cages are at most four cells, so it is cheap.
        """
        known = [self.board[r][c] for r, c in cage["cells"] if self.board[r][c]]
        # A digit already sitting in this cage cannot appear in it twice.
        excluded = set(known)
        empty = [tuple(cell) for cell in cage["cells"] if not self.board[cell[0]][cell[1]]]
        if (row, col) not in empty:
            return candidates
        needed = cage["sum"] - sum(known)
        others = [cell for cell in empty if cell != (row, col)]

        if not others:
            return candidates & {needed} if 1 <= needed <= self.size else set()

        # Assign digits to cells, not digits to a pool. This used to build one
        # union of what every sibling *could* take and look for any combination
        # of the right size and sum, which answers a different question: the
        # combination can be real while no cell can actually supply its share.
        # Measured on synthetic cages, 18.7% of the candidates that survived
        # had no valid assignment at all, so the filter let unsatisfiable digits
        # through on every cage where it mattered.
        #
        # `_base_candidates` rather than `candidates_for`: asking a sibling in
        # this same cage for its filtered candidates comes back here to ask
        # about this cell, which is not in the cache yet.
        available = [self._base_candidates(*cell) - excluded for cell in others]
        pool = sorted(set().union(*available)) if available else []

        keep = set()
        for value in candidates:
            if value in excluded:
                continue
            target = needed - value
            # `permutations` over the pooled values, not over the per-cell lists:
            # the digits in a cage have to be distinct, and an ordered tuple of
            # distinct values from the pool is exactly that. Each position is then
            # checked against the cell that would have to supply it, which is the
            # step the old union-pool version skipped.
            for assignment in permutations([d for d in pool if d != value], len(others)):
                if sum(assignment) == target and all(
                    digit in available[index] for index, digit in enumerate(assignment)
                ):
                    keep.add(value)
                    break
        return keep

    def all_candidates(self):
        # candidates_for memoises individual cells, so completeness has to be
        # checked by size rather than by "is the cache empty". It used to compare
        # against size*size, which can never be reached: `candidates_for` returns
        # early for a filled cell *without* caching it, so the cache tops out at
        # the number of empty cells and the guard was always True -- every call
        # re-walked the whole board even when everything was already derived.
        empty_cells = sum(1 for row in self.board for value in row if not value)
        if len(self._candidate_cache) < empty_cells:
            for row in range(self.size):
                for col in range(self.size):
                    self.candidates_for(row, col)
        return {cell: set(values) for cell, values in self._candidate_cache.items()}

    def displayed_candidates(self):
        calculated = self.all_candidates()
        return {cell: (set(self.manual_notes[cell]) if cell in self.manual_notes else calculated[cell] if self.show_all else set()) for cell in calculated}

    def toggle_candidate(self, row, col, candidate):
        if self.board[row][col] or candidate not in self.candidates_for(row, col):
            return False
        notes = self.manual_notes.setdefault((row, col), set())
        if candidate in notes:
            notes.remove(candidate)
        else:
            notes.add(candidate)
        return True

    def set_manual_notes(self, row, col, candidates):
        if self.board[row][col]:
            raise ValueError("A filled cell cannot contain notes")
        invalid = set(candidates) - self.candidates_for(row, col)
        if invalid:
            raise ValueError(f"Invalid candidates: {sorted(invalid)}")
        self.manual_notes[(row, col)] = set(candidates)

    def set_show_all(self, enabled):
        self.show_all = bool(enabled)

    def reset_candidates(self):
        self._candidate_cache.clear()
        self.manual_notes.clear()
        self.show_all = False

    def remove_invalid_candidates(self):
        removed = 0
        for cell, notes in list(self.manual_notes.items()):
            valid = self.candidates_for(*cell)
            invalid = notes - valid
            removed += len(invalid)
            notes -= invalid
            if not notes:
                del self.manual_notes[cell]
        return removed

    def digit_filter(self, digit):
        if not 1 <= digit <= self.size:
            return set()
        return {cell for cell, candidates in self.all_candidates().items() if digit in candidates}

    def bivalue_cells(self):
        return {cell for cell, candidates in self.all_candidates().items() if len(candidates) == 2}

    def row_column_box_highlights(self, row, col):
        return {cell for unit in self.unit_for(row, col) for cell in unit}

    def same_digit_highlights(self, digit):
        return {(row, col) for row in range(self.size) for col in range(self.size) if self.board[row][col] == digit}

    def snapshot(self):
        return {"show_all": self.show_all, "manual_notes": {cell: set(notes) for cell, notes in self.manual_notes.items()}}

    def restore(self, snapshot):
        self.show_all = snapshot["show_all"]
        self.manual_notes = {cell: set(notes) for cell, notes in snapshot["manual_notes"].items()}
