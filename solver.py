from dataclasses import dataclass
from time import perf_counter


@dataclass(frozen=True)
class SolveResult:
    solved: bool
    board: tuple[tuple[int, ...], ...] | None
    cancelled: bool = False
    nodes: int = 0
    elapsed_seconds: float = 0.0
    progress: float = 0.0


@dataclass(frozen=True)
class CountResult:
    count: int
    cancelled: bool = False
    nodes: int = 0
    elapsed_seconds: float = 0.0
    progress: float = 0.0


class SudokuSolver:
    def __init__(self, board, box_rows=3, box_cols=3, should_cancel=None, progress=None, progress_interval=1000):
        self.initial_board = self._copy_board(board)
        self.size = len(board)
        self.box_rows = box_rows
        self.box_cols = box_cols
        self.should_cancel = should_cancel
        self.progress = progress
        self.progress_interval = max(1, progress_interval)
        self._validate_dimensions()
        # Built once. `_validate_initial_board` used to call `_build_units()`
        # itself and throw the result away, so every construction did the work
        # twice -- and `_remove_clues` constructs one solver per clue attempt.
        self._units = self._build_units()
        self._validate_initial_board()
        self._cells = tuple((row, col) for row in range(self.size) for col in range(self.size))

    def _copy_board(self, board):
        return tuple(tuple(int(value) for value in row) for row in board)

    def _validate_dimensions(self):
        if self.size <= 0 or self.size % self.box_rows or self.size % self.box_cols:
            raise ValueError("Board dimensions must evenly divide the board")
        if any(len(row) != self.size for row in self.initial_board):
            raise ValueError("Board rows must have matching dimensions")
        if any(not isinstance(value, int) or not 0 <= value <= self.size for row in self.initial_board for value in row):
            raise ValueError("Board values are outside the board range")

    def _validate_initial_board(self):
        for unit in self._units:
            values = [self.initial_board[row][col] for row, col in unit if self.initial_board[row][col]]
            if len(values) != len(set(values)):
                raise ValueError("Initial board contains duplicate values in a unit")

    def _build_units(self):
        units = [tuple((row, col) for col in range(self.size)) for row in range(self.size)]
        units.extend(tuple((row, col) for row in range(self.size)) for col in range(self.size))
        boxes_per_row = self.size // self.box_cols
        for box_index in range(boxes_per_row * (self.size // self.box_rows)):
            start_row = (box_index // boxes_per_row) * self.box_rows
            start_col = (box_index % boxes_per_row) * self.box_cols
            units.append(tuple((row, col) for row in range(start_row, start_row + self.box_rows) for col in range(start_col, start_col + self.box_cols)))
        return tuple(units)

    def _cancelled(self):
        if self.should_cancel is None:
            return False
        if hasattr(self.should_cancel, "is_set"):
            return self.should_cancel.is_set()
        return bool(self.should_cancel())

    def _notify(self, nodes, completed=False):
        if self.progress is None or nodes == 0 and not completed:
            return
        if nodes % self.progress_interval != 0 and not completed:
            return
        total = max(1, self.size * self.size)
        self.progress(min(1.0, nodes / total))

    def _new_state(self):
        size = self.size
        values = [list(row) for row in self.initial_board]
        row_masks = [0] * size
        col_masks = [0] * size
        box_masks = [0] * ((size // self.box_rows) * (size // self.box_cols))
        for row in range(size):
            for col in range(size):
                value = values[row][col]
                if value:
                    mask = 1 << (value - 1)
                    row_masks[row] |= mask
                    col_masks[col] |= mask
                    box_masks[self._box_index(row, col)] |= mask
        full_mask = (1 << size) - 1
        candidates = [[0] * size for _ in range(size)]
        for row in range(size):
            for col in range(size):
                if not values[row][col]:
                    candidates[row][col] = full_mask & ~(row_masks[row] | col_masks[col] | box_masks[self._box_index(row, col)])
        return values, row_masks, col_masks, box_masks, candidates, full_mask

    def _box_index(self, row, col):
        return (row // self.box_rows) * (self.size // self.box_cols) + col // self.box_cols

    def _assign(self, state, row, col, digit):
        values, row_masks, col_masks, box_masks, candidates, full_mask = state
        values[row][col] = digit
        mask = 1 << (digit - 1)
        row_masks[row] |= mask
        col_masks[col] |= mask
        box_masks[self._box_index(row, col)] |= mask
        for other in range(self.size):
            if not values[row][other]:
                candidates[row][other] &= ~mask
            if not values[other][col]:
                candidates[other][col] &= ~mask
        start_row = (row // self.box_rows) * self.box_rows
        start_col = (col // self.box_cols) * self.box_cols
        for other_row in range(start_row, start_row + self.box_rows):
            for other_col in range(start_col, start_col + self.box_cols):
                if not values[other_row][other_col]:
                    candidates[other_row][other_col] &= ~mask
        candidates[row][col] = 0

    def _propagate(self, state):
        values, row_masks, col_masks, box_masks, candidates, full_mask = state
        changed = True
        while changed:
            # Polled here as well as in the search loop. It used to be polled only
            # between branches, so a single propagation on a wide board had to
            # finish before a cancel could land.
            if self._cancelled():
                return False
            changed = False
            for row in range(self.size):
                for col in range(self.size):
                    if not values[row][col] and candidates[row][col] == 0:
                        return False
                    if not values[row][col] and candidates[row][col].bit_count() == 1:
                        digit = candidates[row][col].bit_length()
                        self._assign(state, row, col, digit)
                        changed = True
            for unit in self._units:
                for digit in range(1, self.size + 1):
                    mask = 1 << (digit - 1)
                    places = [(row, col) for row, col in unit if not values[row][col] and candidates[row][col] & mask]
                    if len(places) == 0:
                        continue
                    if len(places) == 1:
                        row, col = places[0]
                        if not values[row][col]:
                            self._assign(state, row, col, digit)
                            changed = True
        return True

    def _mrv_cell(self, state):
        values, row_masks, col_masks, box_masks, candidates, full_mask = state
        best = None
        best_count = self.size + 1
        for row in range(self.size):
            for col in range(self.size):
                if values[row][col]:
                    continue
                count = candidates[row][col].bit_count()
                if count < best_count:
                    best = (row, col)
                    best_count = count
                    if count == 1:
                        return best
        return best

    def _copy_state(self, state):
        values, row_masks, col_masks, box_masks, candidates, full_mask = state
        return [row[:] for row in values], row_masks[:], col_masks[:], box_masks[:], [row[:] for row in candidates], full_mask

    def _search(self, limit=1):
        started = perf_counter()
        nodes = 0
        cancelled = False
        root = self._new_state()
        if not self._propagate(root):
            # A propagate that stops for a cancel returns False for the same
            # reason a contradiction does, so ask which it was. Reporting a
            # cancelled search as `cancelled=False, count=0` makes it look like
            # a board with no solution at all.
            return [], 0, nodes, self._cancelled(), started
        stack: list = [(root, None, None)]
        solutions = []
        while stack:
            if self._cancelled():
                cancelled = True
                break
            state, cell, next_candidates = stack[-1]
            if next_candidates is None:
                cell = self._mrv_cell(state)
                if cell is None:
                    solutions.append(tuple(tuple(row) for row in state[0]))
                    if len(solutions) >= limit:
                        break
                    stack.pop()
                    continue
                stack[-1] = (state, cell, list(self._candidate_digits(state[4][cell[0]][cell[1]])))
                continue
            if not next_candidates:
                stack.pop()
                continue
            digit = next_candidates.pop(0)
            child = self._copy_state(state)
            nodes += 1
            self._assign(child, cell[0], cell[1], digit)
            if self._propagate(child):
                stack.append((child, None, None))
            self._notify(nodes)
        self._notify(nodes, completed=True)
        return solutions, limit if len(solutions) >= limit else len(solutions), nodes, cancelled, started

    def _candidate_digits(self, mask):
        while mask:
            bit = mask & -mask
            yield bit.bit_length()
            mask ^= bit

    def solve(self):
        solutions, count, nodes, cancelled, started = self._search(limit=1)
        elapsed = perf_counter() - started
        board = solutions[0] if solutions else None
        return SolveResult(bool(board), board, cancelled, nodes, elapsed, 1.0 if board else 0.0)

    def count_solutions(self, limit=2):
        solutions, count, nodes, cancelled, started = self._search(limit=max(1, limit))
        return CountResult(count, cancelled, nodes, perf_counter() - started, 1.0 if count >= limit else 0.0)

    def solutions(self, limit=2):
        found, count, nodes, cancelled, started = self._search(limit=max(1, limit))
        return tuple(found)

    def is_unique(self):
        # `cancelled` has to be part of this. `_search` returns the number of
        # solutions it had found when it stopped, so a search cancelled after
        # finding one reports `count == 1` having never looked for a second --
        # and this said True. Confirmed: cancelling after poll 7 of a board that
        # needed real search returned True.
        result = self.count_solutions(limit=2)
        return not result.cancelled and result.count == 1


def benchmark(puzzles, box_rows=3, box_cols=3, should_cancel=None):
    results = []
    for name, puzzle in puzzles:
        solver = SudokuSolver(puzzle, box_rows, box_cols, should_cancel=should_cancel)
        result = solver.solve()
        results.append({"name": name, "solved": result.solved, "nodes": result.nodes, "elapsed_seconds": result.elapsed_seconds})
    return results
