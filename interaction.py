from dataclasses import dataclass


@dataclass
class InteractionController:
    size: int
    board: list[list[int]]
    selected: list[tuple[int, int]]
    solution: list[list[int]] | None = None
    wrap_navigation: bool = True
    single_click_entry: bool = True
    drag_enabled: bool = True

    def __post_init__(self):
        if self.size <= 0 or len(self.board) != self.size or any(len(row) != self.size for row in self.board):
            raise ValueError("Board dimensions do not match interaction controller")
        self._drag_origin = None

    def set_board(self, board):
        if len(board) != self.size or any(len(row) != self.size for row in board):
            raise ValueError("Board dimensions do not match interaction controller")
        self.board = board

    def active(self):
        return self.selected[-1] if self.selected else None

    def select(self, cell, extend=False, toggle=False):
        cell = self._cell(cell)
        if cell is None:
            return
        if toggle:
            if cell in self.selected:
                self.selected.remove(cell)
            else:
                self.selected.append(cell)
        elif extend and self.selected:
            self.selected.append(cell)
        else:
            self.selected[:] = [cell]

    def select_rectangle(self, first, last, toggle=False):
        first = self._cell(first)
        last = self._cell(last)
        if first is None or last is None:
            return
        cells = [(row, col) for row in range(min(first[0], last[0]), max(first[0], last[0]) + 1) for col in range(min(first[1], last[1]), max(first[1], last[1]) + 1)]
        if toggle:
            for cell in cells:
                self.select(cell, toggle=True)
        else:
            self.selected[:] = cells

    def select_row(self, row, toggle=False):
        self._select_unit([(row, col) for col in range(self.size)], toggle)

    def select_column(self, col, toggle=False):
        self._select_unit([(row, col) for row in range(self.size)], toggle)

    def select_box(self, row, col, box_rows, box_cols, toggle=False):
        start_row = (row // box_rows) * box_rows
        start_col = (col // box_cols) * box_cols
        self._select_unit([(r, c) for r in range(start_row, start_row + box_rows) for c in range(start_col, start_col + box_cols)], toggle)

    def _select_unit(self, cells, toggle):
        if not toggle:
            self.selected[:] = cells
            return
        # Toggling a unit means "also select it": if every cell of the unit is
        # already selected the unit is removed, otherwise it is merged in.
        # A symmetric difference here produced nonsense for row-then-column
        # selection, silently dropping the overlapping cell.
        if all(cell in self.selected for cell in cells):
            for cell in cells:
                if cell in self.selected:
                    self.selected.remove(cell)
            return
        for cell in cells:
            if cell not in self.selected:
                self.selected.append(cell)

    def move(self, row_delta, col_delta, extend=False):
        active = self.active()
        if active is None:
            return
        row, col = active
        if self.wrap_navigation:
            row = (row + row_delta) % self.size
            col = (col + col_delta) % self.size
        else:
            row = min(self.size - 1, max(0, row + row_delta))
            col = min(self.size - 1, max(0, col + col_delta))
        self.select((row, col), extend=extend)

    def jump_next_unsolved(self, current=None, include_wrong=True):
        start = current or self.active() or (0, 0)
        for offset in range(1, self.size * self.size + 1):
            row = (start[0] + (offset - 1) // self.size) % self.size
            col = (start[1] + (offset - 1) % self.size) % self.size
            if include_wrong or self.board[row][col] == 0:
                self.select((row, col))
                return (row, col)
        return None

    def jump_next_error(self, current=None):
        start = current or self.active() or (0, 0)
        for offset in range(1, self.size * self.size + 1):
            row = (start[0] + (offset - 1) // self.size) % self.size
            col = (start[1] + (offset - 1) % self.size) % self.size
            if self.board[row][col] and self.solution is not None and self.board[row][col] != self.solution[row][col]:
                self.select((row, col))
                return (row, col)
        return None

    def begin_drag(self, cell):
        if self.drag_enabled:
            cell = self._cell(cell)
            self._drag_origin = cell
            if cell is not None:
                self.select(cell)

    def update_drag(self, cell, rectangular=False):
        if not self.drag_enabled or self._drag_origin is None:
            return
        cell = self._cell(cell)
        if cell is None:
            return
        if rectangular:
            # A drag rectangle defines the selection; XOR-ing it against the
            # drag origin dropped the anchor cell.
            self.select_rectangle(self._drag_origin, cell)
        else:
            self.select(cell, extend=True)

    def end_drag(self):
        self._drag_origin = None

    def entry_click(self, cell, value, double_click=False):
        if not self.single_click_entry and not double_click:
            return False
        self.select(cell)
        return True

    def context_actions(self):
        return ("select_row", "select_column", "select_box", "clear_selection")

    def _cell(self, cell):
        row, col = cell
        if 0 <= row < self.size and 0 <= col < self.size:
            return (row, col)
        return None
