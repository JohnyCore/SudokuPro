"""On-board technique overlays: shaded units, ringed cells, and arrow paths.

The deduction and explanation objects produced by the strategy engines already
carry everything needed to draw a teaching diagram -- which cells matter,
which units are involved, and the ordered `chain` of cells a fish or forcing
chain follows. None of it was ever rendered.

This module turns those plain data structures into drawable geometry. Keeping
it separate from `BoardWidget.paintEvent` means the overlay can be unit tested
without a Qt widget, and the same geometry can be reused for export and for
the tutorial example boards.

Overlays are drawn as translucent washes *over* the existing cell contents
rather than as replacements, so a player's own pencil marks, colours, and
mistake highlighting stay visible underneath a technique diagram.
"""

from dataclasses import dataclass, field

#: Visual roles an overlay cell can play.
ROLE_TARGET = "target"
ROLE_SUPPORT = "support"
ROLE_ELIMINATION = "elimination"
ROLE_ARROW = "arrow"


@dataclass(frozen=True)
class Overlay:
    """A drawable technique diagram.

    `cells` are the cells the technique reasons about, `units` are the
    row/column/box groups to wash, and `chain` is an ordered path drawn with
    arrows. `labels` maps a cell to a short string drawn in its corner, which
    is how elimination steps get numbered.
    """

    technique: str = ""
    title: str = ""
    detail: str = ""
    formal: str = ""
    cells: tuple = ()
    targets: tuple = ()
    units: tuple = ()
    chain: tuple = ()
    labels: dict = field(default_factory=dict)
    roles: dict[tuple[int, int], str] = field(default_factory=dict)

    @property
    def is_empty(self):
        return not (self.cells or self.units or self.chain)


def _unit_key(unit):
    """Canonical, order-insensitive identity for a unit so dedup works."""
    return tuple(sorted(unit))


def _dedupe_groups(groups):
    seen = set()
    result = []
    for group in groups:
        if not group:
            continue
        key = _unit_key(group)
        if key in seen:
            continue
        seen.add(key)
        result.append(tuple(group))
    return tuple(result)


def unit_index(kind, size, box_rows, box_cols, value):
    """Return the cells of a row, column, box, or diagonal unit."""
    if kind == "row" and 0 <= value < size:
        return tuple((value, col) for col in range(size))
    if kind == "col" and 0 <= value < size:
        return tuple((row, value) for row in range(size))
    if kind == "box":
        boxes_per_row = size // box_cols if box_cols else 0
        if boxes_per_row and 0 <= value < boxes_per_row * (size // box_rows if box_rows else 0):
            start_row = (value // boxes_per_row) * box_rows
            start_col = (value % boxes_per_row) * box_cols
            return tuple(
                (row, col)
                for row in range(start_row, start_row + box_rows)
                for col in range(start_col, start_col + box_cols)
            )
        return ()
    if kind == "main_diagonal":
        return tuple((index, index) for index in range(size))
    if kind == "anti_diagonal":
        return tuple((index, size - index - 1) for index in range(size))
    return ()


def _rows_cols_boxes(cells, size, box_rows, box_cols):
    """Derive the row, column, and box units a set of cells touches."""
    groups = []
    rows = sorted({row for row, _ in cells})
    cols = sorted({col for _, col in cells})
    boxes = set()
    boxes_per_row = size // box_cols if box_cols else 0
    if boxes_per_row and box_rows and box_cols:
        for row, col in cells:
            boxes.add((row // box_rows) * boxes_per_row + (col // box_cols))
    for row in rows:
        groups.append(unit_index("row", size, box_rows, box_cols, row))
    for col in cols:
        groups.append(unit_index("col", size, box_rows, box_cols, col))
    for box in sorted(boxes):
        groups.append(unit_index("box", size, box_rows, box_cols, box))
    return groups


def _order_chain(chain, size):
    """Normalise a chain into a simple ordered path of in-bounds cells."""
    ordered: list = []
    for item in chain or ():
        if isinstance(item, (tuple, list)) and len(item) >= 2:
            row, col = int(item[0]), int(item[1])
        else:
            continue
        if not (0 <= row < size and 0 <= col < size):
            continue
        if not ordered or ordered[-1] != (row, col):
            ordered.append((row, col))
    return tuple(ordered)


def from_deduction(deduction, size, box_rows, box_cols, chain=(), formal=""):
    """Build an Overlay from a `strategies.Deduction`.

    Falls back gracefully when the deduction carries nothing drawable so the
    caller never has to special-case a technique it does not know.
    """
    if deduction is None:
        return Overlay()
    cells = tuple(getattr(deduction, "cells", ()) or ())
    placements = tuple(getattr(deduction, "placements", ()) or ())
    eliminations = tuple(getattr(deduction, "eliminations", ()) or ())

    targets = tuple((row, col) for row, col, _ in placements)
    elimination_cells = tuple(dict.fromkeys((row, col) for row, col, _ in eliminations))

    if not cells:
        seen = []
        for group in (targets, elimination_cells):
            for cell in group:
                if cell not in seen:
                    seen.append(cell)
        cells = tuple(seen)

    labels = {}
    for _order, (row, col, value) in enumerate(eliminations, start=1):
        labels[(row, col)] = f"x{value}"

    roles = {}
    for cell in targets:
        roles[cell] = ROLE_TARGET
    for cell in elimination_cells:
        roles.setdefault(cell, ROLE_ELIMINATION)
    for cell in cells:
        roles.setdefault(cell, ROLE_SUPPORT)

    units = _dedupe_groups(_rows_cols_boxes(cells, size, box_rows, box_cols))
    ordered_chain = _order_chain(chain, size)

    return Overlay(
        technique=getattr(deduction, "technique", "") or "",
        title=getattr(deduction, "technique", "") or "",
        detail=getattr(deduction, "message", "") or "",
        formal=formal or "",
        cells=tuple(dict.fromkeys(cells)),
        targets=targets,
        units=units,
        chain=ordered_chain,
        labels=labels,
        roles=roles,
    )


def from_mistake(moves, note="", limit=6):
    """Highlight the cells where the player most recently went wrong."""
    recent = [move for move in moves if not move.correct][-limit:]
    cells = tuple(dict.fromkeys((move.row, move.col) for move in recent))
    return Overlay(
        technique="Mistake review",
        title="Mistake review",
        detail=note or "Cells where your last entries did not match the solution.",
        cells=cells,
        targets=cells,
        roles={cell: ROLE_ELIMINATION for cell in cells},
    )


def from_history_entry(move, size, box_rows, box_cols):
    """Highlight the peers of the cell a move was played in."""
    if move is None:
        return Overlay()
    cell = (move.row, move.col)
    units = _dedupe_groups(_rows_cols_boxes([cell], size, box_rows, box_cols))
    return Overlay(
        technique=move.describe(size),
        title=move.describe(size),
        detail=f"{move.cell(size)} was set to {move.value}." if move.value else f"{move.cell(size)} was cleared.",
        cells=(cell,),
        targets=(cell,),
        units=units,
        roles={cell: ROLE_TARGET},
    )


# --------------------------------------------------------------------------
# Geometry
# --------------------------------------------------------------------------

def cell_rect(row, col, origin_x, origin_y, cell_size, grid_width=1):
    """Return the (x, y, w, h) rectangle for a cell."""
    width = max(1, int(cell_size - grid_width))
    return (
        origin_x + col * cell_size,
        origin_y + row * cell_size,
        width,
        max(1, int(cell_size - grid_width)),
    )


def arrow_segments(chain, origin_x, origin_y, cell_size, grid_width=1, inset_ratio=0.5):
    """Yield (start, end) centre points for each arrow in a chain.

    The chain is stored in deduction order, but a chain is usually a closed
    cycle. Rather than draw a final arrow from the last cell back to the
    first, the last cell is linked back to the origin so the diagram reads as
    a loop.
    """
    points = []
    for row, col in chain:
        x, y, w, h = cell_rect(row, col, origin_x, origin_y, cell_size, grid_width)
        points.append((x + w / 2.0, y + h / 2.0))
    if len(points) < 2:
        return ()
    segments = [(points[index], points[index + 1]) for index in range(len(points) - 1)]
    if points[-1] != points[0]:
        segments.append((points[-1], points[0]))
    return tuple(segments)


def shorten(start, end, padding):
    """Trim an arrow so its head does not overlap the cell contents."""
    dx = end[0] - start[0]
    dy = end[1] - start[1]
    length = (dx * dx + dy * dy) ** 0.5
    if length <= padding * 2 or length == 0:
        return start, end
    ux, uy = dx / length, dy / length
    return (
        (start[0] + ux * padding, start[1] + uy * padding),
        (end[0] - ux * padding, end[1] - uy * padding),
    )


def arrow_head(tip, start, half_width=5.0, length=9.0):
    """Return the two wing points for an arrow head at `tip`."""
    dx = start[0] - tip[0]
    dy = start[1] - tip[1]
    magnitude = (dx * dx + dy * dy) ** 0.5
    if magnitude == 0:
        return (tip, tip)
    ux, uy = dx / magnitude, dy / magnitude
    base_x = tip[0] + ux * length
    base_y = tip[1] + uy * length
    px, py = -uy, ux
    return (
        (base_x + px * half_width, base_y + py * half_width),
        (base_x - px * half_width, base_y - py * half_width),
    )
