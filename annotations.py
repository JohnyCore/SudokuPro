from dataclasses import dataclass, field

COLORBLIND_PALETTE = {
    "blue": "#0072B2",
    "orange": "#E69F00",
    "green": "#009E73",
    "yellow": "#F0E442",
    "purple": "#CC79A7",
    "red": "#D55E00",
    "black": "#000000",
    "white": "#FFFFFF",
}

HIGH_CONTRAST_PALETTE = {
    "black": "#000000",
    "white": "#FFFFFF",
    "yellow": "#FFFF00",
    "cyan": "#00FFFF",
    "magenta": "#FF00FF",
    "red": "#FF0000",
    "green": "#00FF00",
    "blue": "#0000FF",
}


@dataclass
class AnnotationState:
    size: int
    cell_colors: dict[tuple[int, int], str] = field(default_factory=dict)
    candidate_colors: dict[tuple[int, int, int], str] = field(default_factory=dict)
    primary_color: str = "#0072B2"
    secondary_color: str = "#E69F00"
    annotations_visible: bool = True
    palette_name: str = "colorblind"

    def __post_init__(self):
        if self.size <= 0:
            raise ValueError("Annotation board size must be positive")
        self._validate_color(self.primary_color)
        self._validate_color(self.secondary_color)
        if self.palette_name not in {"default", "colorblind", "high_contrast"}:
            raise ValueError("Unknown annotation palette")

    def _validate_color(self, color):
        if not isinstance(color, str) or not color.startswith("#") or len(color) not in {4, 7}:
            raise ValueError("Colors must use hexadecimal notation")

    def _cell(self, cell):
        row, col = cell
        if not (0 <= row < self.size and 0 <= col < self.size):
            raise ValueError("Annotation cell is outside the board")
        return (row, col)

    def set_cell_color(self, cell, color, secondary=False):
        cell = self._cell(cell)
        self._validate_color(color)
        self.cell_colors[cell] = self.secondary_color if secondary and color == self.primary_color else color

    def set_candidate_color(self, cell, candidate, color):
        row, col = self._cell(cell)
        if not 1 <= candidate <= self.size:
            raise ValueError("Candidate is outside the board range")
        self._validate_color(color)
        self.candidate_colors[(row, col, candidate)] = color

    def swap_colors(self):
        self.primary_color, self.secondary_color = self.secondary_color, self.primary_color

    def clear_cell_color(self, cell):
        self.cell_colors.pop(self._cell(cell), None)

    def clear_candidate_color(self, cell, candidate):
        self.candidate_colors.pop((*self._cell(cell), candidate), None)

    def clear_color(self, color):
        self.cell_colors = {cell: value for cell, value in self.cell_colors.items() if value != color}
        self.candidate_colors = {cell: value for cell, value in self.candidate_colors.items() if value != color}

    def clear_all(self):
        self.cell_colors.clear()
        self.candidate_colors.clear()

    def set_visibility(self, visible):
        self.annotations_visible = bool(visible)

    def visible_cell_colors(self):
        return dict(self.cell_colors) if self.annotations_visible else {}

    def visible_candidate_colors(self):
        return dict(self.candidate_colors) if self.annotations_visible else {}

    def digit_filter_colors(self, digit, color):
        self._validate_color(color)
        return {(row, col): color for (row, col, candidate) in self.candidate_colors if candidate == digit}

    def set_palette(self, name):
        if name not in {"default", "colorblind", "high_contrast"}:
            raise ValueError("Unknown annotation palette")
        self.palette_name = name

    def palette_colors(self):
        return {"colorblind": COLORBLIND_PALETTE, "high_contrast": HIGH_CONTRAST_PALETTE}.get(self.palette_name, {"primary": self.primary_color, "secondary": self.secondary_color})

    def snapshot(self):
        """A JSON-safe copy.

        The keys here are tuples -- (row, col) for a cell, (row, col, value) for a
        pencil mark -- and JSON object keys must be strings. So the snapshot went
        into the save payload with tuple keys and `json.dump` raised "keys must be
        str, int, float, bool or None, not tuple". Nothing noticed for as long as
        no UI could set a colour, because the dictionaries were always empty; the
        moment annotations became creatable, colouring a single cell made the game
        unsaveable, and the failure surfaced from closeEvent.

        Keys are flattened to comma-separated strings on the way out and rebuilt
        on the way in.
        """
        return {
            "cell_colors": {
                f"{row},{col}": color for (row, col), color in self.cell_colors.items()
            },
            "candidate_colors": {
                f"{row},{col},{value}": color
                for (row, col, value), color in self.candidate_colors.items()
            },
            "primary_color": self.primary_color,
            "secondary_color": self.secondary_color,
            "annotations_visible": self.annotations_visible,
            "palette_name": self.palette_name,
        }

    @staticmethod
    def _decode_keys(mapping, width, what):
        """Turn "row,col,value" back into a tuple, skipping anything malformed.

        A corrupt key is dropped rather than raising: one bad annotation should
        not cost the player the rest of the save.
        """
        decoded = {}
        for key, color in (mapping or {}).items():
            if isinstance(key, (tuple, list)):
                decoded[tuple(key)] = color
                continue
            parts = [piece.strip() for piece in str(key).split(",")]
            if len(parts) != width:
                continue
            try:
                numbers = tuple(int(piece) for piece in parts)
            except ValueError:
                continue
            decoded[numbers] = color
        del what
        return decoded

    def restore(self, snapshot):
        self.cell_colors = self._decode_keys(snapshot["cell_colors"], 2, "cell_colors")
        self.candidate_colors = self._decode_keys(snapshot["candidate_colors"], 3, "candidate_colors")
        self.primary_color = snapshot["primary_color"]
        self.secondary_color = snapshot["secondary_color"]
        self.annotations_visible = snapshot["annotations_visible"]
        self.palette_name = snapshot["palette_name"]
        self.__post_init__()
