"""Choosing a new puzzle: four questions, asked in a dialog.

This started as a panel in the left sidebar. It looked right there and read well,
but the sidebar simply has no room for it: the keypad, three action buttons and
this panel together need about 886 pixels, and the pane gets roughly 780 in an
ordinary window. So the sidebar grew a scrollbar, which is the opposite of the
point -- a control you have to scroll to find is less reachable than the nested
menu it replaced.

In a dialog it costs the sidebar nothing, and it gets to lay out properly: five
segments to a row instead of three, so every option is on one line with room to
be read, which is what the design this was copied from does.

The New Game menu still exists and still offers the same thirty-six boards, for
anyone who wants the keyboard-driven route. It is no longer the primary way in.
"""

import random

from PyQt5.QtCore import Qt, pyqtSignal
from PyQt5.QtWidgets import (
    QButtonGroup,
    QDialog,
    QHBoxLayout,
    QLabel,
    QPushButton,
    QSizePolicy,
    QVBoxLayout,
    QWidget,
)

import main
from game_modes import NO_HINTS, NO_MISTAKES, SPRINT, TIMED

#: Height of a segment, and the fixed width of the caption column beside it.
#: Chosen so eight sizes fit on one line without the labels becoming hard to
#: read: the dialog is compact, not squeezed.
SEGMENT_HEIGHT = 28
CAPTION_WIDTH = 66

#: Board sizes offered, smallest first. Every size the generator can deal.
PANEL_SIZES = (4, 6, 8, 9, 10, 12, 15, 16)

#: Variants offered. Only variants the generator can actually produce: see the
#: note on X-Sudoku in the roadmap. A button here that dealt an ordinary Sudoku
#: would be worse than no button.
PANEL_VARIANTS = (
    ("Classic", None),
    ("Killer", "killer"),
)

#: Challenges, with the mode behind each label. `None` means no limits.
#:
#: Accuracy used to be here as well, and it was the same rule twice: it sets
#: `no_mistakes`, exactly as No Mistakes does, so both ended the game on the
#: first mistake. One of them had to go, and No Mistakes says what it does.
#:
#: "1 Hint" went the same way, for a different reason. Allowing one hint is a
#: question about whether you would spend it, not a constraint you solve around
#: -- and it made the row longer for the least interesting option on it. No Hints
#: is the same idea taken seriously: the button stops existing. Sprint joins it
#: because Timed's fifteen minutes is long enough on a 9x9 that the clock is
#: scenery; five minutes makes speed the puzzle.
PANEL_CHALLENGES = (
    ("None", None),
    ("Timed", TIMED),
    ("Sprint", SPRINT),
    ("No Hints", NO_HINTS),
    ("No Mistakes", NO_MISTAKES),
)


def size_tooltips():
    """One per board size, so "12x12" can say which puzzle it means."""
    tooltips = {}
    for size in PANEL_SIZES:
        label = next(
            (
                name
                for name, spec in main.CUSTOM_BOARD_SIZES.items()
                if spec["size"] == size
            ),
            "9x9 Sudoku",
        )
        tooltips[f"{size}x{size}"] = label
    return tooltips


def game_label(size, variant, difficulty):
    """The label the rest of the app already understands.

    A bare 9x9 difficulty is its own label, which is how the seed checksum, the
    statistics and the win screen have always identified one; everything else is
    `custom_label(size_label, difficulty)`. Going through the existing labels
    rather than passing four separate arguments keeps a puzzle dealt from here
    indistinguishable from one dealt from the menu.
    """
    if difficulty == "Any":
        difficulty = random.choice(main.DIFFICULTY_LEVELS)
    if variant == "killer":
        return main.custom_label(main.KILLER_SUDOKU_LABEL, difficulty)
    if size == 9:
        return difficulty
    size_label = next(
        (
            name
            for name, spec in main.CUSTOM_BOARD_SIZES.items()
            if spec["size"] == size
        ),
        None,
    )
    if size_label is None:
        return difficulty
    return main.custom_label(size_label, difficulty)


def describe(size, variant, difficulty, challenge):
    """One line saying what the button is about to do.

    "Any" has already become a real difficulty by this point, so the line names a
    real difficulty rather than the word Any.
    """
    label = game_label(size, variant, difficulty)
    _base, parsed = main.difficulty_parts(label)
    shown = parsed or difficulty
    parts = [label if shown == difficulty else f"{label} ({shown})"]
    if challenge is not None:
        parts.append(challenge.name)
    return "  \u00b7  ".join(parts)


class SegmentedRow(QWidget):
    """One row of mutually exclusive choices, on a single line.

    A `QButtonGroup` of checkable buttons sitting inside one rounded track, so
    it reads as one control with a position rather than a row of separate
    buttons. The caption sits beside the track rather than above it, which saves
    a line per row -- four of them here.

    Every option is on one line even where there are eight of them. Two rows of
    four looked like two controls with a gap, and read as an accident.
    """

    #: Emitted with the new label whenever the selection changes.
    changed = pyqtSignal(str)

    def __init__(self, caption, options, parent=None, columns=None, tooltips=None):
        super().__init__(parent)
        self.caption = caption
        self.options = list(options)
        self._buttons = {}
        self._per_row = max(1, columns or len(self.options) or 1)

        # The row is handed whatever width there is and asks for none of its own.
        self.setSizePolicy(QSizePolicy.Expanding, QSizePolicy.Fixed)
        self.setMinimumWidth(0)

        outer = QHBoxLayout(self)
        outer.setContentsMargins(0, 0, 0, 0)
        outer.setSpacing(8)

        label = QLabel(caption)
        label.setObjectName("panelRowCaption")
        # Fixed width so the four tracks line up into a column, whatever each
        # caption is called.
        label.setFixedWidth(CAPTION_WIDTH)
        # Left, not right. Right-aligned against a fixed column left the captions
        # floating in the middle of the dialog, detached from both the edge and
        # their own controls.
        label.setAlignment(Qt.AlignLeft | Qt.AlignVCenter)
        outer.addWidget(label)

        self.group = QButtonGroup(self)
        self.group.setExclusive(True)

        track = QWidget()
        track.setObjectName("segmentTrack")
        line = QHBoxLayout(track)
        line.setContentsMargins(3, 3, 3, 3)
        line.setSpacing(2)
        for index, option in enumerate(self.options):
            text, value = option if isinstance(option, tuple) else (option, option)
            button = QPushButton(text)
            button.setCheckable(True)
            button.setObjectName("segmentButton")
            button.setCursor(Qt.PointingHandCursor)
            # Expanding with a zero minimum, so the row divides evenly and can
            # still shrink when the pane is narrow -- but the button keeps its
            # size hint.
            #
            # `Ignored` was tried and threw the hints away, which meant the
            # dialog could not measure itself: its sizeHint came out at 268px and
            # every long label was cut off mid-word on a machine with a wider
            # default font.
            button.setSizePolicy(QSizePolicy.Expanding, QSizePolicy.Fixed)
            button.setMinimumWidth(0)
            button.setMinimumHeight(SEGMENT_HEIGHT)
            if tooltips:
                button.setToolTip(tooltips.get(text, ""))
            button.toggled.connect(
                lambda checked, name=text: self._on_toggled(name, checked)
            )
            line.addWidget(button, 1)
            self.group.addButton(button, index)
            self._buttons[text] = button
        outer.addWidget(track, 1)
        self.track = track

        if self._buttons:
            self.select(next(iter(self._buttons)))

    def _on_toggled(self, name, checked):
        button = self._buttons[name]
        # The stylesheet keys off the object name, so the two states need two
        # names rather than a dynamic property the sheet cannot match.
        button.setObjectName("segmentButtonSelected" if checked else "segmentButton")
        # Qt does not restyle a widget when its object name changes: the rule is
        # matched once, when the widget is polished. Without this the checked
        # state was recorded and nothing on screen changed.
        style = button.style()
        style.unpolish(button)
        style.polish(button)
        button.update()
        if checked:
            self.changed.emit(name)

    def select(self, text):
        button = self._buttons.get(text)
        if button is not None:
            button.setChecked(True)
        return button

    def selected(self):
        for name, button in self._buttons.items():
            if button.isChecked():
                return name
        return None

    def value(self):
        """The option's value, not its label."""
        name = self.selected()
        for option in self.options:
            text, value = option if isinstance(option, tuple) else (option, option)
            if text == name:
                return value
        return None

    def select_value(self, value):
        for option in self.options:
            text, option_value = option if isinstance(option, tuple) else (option, option)
            if option_value == value:
                return self.select(text)
        return None

    def width_needed(self):
        """Width this track needs for its labels, from the buttons' own hints."""
        if not self._buttons:
            return 0
        widest = max(button.sizeHint().width() for button in self._buttons.values())
        return widest * len(self._buttons) + 2 * len(self._buttons)


class NewPuzzleDialog(QDialog):
    """Size, variant, difficulty and rules, then one button to deal the board."""

    #: (game label, challenge mode or None), emitted when the player commits.
    requested = pyqtSignal(str, object)

    def __init__(self, window, parent=None):
        super().__init__(parent or window)
        self.window = window
        self.setWindowTitle("New Game")
        self.setModal(True)

        root = QVBoxLayout(self)
        root.setContentsMargins(18, 14, 18, 14)
        root.setSpacing(8)

        header = QVBoxLayout()
        header.setSpacing(1)
        title = QLabel("New Game")
        title.setObjectName("newGameTitle")
        header.addWidget(title)
        subtitle = QLabel("Set up your next Sudoku challenge")
        subtitle.setObjectName("newGameSubtitle")
        header.addWidget(subtitle)
        root.addLayout(header)

        tooltips = size_tooltips()
        tooltips["Any"] = "Let the app pick one at random"
        tooltips.update(
            {
                difficulty: f"{difficulty} -- or let the app choose with Any"
                for difficulty in main.DIFFICULTY_LEVELS
            }
        )

        self.size_row = SegmentedRow(
            "Size",
            [(f"{size}x{size}", size) for size in PANEL_SIZES],
            # All eight on one line. Two rows of four looked like two separate
            # controls with a gap between them, and read as a mistake rather
            # than a choice.
            columns=8,
            tooltips=tooltips,
        )
        self.variant_row = SegmentedRow(
            "Variant",
            list(PANEL_VARIANTS),
            columns=2,
            tooltips={
                "Classic": "Rows, columns and boxes only",
                "Killer": "Cage sums give you extra information to work with",
            },
        )
        self.difficulty_row = SegmentedRow(
            "Difficulty",
            [("Any", "Any")] + [(name, name) for name in main.DIFFICULTY_LEVELS],
            columns=5,
            tooltips=tooltips,
        )
        self.challenge_row = SegmentedRow(
            "Challenge",
            list(PANEL_CHALLENGES),
            columns=5,
            tooltips={
                "None": "Play without limits",
                "Timed": main.challenge_rules(TIMED),
                "Sprint": main.challenge_rules(SPRINT),
                "No Hints": main.challenge_rules(NO_HINTS),
                "No Mistakes": main.challenge_rules(NO_MISTAKES),
            },
        )
        self.rows = (self.size_row, self.variant_row, self.difficulty_row, self.challenge_row)
        for row in self.rows:
            root.addWidget(row)


        # Killer is a 9x9 variant, and always was. Leaving the size on 16x16 while
        # the variant said Killer dealt a 9x9 and left the dialog claiming
        # otherwise, so the rows now correct each other.
        self.variant_row.changed.connect(self._on_variant_changed)
        self.size_row.changed.connect(self._on_size_changed)

        buttons = QHBoxLayout()
        buttons.setSpacing(10)
        buttons.addStretch()
        self.go = QPushButton("New Puzzle")
        self.go.setObjectName("newPuzzleGo")
        self.go.setCursor(Qt.PointingHandCursor)
        self.go.setDefault(True)
        self.go.setMinimumHeight(36)
        self.go.setMinimumWidth(150)
        self.go.setToolTip("Deal a puzzle with the settings above")
        self.go.clicked.connect(self.start)
        buttons.addWidget(self.go)
        cancel = QPushButton("Cancel")
        cancel.setObjectName("dialogFooterClose")
        cancel.setMinimumHeight(36)
        cancel.clicked.connect(self.reject)
        buttons.addWidget(cancel)
        root.addLayout(buttons)

        self.sync_from_game()

    def showEvent(self, event):
        """Refuse to open narrower than the labels need.

        The size hints are computed from the font in use, but the app stylesheet
        is only applied once the dialog is in the hierarchy -- so the width
        measured during construction can be short by however much the stylesheet
        changes the font. On a machine with a wider default face that clipped
        "Medium" to "Medi" and "No Mistakes" to "list".

        Measuring again here, with the real font, is the difference between a
        dialog that fits and one that truncates its own options.
        """
        super().showEvent(event)
        self._fit_width()

    def _fit_width(self):
        """Widen to whatever the labels need.

        Raising the minimum alone was not enough: the dialog had already been
        laid out by then, and on a narrow screen the tracks ran off the right
        edge. It resized as well as re-measuring.
        """
        needed = (
            CAPTION_WIDTH
            + 8
            + max(row.width_needed() for row in self.rows)
            + 2 * self.layout().contentsMargins().left()
        )
        if needed > self.minimumWidth():
            self.setMinimumWidth(needed)
        if self.width() < needed:
            self.resize(needed, self.height())

    def resizeEvent(self, event):
        super().resizeEvent(event)
        self._fit_width()

    # ---- consistency -----------------------------------------------------

    def _on_variant_changed(self, name):
        if name == "Killer" and self.size_row.selected() != "9x9":
            self.size_row.select("9x9")

    def _on_size_changed(self, name):
        if name != "9x9" and self.variant_row.selected() == "Killer":
            self.variant_row.select("Classic")

    # ---- choices ---------------------------------------------------------

    def sync_from_game(self):
        """Open on the board actually in play, so nothing is a surprise."""
        state = getattr(self.window, "state", None)
        if state is None:
            return
        size = getattr(state, "board_size", 9)
        self.size_row.select(f"{size}x{size}")
        self.variant_row.select("Killer" if getattr(state, "killer", False) else "Classic")

        current = getattr(state, "current_difficulty", "Medium")
        # A bare 9x9 difficulty is its own label, and `difficulty_parts` only
        # splits the composite ones -- so a board dealt as plain "Expert" came
        # back as (None, None).
        if current in main.DIFFICULTY_LEVELS:
            difficulty = current
        else:
            _base, difficulty = main.difficulty_parts(current)
        self.difficulty_row.select(
            difficulty if difficulty in main.DIFFICULTY_LEVELS else "Medium"
        )

        session = getattr(self.window, "challenge_session", None)
        self.challenge_row.select_value(session.mode if session and not session.finished else None)

    def choices(self):
        return (
            self.size_row.value() or 9,
            self.variant_row.value(),
            self.difficulty_row.value() or "Medium",
            self.challenge_row.value(),
        )

    # ---- dealing ---------------------------------------------------------

    def start(self):
        size, variant, difficulty, challenge = self.choices()
        self.requested.emit(game_label(size, variant, difficulty), challenge)
        self.accept()

    def buttons(self):
        """Every segment button.

        `_build_ui` gives each button in the left pane a 112px width floor so the
        stacked action buttons stay legible. Three of these across a narrow pane
        would then ask for more width than there is, so if this ever goes back in
        the sidebar it has to be exempt the way the keypad and footer are.
        """
        return [button for row in self.rows for button in row._buttons.values()]
