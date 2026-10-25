from dataclasses import dataclass


@dataclass(frozen=True)
class AccessibilitySettings:
    high_contrast: bool = False
    color_blind_palette: bool = False
    reduced_motion: bool = False
    sound_enabled: bool = True
    feedback_delay_ms: int = 150
    simple_mode: bool = False

    def __post_init__(self):
        if not 0 <= self.feedback_delay_ms <= 2000:
            raise ValueError("Feedback delay must be between 0 and 2000 milliseconds")

    def cell_accessibility_label(self, row, col, value=0, solution=None, mistake=False, note_count=0):
        state = "empty" if not value else str(value)
        if mistake:
            state += ", incorrect"
        if note_count:
            state += f", {note_count} notes"
        return f"Row {row + 1}, column {col + 1}, {state}"

    # `focus_visible`, `error_text_enabled`, `focus_style()` and
    # `error_presentation()` used to live here. None of them was ever read:
    # `apply_settings` rebuilds this object without passing either field, and
    # `focus_style` returned CSS ("outline: 3px solid #005fcc") that Qt's
    # stylesheet parser does not consume in that form. A switch that does
    # nothing is worse than no switch -- `test_accessibility_switches.py` exists
    # precisely to catch that class of thing, and these two slipped past it
    # because the guard only checks six other keys.


class TechniqueHelpIndex:
    def __init__(self, entries=None):
        self.entries = tuple(entries or ())

    def add(self, name, description, keywords=()):
        self.entries += ((name, description, tuple(keywords)),)

    def search(self, query):
        query = str(query).strip().lower()
        if not query:
            return self.entries
        return tuple(entry for entry in self.entries if query in entry[0].lower() or query in entry[1].lower() or any(query in keyword.lower() for keyword in entry[2]))


#: Help entries that describe a part of the app rather than a solving
#: technique. They are legitimately in the reference, and no engine will ever
#: produce them, so the check that keeps the reference honest has to know about
#: them.
TECHNIQUE_HELP_TOPICS = frozenset({"Training Mode"})

DEFAULT_HELP = TechniqueHelpIndex((
    (
        "Naked Single",
        "A cell with only one possible number, so it must be that number. "
        "This is the only technique you need for an easy puzzle, and it is worth "
        "learning to spot instantly.",
        ("single", "cell", "basic", "easy", "beginner"),
    ),
    (
        "Hidden Single",
        "A number has only one possible home inside a row, column or box. The cell "
        "may still look empty to you, but the digit has nowhere else to go.",
        ("single", "row", "column", "box", "basic", "pointing"),
    ),
    (
        "Locked Candidates / Pointing",
        "Inside a box, two or three cells hold the same small set of digits and all "
        "of them can see the same cells. Those digits cannot go outside the box. "
        "When the set 'points' at a single row or column, that line cannot use them.",
        ("locked", "candidate", "pointing", "box", "elimination"),
    ),
    (
        "Locked Candidates / Claiming",
        "The mirror image of pointing: a set trapped in a box that can all see the "
        "same cells, so every cell in the line they claim loses those digits.",
        ("locked", "candidate", "claiming", "box", "elimination"),
    ),
    (
        "Naked Pair",
        "Two cells in one unit share an identical pair of candidates. Those two "
        "digits are spoken for, and can be struck from every other cell that can "
        "see them.",
        ("pair", "candidate", "unit", "elimination"),
    ),
    (
        "Naked Triple",
        "The same idea with three cells and three digits.",
        ("triple", "candidate", "unit", "elimination"),
    ),
    (
        "X-Wing",
        "A fish. Two cells in different rows share a pair of candidates, and two "
        "cells in different columns share the same pair. Either way those digits "
        "can only live in those four cells, so every other cell that can see them "
        "loses them.",
        ("fish", "wing", "candidate", "elimination", "x-wing"),
    ),
    (
        "Swordfish",
        "The three-cell version of the same idea: three cells in different rows and "
        "three in different columns share an identical triple of candidates.",
        ("fish", "swordfish", "candidate", "elimination"),
    ),
    (
        "Unique Rectangle",
        "A rectangle of four cells where one pair already holds the same two digits. "
        "It cannot be the two-by-two pattern it looks like, so the other pair is "
        "forced into the remaining two cells -- which is what breaks hard pairs.",
        ("rectangle", "deadly", "pattern", "uniqueness"),
    ),
    (
        "Forcing Chain",
        "When two ways of placing the same digit both start at the same cell, only "
        "one of them can be the truth. Follow the resolving chain and the digits it "
        "passes through are forced; the other branch simply runs out of options.",
        ("chain", "forcing", "bivalue", "hard"),
    ),
    (
        "Training Mode",
        "Walk the next logical step on your own board, with the reasoning shown. It "
        "highlights the real cells in the puzzle you are playing and waits for you "
        "to make the deduction, so the skill transfers.",
        ("practice", "learn", "training", "walkthrough"),
    ),
))
