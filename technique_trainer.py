"""Find a board that needs a named technique, to practise on.

Training mode walks the player through the next logical step on whatever board
is open. That teaches well and practises badly: on a random board the cheapest
step is almost always a single, so the walkthrough is mostly singles however
many techniques the player is trying to learn.

There are two ways in, and they answer different questions.

`build_scenario` **constructs** a board: it starts from a generated one that uses
the technique and then fills cells back in from the solution for as long as the
technique still fires and the puzzle still has one solution. What survives is a
handful of holes arranged so the named technique is nearly the only thing left to
see -- which is the board a textbook would print for you.

`find_training_board` **searches** for a board: it generates and keeps the
earliest one where the technique turns up, and falls back to the best of those
tried. That board is an ordinary generated puzzle, so the technique is somewhere
in it rather than staged for it.

The scenario is tried first and the search is the fallback, because the search
is what makes every technique reachable: staging is best-effort, and a technique
the minimiser cannot isolate (Swordfish, for one) still has to be practisable.

No Qt and no GUI state here: the search is pure and slow enough that it belongs
on a worker thread, and a pure function is testable without one.
"""
import math
import random
import time

from advanced_search import AdvancedSearch
from advanced_strategies import AdvancedStrategyEngine
from candidates import CandidateState
from solver import SudokuSolver
from strategies import StrategyEngine

#: Techniques a learner can ask for, and that a generated board can actually be
#: found to contain.
#:
#: The second list is the important one. Five techniques here used to be offered
#: and **never** turned up: Hidden Pair, Hidden Triple, Hidden Quad, Remote Pair
#: and Unique Rectangle. Measured over 25 generated boards at each of Medium and
#: Hard, all five appear zero times -- so asking for them spun the search and
#: then told the player nothing was found, every single time. That is not a rare
#: miss, it is a guaranteed one, and offering a technique that cannot be
#: practised is worse than not offering it.
#:
#: Why they cannot be found: a generated board is dug cell by cell against the
#: generator's own rating, and what survives that is not a position where a unit
#: has exactly two cells left for the same two digits. Unique Rectangle is the
#: clearest case -- a uniquely-solvable puzzle cannot contain one at all, which
#: is why `advanced_search` carries it as sound-but-vacuous.
#:
#: Practising those five needs a board *constructed* around the pattern rather
#: than searched for, one recipe per technique. That is real work and it is not
#: here yet; until it is, they are off the menu rather than broken on it.
NEEDS_CONSTRUCTION = (
    "Hidden Pair", "Hidden Triple", "Hidden Quad", "Remote Pair",
    "Unique Rectangle",
)

PRACTICEABLE = tuple(
    name for name in (
        "Naked Pair", "Locked Candidates / Pointing",
        "Locked Candidates / Claiming", "Naked Triple", "Naked Quad",
        "X-Wing", "XY-Wing", "Skyscraper",
        "Swordfish", "XY-Chain", "W-Wing",
        "Sashimi Fish",
    ) if name not in NEEDS_CONSTRUCTION
)


def deductions_for(board, box_rows=3, box_cols=3):
    """Every deduction any engine makes on this board, cheapest first."""
    state = CandidateState.from_board(board, box_rows=box_rows, box_cols=box_cols)
    found = list(StrategyEngine(state).iter_all())
    found += list(AdvancedStrategyEngine(state).iter_all())
    found += list(AdvancedSearch(state).find_all())
    return sorted(
        (d for d in found if d.eliminations or d.placements),
        key=lambda d: (d.difficulty, d.technique),
    )


def board_uses(board, technique, box_rows=3, box_cols=3):
    """How early `technique` shows up, or None if the board never uses it.

    The difficulty is the point: 1 means it is the very first thing a player
    would see on this board, 9 means it is buried behind everything else and the
    board is not much use for practising it.
    """
    for deduction in deductions_for(board, box_rows, box_cols):
        if deduction.technique == technique:
            return deduction.difficulty
    return None


def geometry_of(variant, size):
    """The box shape of a generated board.

    `main.generate_puzzle` hands back a third element that is a dict for an
    ordinary puzzle -- carrying `box_rows`/`box_cols` -- and a plain string for
    a killer variant, which is not something this search can analyse. Reading it
    matters: a 4x4 board analysed as though its boxes were 3x3 gets the wrong
    candidates, the wrong locked-candidate pairs, and so no useful technique is
    ever found on it. `isqrt` is the fallback for a variant that does not say.
    """
    if isinstance(variant, dict) and variant.get("box_rows"):
        return int(variant["box_rows"]), int(variant["box_cols"])
    side = math.isqrt(size)
    return (side or 1), (side or 1)


def _has_one_solution(board, box_rows=3, box_cols=3):
    """Whether this grid still has exactly one solution.

    Staging removes givens, and removing givens can admit a *second* solution --
    which would make the practice board a puzzle with two answers, and every
    deduction built on it worth less than a hint. So this gates every fill.
    """
    try:
        return SudokuSolver(board, box_rows, box_cols).count_solutions(1).count == 1
    except ValueError:
        # A cell collides with a digit its own unit already holds, which is not a
        # board the solver will analyse.
        return False


def _empty_cells(board):
    return [(row, col)
            for row in range(len(board))
            for col in range(len(board))
            if board[row][col] == 0]


def _deduction_for(board, technique, box_rows=3, box_cols=3):
    for deduction in deductions_for(board, box_rows, box_cols):
        if deduction.technique == technique:
            return deduction
    return None


#: How many correct digits a staged board should already have entered on it.
#:
#: Neither extreme is right, and both were tried. One digit is a puzzle that has
#: only just been dealt -- there is nothing of the player's about it -- and forty
#: is a near-finished grid that reads as a demonstration rather than as a game.
#: Around a dozen is what a board actually looks like partway through, and it is
#: enough that the technique is not sitting behind a wall of singles.
SCENARIO_TARGET_MOVES = 12

#: How far from that target a stop point may be and still be worth measuring.
#:
#: The engines are the entire cost of building a scenario, so stop points far
#: from the target are not scored at all unless nothing better has turned up.
#: Widening this makes the search slower without making the board better.
SCENARIO_TARGET_WINDOW = 6

#: How many cells get pencil marks. A player marks the position they have worked
#: out, not the whole grid; filling every cell turns the board into a wall of
#: digits and hides the very pattern the technique is about.
SCENARIO_TARGET_MARKS = 6


def _naked_single_cells(board, box_rows=3, box_cols=3):
    """Empty cells with exactly one candidate -- what a beginner just fills in."""
    state = CandidateState.from_board(board, box_rows=box_rows, box_cols=box_cols)
    out = []
    for row in range(len(board)):
        for col in range(len(board)):
            if board[row][col] != 0:
                continue
            candidates = set(state.candidates_for(row, col))
            if len(candidates) == 1:
                out.append((row, col, next(iter(candidates))))
    return out


def _pencil_in(board, rng, box_rows=3, box_cols=3, marks=SCENARIO_TARGET_MARKS):
    """Put the right candidates in a handful of cells, as a player would.

    The marks are the *real* candidates for this position, not decoration: a
    pencil mark that is not there yet teaches the wrong thing, and one that is
    wrong is worse than none.
    """
    state = CandidateState.from_board(board, box_rows=box_rows, box_cols=box_cols)
    size = len(board)
    notes: list[list[set[int]]] = [[set() for _ in range(size)] for _ in range(size)]
    options = []
    for row in range(size):
        for col in range(size):
            if board[row][col] != 0:
                continue
            candidates = set(state.candidates_for(row, col))
            # Only tight cells. A cell with seven candidates is not something a
            # player has worked out yet, and marking it reads as noise.
            if 2 <= len(candidates) <= 4:
                options.append((row, col, candidates))
    rng.shuffle(options)
    for row, col, candidates in options[:marks]:
        notes[row][col] = set(candidates)
    return notes


def _play_forward(board, solution, rng, max_moves=40):
    """Enter the easy digits one at a time, and remember every position.

    These are the moves a player makes before the technique becomes the obvious
    thing to look for. Each step is a correct digit the player would have had no
    trouble with, so the board ends up looking played rather than dealt.

    Every intermediate position is returned because playing too far destroys the
    technique: entering the singles it depends on leaves it nothing to say. The
    caller tries each stop point and keeps the best.
    """
    board = [row[:] for row in board]
    entered = set()
    seen: list[tuple[list[list[int]], set[tuple[int, int]]]] = [([row[:] for row in board], set())]
    for _ in range(max_moves):
        options = _naked_single_cells(board)
        if not options:
            break
        row, col, value = rng.choice(options)
        if solution[row][col] != value:
            continue
        board[row][col] = value
        entered.add((row, col))
        seen.append(([row[:] for row in board], set(entered)))
    return seen


def build_scenario(technique, generator, box_rows=None, box_cols=None,
                   attempts=25, deadline_seconds=12.0, seed=0):
    """A position staged around `technique`, set up like a game in progress.

    Starts from a generated board where the technique is available, then enters
    the easy digits the way a player would -- as correct moves of their own --
    until the technique is the cheapest thing left, and pencils in the candidates
    for the position. What the player sees is their own board partway through:
    their digits in their colour, real pencil marks, and one technique standing
    out.

    Returns the same shape as `find_training_board`, plus `user_cells` (the
    digits the player is taken to have entered, so the board can draw them as
    moves rather than as givens), `notes` and `scenario`.
    """
    if technique not in PRACTICEABLE:
        raise ValueError(f"{technique!r} is not something to practise")

    end = time.time() + deadline_seconds
    rng = random.Random(seed)
    best = None
    checked = 0
    for checked in range(1, attempts + 1):
        if time.time() > end:
            break
        made = generator()
        if made is None or len(made) < 2 or made[1] is None:
            continue
        board, solution = made[0], made[1]
        variant = made[2] if len(made) > 2 else None
        rows = box_rows if box_rows else geometry_of(variant, len(board))[0]
        cols = box_cols if box_cols else geometry_of(variant, len(board))[1]
        if _deduction_for(board, technique, rows, cols) is None:
            continue

        for played, entered in _play_forward(board, solution, rng):
            if not entered:
                continue
            distance = abs(len(entered) - SCENARIO_TARGET_MOVES)
            # `board_uses` runs all three engines, and that is the whole cost of
            # this function -- measured at 0.07s, against 0.001s for the solver
            # and 0.007s for a bare deduction. Evaluating every one of the forty
            # stop points a board offers is most of a second of engine time per
            # board, and every one of them except the handful near the target is
            # a board we would not keep anyway. So the window is checked first.
            if distance > SCENARIO_TARGET_WINDOW and best is not None:
                continue
            difficulty = board_uses(played, technique, rows, cols)
            if difficulty is None:
                continue
            if not _has_one_solution(played, rows, cols):
                continue
            # Cheapest technique first, then the stop point closest to a
            # partway-through board. A board that is either untouched or nearly
            # finished teaches the technique, but not the habit of spotting it.
            score = (difficulty, distance)
            if best is not None and score >= best[0]:
                continue
            best = (score, {
                "board": played,
                "solution": [row[:] for row in solution],
                "user_cells": sorted(entered),
                "notes": _pencil_in(played, rng, rows, cols),
                "holes": len(_empty_cells(played)),
                "difficulty": difficulty,
                "attempts": checked,
                "found": True,
                "scenario": True,
                "box_rows": rows,
                "box_cols": cols,
            })
            # Cheap enough to be the common case and worth stopping for: the
            # technique is nearly the cheapest step and the board looks played.
            if difficulty <= 2 and distance <= 1:
                return best[1]

    return best[1] if best is not None else None


def find_training_board(technique, generator, box_rows=None, box_cols=None,
                        attempts=300, deadline_seconds=10.0):
    """Generate boards until one uses `technique`, keeping the earliest found.

    `generator` is called with no arguments and returns whatever
    `main.generate_puzzle` returns. It is asked for a fresh board each time, so
    the caller controls difficulty by choosing what to wrap.

    The deadline is the real constraint. Swordfish turned up on 2 boards in 120
    generated, so some techniques will not be found in any reasonable time, and
    a caller driving a UI needs an answer rather than a spinner. When nothing
    matches, the best board seen so far is still returned with `found` False --
    an approximate board beats telling the player nothing.
    """
    if technique not in PRACTICEABLE:
        raise ValueError(f"{technique!r} is not something to practise")

    end = time.time() + deadline_seconds
    best = None
    checked = 0
    for checked in range(1, attempts + 1):
        if time.time() > end:
            break
        made = generator()
        if made is None:
            continue
        board = made[0]
        variant = made[2] if len(made) > 2 else None
        # Per board, not once at the top: a caller can leave these unset and let
        # the generated variant decide, which is the only way a 4x4 is analysed
        # as a 4x4 rather than as a 9x9 with the edges trimmed.
        rows = box_rows if box_rows else geometry_of(variant, len(board))[0]
        cols = box_cols if box_cols else geometry_of(variant, len(board))[1]
        found = board_uses(board, technique, rows, cols)
        if found is None:
            continue
        shape = {"box_rows": rows, "box_cols": cols}
        if found <= 3:
            return {"board": board, "solution": (made[1] if len(made) > 1 else None),
                    "difficulty": found, "attempts": checked, "found": True,
                    **shape}
        if best is None or found < best["difficulty"]:
            best = {"board": board, "solution": (made[1] if len(made) > 1 else None),
                    "difficulty": found, "attempts": checked, "found": False,
                    **shape}

    if best is not None:
        return best
    return {"board": None, "solution": None, "difficulty": None,
            "attempts": checked, "found": False,
            "box_rows": box_rows or 3, "box_cols": box_cols or 3}
