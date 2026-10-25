from dataclasses import dataclass
from datetime import date


@dataclass(frozen=True)
class GameMode:
    name: str
    timed: bool = False
    accuracy_required: bool = False
    hints_limited: bool = False
    no_mistakes: bool = False
    mistake_limit: int | None = None
    time_limit: int | None = None
    hint_limit: int | None = None


CASUAL = GameMode("Casual")
DAILY = GameMode("Daily Challenge", timed=True)
TIMED = GameMode("Timed Challenge", timed=True, time_limit=900)
ACCURACY = GameMode("Accuracy Challenge", accuracy_required=True, no_mistakes=True)
HINT_LIMITED = GameMode("Hint-Limited", hints_limited=True, hint_limit=1)
NO_MISTAKES = GameMode("No-Mistake", no_mistakes=True, mistake_limit=0)

#: Finish it quickly. Timed Challenge allows fifteen minutes, which is long
#: enough that it only bites on the largest boards; five minutes turns the clock
#: into the point of the puzzle rather than a background detail. It reuses the
#: same `time_limit` enforcement, so it needs no new machinery to be real.
SPRINT = GameMode("Sprint", timed=True, time_limit=300)

#: No assistance at all. `HINT_LIMITED` allowed exactly one hint, which is a
#: question about whether you would spend it; this removes the option and leaves
#: only the board. `hint_limit=0` means the allowance check trips on the first
#: press, so the existing guard already enforces it.
NO_HINTS = GameMode("No Hints", hints_limited=True, hint_limit=0)


@dataclass
class MistakeRecord:
    cell: tuple[int, int]
    value: int
    expected: int


@dataclass
class GameSummary:
    status: str
    elapsed_seconds: int
    mistakes: tuple[MistakeRecord, ...]
    hints_used: int
    achievements: tuple[str, ...]


class ChallengeSession:
    def __init__(self, mode=CASUAL, puzzle_id=None):
        self.mode = mode
        self.puzzle_id = puzzle_id or ""
        self.elapsed_seconds = 0
        self.mistakes = []
        self.hints_used = 0
        self.paused = False
        self.finished = False
        self.completed = False
        self.revealed = False
        self.completion_id = None

    def start(self):
        self.paused = False
        self.finished = False
        return self

    def pause(self):
        if not self.finished:
            self.paused = True

    def resume(self):
        if not self.finished:
            self.paused = False

    def tick(self, seconds=1):
        if not self.paused and not self.finished:
            self.elapsed_seconds += seconds
        if self.mode.time_limit is not None and self.elapsed_seconds >= self.mode.time_limit:
            self.finish(False)

    def record_mistake(self, cell, value, expected):
        if self.finished:
            return False
        self.mistakes.append(MistakeRecord(tuple(cell), value, expected))
        if self.mode.no_mistakes or self.mode.mistake_limit is not None and len(self.mistakes) > (self.mode.mistake_limit or 0):
            self.finish(False)
        return True

    def use_hint(self):
        if self.finished:
            return False
        if self.mode.hint_limit is not None and self.hints_used >= self.mode.hint_limit:
            return False
        self.hints_used += 1
        return True

    def finish(self, completed, completion_id=None):
        if self.finished:
            return self.summary()
        if self.mode.accuracy_required and self.mistakes:
            completed = False
        self.completed = bool(completed)
        self.finished = True
        self.completion_id = completion_id
        return self.summary()

    def reveal_solution(self):
        self.revealed = True
        self.finished = True

    def summary(self):
        return GameSummary("Completed" if self.completed else "Game Over" if self.finished else "In Progress", self.elapsed_seconds, tuple(self.mistakes), self.hints_used, self.achievements())

    def mistake_review(self):
        return tuple(self.mistakes)

    def achievements(self):
        achievements = []
        if self.completed and self.elapsed_seconds < 300:
            achievements.append("Speed Demon")
        if self.completed and not self.mistakes:
            achievements.append("Flawless")
        if self.completed and self.hints_used == 0:
            achievements.append("No Hints Needed")
        if self.completed and self.puzzle_id:
            achievements.append("Puzzle Completed")
        return tuple(achievements)


def custom_mode(mistake_limit=None, time_limit=None, hint_limit=None):
    return GameMode("Custom", mistake_limit=mistake_limit, time_limit=time_limit, hint_limit=hint_limit, hints_limited=hint_limit is not None, timed=time_limit is not None)


def daily_seed(day=None, timezone=None, difficulty="Medium"):
    """The seed for a day's daily puzzle.

    This used to hash `f"daily|{day}|{timezone_offset}"` while
    `DailyChallengeManager.seed_for` hashed `f"daily|{day}|{str(self.timezone)}"`,
    so the same day produced a different puzzle depending on which one you
    asked: 2026-03-01 gave 3135808786926804 here and 3457712059312985 there.
    Harmless only because `main.py` discards the value this returns and uses
    `seed_for`. Two derivations of "today's puzzle" is a trap either way, so
    there is now one, and this delegates to it.

    `timezone` is accepted and ignored. It used to be mixed into the seed,
    which meant the daily puzzle was per UTC offset: two people asking for the
    same date in different zones got different boards, so the puzzle was not
    shareable and no leaderboard across the world could mean anything. It is
    still the zone the *day* rolls over in -- `timezone` used to change the
    seed without changing which day it is, which was the part that was never
    wanted -- but the seed is now a pure function of the date and difficulty,
    so everybody plays the same board.
    """
    from daily import DailyChallengeManager

    manager = DailyChallengeManager.__new__(DailyChallengeManager)
    manager.timezone = timezone or "UTC"
    manager.difficulty = difficulty
    return manager.seed_for(day or date.today())


def daily_mode(day=None, timezone=None, difficulty="Medium"):
    """The challenge mode for a day, and the seed its puzzle is generated from.

    `difficulty` is passed through rather than defaulted and forgotten, so the
    mode and the seed agree. The caller used to take the seed from here and
    then ignore it, seeding from `DailyChallengeManager.seed_for` instead --
    two derivations of "today's puzzle", one of them dead.
    """
    return DAILY, daily_seed(day, timezone, difficulty)
