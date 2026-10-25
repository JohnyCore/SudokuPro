import hashlib
import json
import os
import tempfile
from dataclasses import dataclass
from datetime import date, datetime, timedelta
from pathlib import Path
from zoneinfo import ZoneInfo, ZoneInfoNotFoundError

DAILY_SCHEMA_VERSION = 1

#: Origin of the daily-puzzle series, mixed into every seed.
#:
#: Bumping this deliberately starts a new series: every date from the bump
#: onward generates a different board, and no date already played changes. It is
#: the reason "the daily" can be a thing with a history rather than a hash that
#: happens to be stable.
DAILY_EPOCH = date(2026, 1, 1)


@dataclass(frozen=True)
class DailyPuzzle:
    day: str
    timezone: str
    seed: int
    difficulty: str
    board: tuple[tuple[int, ...], ...]
    solution: tuple[tuple[int, ...], ...]
    variant: str = "standard"
    generated: bool = True


class DailyChallengeManager:
    def __init__(self, data_dir, timezone="UTC", difficulty="Medium"):
        self.data_dir = Path(data_dir)
        self.data_dir.mkdir(parents=True, exist_ok=True)
        self.path = self.data_dir / "daily_challenges.json"
        self.timezone = self._timezone(timezone)
        self.difficulty = difficulty
        self.data = self._load()

    def current_day(self, now=None):
        current = now or datetime.now(self.timezone)
        if current.tzinfo is None:
            current = current.replace(tzinfo=self.timezone)
        return current.astimezone(self.timezone).date()

    def puzzle_for(self, day=None, generator=None, generated=None):
        """Today's puzzle, from cache or freshly made.

        ``generated`` lets the caller pass a board it has already produced --
        the daily challenge generates on a worker thread now, so the result
        arrives here rather than being produced by the callback.
        """
        current = self.current_day() if day is None else day
        key = current.isoformat()
        cached = self.data.get("puzzles", {}).get(key)
        if cached:
            return self._decode_puzzle(cached)
        if generated is None and generator is None:
            raise ValueError("A generator or a generated puzzle is required")
        if generated is not None:
            board, solution, variant_name = generated
            variant = {"variant": variant_name} if isinstance(variant_name, str) else (variant_name or {})
        else:
            seed = self.seed_for(current)
            result = generator(seed)
            if result is None:
                raise RuntimeError("Daily puzzle generation failed")
            board, solution, variant = result
        puzzle = DailyPuzzle(key, str(self.timezone), self.seed_for(current), self.difficulty, tuple(tuple(row) for row in board), tuple(tuple(row) for row in solution), variant.get("variant", "standard"))
        self.data.setdefault("puzzles", {})[key] = self._encode_puzzle(puzzle)
        self._save()
        return puzzle

    def seed_for(self, day):
        """The seed for a day's puzzle: the same one for everyone, everywhere.

        The seed is a pure function of the date and the difficulty, and of
        nothing else. It used to hash the manager's timezone in as well, which
        meant a player in Wellington and a player in Los Angeles asking for the
        same date got two different puzzles -- so nobody could ever share a
        daily result, and a leaderboard would have had to be split per offset.

        `DAILY_EPOCH` anchors the series to a fixed origin date and is mixed
        into the hash, so the daily puzzle set is a versioned thing: bump it and
        every future date generates a different (and better) board, without
        touching any date already played. Leaving it out would mean the daily
        seed is still perfectly reproducible, but there would be no way to start
        a new series deliberately.

        Difficulty is in the key because `seed_for` is what the generator is
        asked to produce. Without it, "today's Medium" and "today's Hard" would
        share a seed, and sharing that seed would not share the puzzle.
        """
        value = f"{DAILY_EPOCH.isoformat()}|{day.isoformat()}|{self.difficulty}"
        return int.from_bytes(
            hashlib.sha256(value.encode()).digest()[:8], "big"
        ) % (36 ** 10)

    def record_result(self, day, time_seconds, mistakes, hints=0, completed=True):
        key = day.isoformat() if isinstance(day, date) else str(day)
        self.data.setdefault("results", {})[key] = {"time_seconds": int(time_seconds), "mistakes": int(mistakes), "hints": int(hints), "completed": bool(completed)}
        self._save()
        return self.data["results"][key]

    def result_for(self, day):
        key = day.isoformat() if isinstance(day, date) else str(day)
        return self.data.get("results", {}).get(key)

    def history(self):
        return tuple(sorted(self.data.get("results", {}).items()))

    def streaks(self, today=None):
        current = today or self.current_day()
        completed = {date.fromisoformat(day) for day, result in self.data.get("results", {}).items() if result.get("completed")}
        current_streak = 0
        cursor = current
        while cursor in completed:
            current_streak += 1
            cursor -= timedelta(days=1)
        longest = 0
        for day in sorted(completed):
            if day - timedelta(days=1) in completed:
                continue
            length = 1
            cursor = day + timedelta(days=1)
            while cursor in completed:
                length += 1
                cursor += timedelta(days=1)
            longest = max(longest, length)
        return {"current": current_streak, "longest": max(longest, current_streak)}

    def share_text(self, day=None, time_seconds=None, mistakes=None):
        key = (day or self.current_day()).isoformat()
        result = self.result_for(key) or {}
        elapsed = result.get("time_seconds", time_seconds or 0)
        wrong = result.get("mistakes", mistakes or 0)
        minutes, seconds = divmod(int(elapsed), 60)
        return f"Sudoku Daily {key}: {minutes:02}:{seconds:02}, {wrong} mistake(s)."

    def _load(self):
        try:
            data = json.loads(self.path.read_text(encoding="utf-8"))
            return data if data.get("schema_version") == DAILY_SCHEMA_VERSION else {"schema_version": DAILY_SCHEMA_VERSION, "puzzles": {}, "results": {}}
        except (FileNotFoundError, OSError, json.JSONDecodeError, AttributeError):
            return {"schema_version": DAILY_SCHEMA_VERSION, "puzzles": {}, "results": {}}

    def _save(self):
        temporary = None
        try:
            with tempfile.NamedTemporaryFile("w", encoding="utf-8", dir=self.data_dir, prefix="daily.", suffix=".tmp", delete=False) as handle:
                temporary = Path(handle.name)
                json.dump(self.data, handle, indent=2)
                handle.flush()
                os.fsync(handle.fileno())
            os.replace(temporary, self.path)
            temporary = None
        finally:
            if temporary is not None:
                temporary.unlink(missing_ok=True)

    def _encode_puzzle(self, puzzle):
        return {"day": puzzle.day, "timezone": puzzle.timezone, "seed": puzzle.seed, "difficulty": puzzle.difficulty, "board": [list(row) for row in puzzle.board], "solution": [list(row) for row in puzzle.solution], "variant": puzzle.variant}

    def _decode_puzzle(self, data):
        return DailyPuzzle(data["day"], data["timezone"], int(data["seed"]), data["difficulty"], tuple(tuple(row) for row in data["board"]), tuple(tuple(row) for row in data["solution"]), data.get("variant", "standard"))

    @staticmethod
    def _timezone(name):
        try:
            return ZoneInfo(name)
        except ZoneInfoNotFoundError as error:
            raise ValueError(f"Unknown timezone: {name}") from error
