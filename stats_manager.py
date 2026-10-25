import json
import uuid
from datetime import datetime, timedelta
from pathlib import Path
from typing import Any

# Shared constants (duplicated from main.py to avoid circular imports)
TIME_UNAVAILABLE = "--"

DIFFICULTY_LEVELS = ["Easy", "Medium", "Hard", "Expert"]

KILLER_SUDOKU_LABEL = "Killer Sudoku"

CUSTOM_SUDOKU_LABELS = [
    "4x4 Sudoku",
    "6x6 Sudoku",
    "8x8 Sudoku",
    "9x9 Sudoku",
    "10x10 Sudoku",
    "12x12 Sudoku",
    "15x15 Sudoku",
    "16x16 Sudoku",
]

ALL_GAME_LABELS = [*DIFFICULTY_LEVELS, KILLER_SUDOKU_LABEL, *CUSTOM_SUDOKU_LABELS]

DEFAULT_CUSTOM_DIFFICULTY = "Medium"


def difficulty_parts(label: str) -> tuple[str | None, str | None]:
    """Split any game label into (base label, difficulty), or (None, None).

    Covers the custom board sizes and Killer, so every label that can carry a
    difficulty is parsed the same way. A bare base label -- "12x12 Sudoku" or
    "Killer Sudoku", as written before these had difficulties -- is accepted
    and reported at the default difficulty, so an existing save still loads and
    still means the same board.
    """
    text = str(label)
    for base in (*CUSTOM_SUDOKU_LABELS, KILLER_SUDOKU_LABEL):
        if text == base:
            return base, DEFAULT_CUSTOM_DIFFICULTY
        prefix = f"{base} - "
        if text.startswith(prefix):
            difficulty = text[len(prefix):]
            if difficulty in DIFFICULTY_LEVELS:
                return base, difficulty
            return None, None
    return None, None
def _atomic_write_text(path: Path, content: str) -> None:
    """Write text to a file atomically via a temporary file."""
    tmp = path.with_suffix(".tmp")
    tmp.write_text(content, encoding="utf-8")
    tmp.replace(path)


def difficulty_matches(recorded: str, wanted: str) -> bool:
    if recorded == wanted:
        return True
    base, _difficulty = difficulty_parts(recorded)
    return base is not None and base == wanted
    """Does a saved difficulty belong under the chosen filter?"""
    if recorded == wanted:
        return True
    base, _difficulty = difficulty_parts(recorded)
    return base is not None and base == wanted


def _time_to_seconds(time_str: str) -> int:
    try:
        time_parts = str(time_str).split(":")
        if len(time_parts) != 2:
            return 0
        return max(0, int(time_parts[0]) * 60 + int(time_parts[1]))
    except (TypeError, ValueError):
        return 0


def _seconds_to_time(seconds: int) -> str:
    mins = seconds // 60
    secs = seconds % 60
    return f"{mins:02}:{secs:02}"


def _times_to_time(times: list[int], best: bool = False, worst: bool = False) -> str:
    if not times:
        return "--"
    if best:
        return _seconds_to_time(min(times))
    if worst:
        return _seconds_to_time(max(times))
    return _seconds_to_time(int(sum(times) / len(times)))


class StatisticsManager:
    """Manages game statistics and history.

    Pure logic - no Qt dependencies. All file I/O is atomic.
    """

    def __init__(self, stats_file: Path):
        self.stats_file = Path(stats_file)
        self.stats = self._load_stats()

    def _load_stats(self) -> list[dict[str, Any]]:
        """Load stats from file."""
        try:
            with open(self.stats_file) as f:
                stats = json.load(f)
                return [self._normalize_entry(entry, index) for index, entry in enumerate(stats, start=1)]
        except (FileNotFoundError, json.JSONDecodeError, OSError):
            return []

    def save_stats(self) -> None:
        """Save stats to file atomically."""
        try:
            _atomic_write_text(self.stats_file, json.dumps(self.stats, indent=2))
        except OSError:
            pass

    def has_completion(self, completion_id: str) -> bool:
        return bool(completion_id) and any(entry.get("completion_id") == completion_id for entry in self.stats)

    def start_attempt(self, puzzle_id: str, difficulty: str, variant: str, seed: str,
                      size: int | None = None, box_rows: int | None = None, box_cols: int | None = None) -> dict[str, Any]:
        if any(entry.get("puzzle_id") == puzzle_id and entry.get("status") == "started" for entry in self.stats):
            return next(entry for entry in self.stats if entry.get("puzzle_id") == puzzle_id and entry.get("status") == "started")
        entry = {
            "id": len(self.stats) + 1,
            "puzzle_id": puzzle_id,
            "difficulty": difficulty,
            "variant": variant,
            "seed": seed,
            "size": size,
            "box_rows": box_rows,
            "box_cols": box_cols,
            "status": "started",
            "completed": False,
            "started_at": datetime.now().isoformat(timespec="seconds"),
            "mistakes": 0,
            "hints": 0,
            "solve_button_used": False,
        }
        self.stats.append(entry)
        self.save_stats()
        return entry

    def finish_attempt(self, puzzle_id: str, status: str, time_seconds: int = 0, mistakes: int = 0,
                       hints: int = 0, solve_button_used: bool = False, completion_id: str | None = None,
                       techniques_used: list[str] | None = None, mistake_history: list[dict] | None = None,
                       difficulty: str = "Unknown", variant: str = "standard") -> dict[str, Any]:
        if status == "completed":
            completion_id = completion_id or uuid.uuid4().hex
            if self.has_completion(completion_id):
                return next(entry for entry in self.stats if entry.get("completion_id") == completion_id)
        entry = next((item for item in reversed(self.stats) if item.get("puzzle_id") == puzzle_id and item.get("status") == "started"), None)
        if entry is None:
            # The caller knows what it just played. This fallback used to hardcode
            # "Unknown"/"standard", so a win after Game Over or a Retry -- both of
            # which close the old row as "failed" first, leaving no "started" row
            # to reuse -- was counted in `total_completed` and `win_rate` but
            # skipped by `by_difficulty` and `personal_bests`. The totals and the
            # breakdown disagreed.
            entry = self.start_attempt(puzzle_id, difficulty, variant, "")
        total_seconds = max(0, int(time_seconds or 0))
        entry.update({
            "status": status,
            "completed": status == "completed",
            "time_seconds": total_seconds,
            "mistakes": max(0, int(mistakes or 0)),
            "hints": max(0, int(hints or 0)),
            "solve_button_used": bool(solve_button_used),
            "completion_id": completion_id,
            "finished_at": datetime.now().isoformat(timespec="seconds"),
        })
        entry["time"] = self._seconds_to_time(total_seconds)
        entry["completed_at"] = entry["finished_at"] if status == "completed" else ""
        if techniques_used is not None:
            entry["techniques_used"] = techniques_used
        if mistake_history is not None:
            entry["mistake_history"] = mistake_history
        self.save_stats()
        return entry

    def has_open_attempt(self, puzzle_id: str) -> bool:
        return any(
            entry.get("puzzle_id") == puzzle_id and entry.get("status") == "started"
            for entry in self.stats
        )

    def get_attempts(self, status: str | None = None) -> list[dict[str, Any]]:
        return [entry for entry in self.stats if status is None or entry.get("status") == status]

    def add_game(self, difficulty: str, seed: str, time_str: str, mistakes: int,
                 solve_button_used: bool = False, tutorial_mode: bool = False,
                 completion_id: str | None = None, techniques_used: list[str] | None = None,
                 mistake_history: list[dict] | None = None) -> dict[str, Any]:
        if completion_id and self.has_completion(completion_id):
            return next(entry for entry in self.stats if entry.get("completion_id") == completion_id)
        game_id = len(self.stats) + 1

        total_seconds = self._time_to_seconds(time_str)

        entry = {
            "id": game_id,
            "difficulty": difficulty,
            "seed": seed,
            "time": time_str,
            "time_seconds": total_seconds,
            "mistakes": mistakes,
            "completed": True,
            "solve_button_used": solve_button_used,
            "tutorial_mode": tutorial_mode,
            "completion_id": completion_id,
            "completed_at": datetime.now().isoformat(timespec="seconds"),
        }
        if techniques_used is not None:
            entry["techniques_used"] = techniques_used
        if mistake_history is not None:
            entry["mistake_history"] = mistake_history
        self.stats.append(entry)
        self.save_stats()
        return entry

    def get_stats(self) -> list[dict[str, Any]]:
        return self.stats

    def get_analytics(self) -> dict[str, Any]:
        return self.build_analytics(self.stats)

    def technique_breakdown(self, stats=None) -> list[dict[str, Any]]:
        """Which techniques the player's hints have actually used.

        This is *not* "how fast are you at each technique", and it is worth
        being precise about why. `techniques_used` is appended to when a hint is
        taken, so it records the technique that solved the cell the player was
        stuck on -- not the techniques they solved unaided. There is no timing
        per technique anywhere in the app, so any "speed per technique" number
        would have to be invented, and an invented number on a statistics screen
        is worse than no number.

        What the data does support is: how often you need a hint at all, and
        which technique it tends to be. A technique that keeps turning up here
        is one worth practising, and `technique_trainer` will deal you a board
        for it.

        Sorted by frequency, most used first, so the thing worth practising is
        the first row rather than buried.
        """
        rows = self.stats if stats is None else stats
        # A technique is counted once per game even if three hints used it --
        # "you needed this three times" is a different fact from "this turned up
        # in three puzzles", and the second is what says whether it is worth
        # practising.
        per_game: dict[str, int] = {}
        hints: dict[str, int] = {}
        for entry in rows:
            used = entry.get("techniques_used") or []
            if not isinstance(used, (list, tuple)):
                continue
            for name in used:
                hints[str(name)] = hints.get(str(name), 0) + 1
            for name in {str(one) for one in used}:
                per_game[str(name)] = per_game.get(str(name), 0) + 1
        breakdown: list[dict[str, Any]] = [
            {
                "technique": name,
                "games": count,
                "hints": hints.get(name, 0),
            }
            for name, count in per_game.items()
        ]
        # Most-turned-up first, so the thing worth practising is the top row.
        breakdown.sort(key=lambda row: (-row["games"], -row["hints"],
                                        row["technique"]))
        return breakdown

    def build_analytics(self, stats: list[dict[str, Any]]) -> dict[str, Any]:
        if not stats:
            return self._empty_analytics()

        completed_games = [g for g in stats if g.get("completed", True)]
        win_count = len(completed_games)
        total_games = len(stats)
        win_rate = (win_count / total_games * 100) if total_games > 0 else 0

        timed_completed_games = [g for g in completed_games if g.get("time_seconds", 0) > 0]
        completed_times = [g.get("time_seconds", 0) for g in timed_completed_games]
        total_time_str = self._times_to_time(completed_times)
        avg_time_str = self._times_to_time(completed_times)

        streaks = self._calculate_streaks(completed_games)
        recent_avg = [g.get("time_seconds", 0) for g in timed_completed_games[-5:]]

        by_difficulty = {}
        personal_bests = {}
        for difficulty in ALL_GAME_LABELS:
            difficulty_games = [g for g in completed_games if difficulty_matches(g.get("difficulty") or "", difficulty)]
            if difficulty_games:
                times = [g.get("time_seconds", 0) for g in difficulty_games if g.get("time_seconds", 0) > 0]
                mistakes = [g.get("mistakes", 0) for g in difficulty_games]
                by_difficulty[difficulty] = {
                    "count": len(difficulty_games),
                    "avg_time": self._times_to_time(times),
                    "best_time": self._times_to_time(times, best=True),
                    "worst_time": self._times_to_time(times, worst=True),
                    "avg_mistakes": round(sum(mistakes) / len(mistakes), 2)
                }
                # Folding this into the loop above is the whole of the fix. It
                # used to be a second pass over the same list for the same
                # numbers -- 13 labels x N games, twice, and `difficulty_matches`
                # parses strings on every one of those calls. It is written as
                # `_seconds_to_time(min(times))` rather than borrowed from
                # `by_difficulty["best_time"]`, even though those two are the
                # same code today: `personal_bests` is rendered in its own place
                # and must not change format just because the summary table
                # decides to show seconds. Same `times`, one pass, no coupling.
                if times:
                    personal_bests[difficulty] = self._seconds_to_time(min(times))

        trend = []
        for game in completed_games[-7:]:
            stamp = game.get("completed_at", "")
            label = stamp[:10] if stamp else f"#{game.get('id', '?')}"
            trend.append({
                "label": label,
                "time": self._times_to_time([game.get("time_seconds", 0)] if game.get("time_seconds", 0) > 0 else []),
                "seconds": game.get("time_seconds", 0),
                "difficulty": game.get("difficulty", "Unknown"),
            })

        by_variant: dict[str, dict[str, Any]] = {}
        by_technique: dict[str, int] = {}
        for game in completed_games:
            variant = game.get("variant", "standard")
            by_variant.setdefault(variant, {"count": 0, "best_time": None})
            by_variant[variant]["count"] += 1
            current_best = by_variant[variant]["best_time"]
            by_variant[variant]["best_time"] = min(current_best or game.get("time_seconds", 0), game.get("time_seconds", 0))
            for technique in game.get("techniques_used", game.get("techniques", [])):
                by_technique[technique] = by_technique.get(technique, 0) + 1

        daily_chart: dict[str, int] = {}
        monthly_chart: dict[str, int] = {}
        for game in completed_games:
            stamp = game.get("completed_at", "")
            if stamp:
                daily_chart[stamp[:10]] = daily_chart.get(stamp[:10], 0) + 1
                monthly_chart[stamp[:7]] = monthly_chart.get(stamp[:7], 0) + 1

        failed_games = [game for game in stats if game.get("status") == "failed"]
        abandoned_games = [game for game in stats if game.get("status") == "abandoned"]
        gave_up_games = [game for game in stats if game.get("status") == "gave_up"]
        average_mistakes = round(sum(game.get("mistakes", 0) for game in completed_games) / len(completed_games), 2) if completed_games else 0
        hints_used = sum(game.get("hints", 0) for game in stats)
        solve_button_usage = sum(bool(game.get("solve_button_used")) for game in stats)

        return {
            "total_games": total_games,
            "total_started": len(stats),
            "total_completed": len(completed_games),
            "total_failed": len(failed_games),
            "total_abandoned": len(abandoned_games),
            "total_gave_up": len(gave_up_games),
            "win_rate": round(win_rate, 1),
            "failure_rate": round((len(failed_games) / total_games * 100) if total_games else 0, 1),
            "average_mistakes": average_mistakes,
            "hints_used": hints_used,
            "solve_button_usage": solve_button_usage,
            "total_time": total_time_str,
            "average_time": avg_time_str,
            "best_time": self._times_to_time(completed_times, best=True),
            "personal_bests": personal_bests,
            "by_variant": by_variant,
            "by_technique": by_technique,
            "daily_chart": [{"label": key, "count": value} for key, value in sorted(daily_chart.items())],
            "monthly_chart": [{"label": key, "count": value} for key, value in sorted(monthly_chart.items())],
            "current_streak": streaks["current"],
            "best_streak": streaks["best"],
            "recent_average": self._times_to_time(recent_avg),
            "by_difficulty": by_difficulty,
            "trend": trend,
        }

    def _empty_analytics(self) -> dict[str, Any]:
        return {
            "total_games": 0,
            "total_started": 0,
            "total_completed": 0,
            "total_failed": 0,
            "total_abandoned": 0,
            "total_gave_up": 0,
            "win_rate": 0,
            "failure_rate": 0,
            "average_mistakes": 0,
            "hints_used": 0,
            "solve_button_usage": 0,
            "total_time": "--",
            "average_time": "--",
            "best_time": "--",
            "personal_bests": {},
            "by_variant": {},
            "by_technique": {},
            "daily_chart": [],
            "monthly_chart": [],
            "current_streak": 0,
            "best_streak": 0,
            "recent_average": "--",
            "by_difficulty": {},
            "trend": [],
        }

    def get_weak_techniques(self, limit: int = 5) -> list[tuple[str, int, int, int, int]]:
        technique_stats = {}
        for entry in self.stats:
            techniques = entry.get("techniques_used", [])
            for tech in techniques:
                if tech not in technique_stats:
                    technique_stats[tech] = {"hint_count": 0, "games": 0}
                technique_stats[tech]["hint_count"] += 1
            if techniques:
                for tech in set(techniques):
                    technique_stats[tech]["games"] += 1

            mistakes = entry.get("mistake_history", [])
            for m in mistakes:
                tech = m.get("technique", "Unknown")
                if tech not in technique_stats:
                    technique_stats[tech] = {"hint_count": 0, "games": 0, "mistakes": 0}
                technique_stats[tech]["mistakes"] = technique_stats[tech].get("mistakes", 0) + 1

        scored = []
        for tech, stats in technique_stats.items():
            hints = stats.get("hint_count", 0)
            games = stats.get("games", 1)
            mistakes = stats.get("mistakes", 0)
            fail_score = hints * 3 + mistakes * 5 - games * 2
            scored.append((tech, max(0, fail_score), hints, mistakes, games))
        scored.sort(key=lambda x: (-x[1], -x[3]))
        return scored[:limit]

    def get_improvement_over_time(self) -> list[dict[str, Any]]:
        monthly = {}
        for entry in self.stats:
            if not entry.get("completed"):
                continue
            stamp = entry.get("completed_at") or entry.get("finished_at", "")
            if not stamp:
                continue
            month = stamp[:7]
            if month not in monthly:
                monthly[month] = {"count": 0, "timed_count": 0, "total_time": 0, "total_mistakes": 0, "total_hints": 0}
            monthly[month]["count"] += 1
            if entry.get("time_seconds", 0) > 0:
                monthly[month]["timed_count"] += 1
                monthly[month]["total_time"] += entry.get("time_seconds", 0)
            monthly[month]["total_mistakes"] += entry.get("mistakes", 0)
            monthly[month]["total_hints"] += entry.get("hints", 0)

        result = []
        for month in sorted(monthly.keys()):
            m = monthly[month]
            avg_time = m["total_time"] / m["timed_count"] if m["timed_count"] else 0
            avg_mistakes = m["total_mistakes"] / m["count"] if m["count"] else 0
            avg_hints = m["total_hints"] / m["count"] if m["count"] else 0
            result.append({
                "month": month,
                "count": m["count"],
                "avg_time": self._seconds_to_time(int(avg_time)),
                "avg_time_seconds": int(avg_time),
                "avg_mistakes": round(avg_mistakes, 1),
                "avg_hints": round(avg_hints, 1),
            })
        return result

    def get_common_mistakes(self, limit: int = 10) -> dict[str, Any]:
        mistake_counts: dict[str, int] = {}
        technique_mistakes: dict[str, int] = {}
        for entry in self.stats:
            for m in entry.get("mistake_history", []):
                tech = m.get("technique", "Unknown")
                technique_mistakes[tech] = technique_mistakes.get(tech, 0) + 1
                cell_key = m.get("cell", "unknown")
                mistake_counts[cell_key] = mistake_counts.get(cell_key, 0) + 1

        sorted_by_technique = sorted(technique_mistakes.items(), key=lambda x: -x[1])
        sorted_by_cell = sorted(mistake_counts.items(), key=lambda x: -x[1])

        total_mistakes = sum(technique_mistakes.values())
        technique_percentages = []
        for tech, count in sorted_by_technique[:limit]:
            pct = round(count / total_mistakes * 100, 1) if total_mistakes else 0
            technique_percentages.append({"technique": tech, "count": count, "percentage": pct})

        return {
            "by_technique": technique_percentages,
            "by_cell": sorted_by_cell[:limit],
            "total": sum(technique_mistakes.values()),
        }

    def get_avg_time_by_technique(self) -> list[dict[str, Any]]:
        tech_times = {}
        for entry in self.stats:
            if not entry.get("completed"):
                continue
            techniques = entry.get("techniques_used", [])
            if not techniques:
                continue
            time_sec = entry.get("time_seconds", 0)
            if time_sec <= 0:
                continue
            for tech in set(techniques):
                if tech not in tech_times:
                    tech_times[tech] = {"total_time": 0, "count": 0, "total_mistakes": 0}
                tech_times[tech]["total_time"] += time_sec
                tech_times[tech]["count"] += 1
                tech_times[tech]["total_mistakes"] += entry.get("mistakes", 0)

        result = []
        for tech in sorted(tech_times.keys()):
            t = tech_times[tech]
            avg = t["total_time"] / t["count"] if t["count"] else 0
            result.append({
                "technique": tech,
                "avg_time": self._seconds_to_time(int(avg)),
                "avg_time_seconds": int(avg),
                "games": t["count"],
                "avg_mistakes": round(t["total_mistakes"] / t["count"], 1) if t["count"] else 0,
            })
        return result

    def recommend_practice(self) -> dict[str, Any]:
        weak = self.get_weak_techniques(limit=10)
        if not weak:
            return {"message": "Not enough data yet. Play more games to get recommendations!", "recommendations": []}

        recommendations = []
        for tech, score, hints, mistakes, games in weak:
            if score > 0:
                recommendations.append({
                    "technique": tech,
                    "priority": "High" if score > 20 else ("Medium" if score > 10 else "Low"),
                    "reason": f"{hints} hint(s) used, {mistakes} mistake(s) in {games} game(s)",
                })
        return {"message": "", "recommendations": recommendations}

    def compare_difficulty_with_past(self) -> dict[str, Any]:
        now = datetime.now()
        recent_cutoff = (now - timedelta(days=30)).isoformat()

        difficulties: dict[str, dict[str, list[dict[str, Any]]]] = {}
        for entry in self.stats:
            if not entry.get("completed"):
                continue
            diff = entry.get("difficulty", "Unknown")
            if diff not in difficulties:
                difficulties[diff] = {"recent": [], "past": []}

            stamp = entry.get("completed_at") or entry.get("finished_at", "")
            bucket = "recent" if stamp is not None and recent_cutoff is not None and stamp >= recent_cutoff and stamp is not None else "past"
            difficulties[diff][bucket].append(entry)

        result = {}
        for diff, buckets in difficulties.items():
            comparison = {}
            for period in ("past", "recent"):
                games = buckets[period]
                if not games:
                    continue
                times = [g.get("time_seconds", 0) for g in games if g.get("time_seconds", 0) > 0]
                mistakes_list = [g.get("mistakes", 0) for g in games]
                comparison[period] = {
                    "count": len(games),
                    "avg_time": self._times_to_time(times),
                    "avg_time_seconds": int(sum(times) / len(times)) if times else 0,
                    "avg_mistakes": round(sum(mistakes_list) / len(mistakes_list), 1),
                }

            if comparison:
                change = ""
                if "past" in comparison and "recent" in comparison:
                    old_avg = comparison["past"]["avg_time_seconds"]
                    new_avg = comparison["recent"]["avg_time_seconds"]
                    if old_avg > 0:
                        pct = int((old_avg - new_avg) / old_avg * 100)
                        change = f"{pct}% faster" if pct >= 0 else f"{abs(pct)}% slower"
                elif "recent" in comparison:
                    change = "New (no past data)"
                result[diff] = {**comparison, "change": change}

        return result

    def get_improvement_tools_data(self) -> dict[str, Any]:
        return {
            "weak_techniques": self.get_weak_techniques(),
            "improvement_over_time": self.get_improvement_over_time(),
            "common_mistakes": self.get_common_mistakes(),
            "avg_time_by_technique": self.get_avg_time_by_technique(),
            "recommendations": self.recommend_practice(),
            "difficulty_comparison": self.compare_difficulty_with_past(),
        }

    def get_filtered_stats(self, difficulty: str = "All", date_range: str = "All Time", search_text: str = "") -> list[dict[str, Any]]:
        stats = list(self.stats)
        if difficulty != "All":
            stats = [entry for entry in stats if difficulty_matches(entry.get("difficulty") or "", difficulty)]

        if date_range != "All Time":
            now = datetime.now()
            windows = {
                "Last 7 Days": now - timedelta(days=7),
                "Last 30 Days": now - timedelta(days=30),
                "This Year": datetime(now.year, 1, 1),
            }
            threshold = windows.get(date_range)
            if threshold is not None:
                stats = [
                    entry for entry in stats
                    if (dt := self._entry_datetime(entry)) is not None and dt >= threshold
                ]

        query = search_text.strip().lower()
        if query:
            stats = [
                entry
                for entry in stats
                if query in str(entry.get("seed", "")).lower()
                or query in str(entry.get("id", "")).lower()
                or query in self.format_game_id(entry.get("id", 0)).lower()
                or query in str(entry.get("difficulty", "")).lower()
                or query in self._display_date(entry).lower()
            ]
        return stats

    def _normalize_entry(self, entry: dict, index: int) -> dict:
        normalized = dict(entry)
        normalized["id"] = normalized.get("id", index)
        normalized["solve_button_used"] = normalized.get("solve_button_used", False)
        # Rows written before "completed" existed carry solve_button_used instead.
        # Defaulting those to a win resurrects the give-up exploit Task 4 closed.
        normalized["completed"] = normalized.get("completed", not normalized["solve_button_used"])
        normalized["status"] = normalized.get(
            "status", "gave_up" if normalized["solve_button_used"] else "completed" if normalized["completed"] else "started"
        )
        normalized["tutorial_mode"] = normalized.get("tutorial_mode", False)
        normalized["completed_at"] = normalized.get("completed_at", "")
        if "time_seconds" not in normalized:
            normalized["time_seconds"] = self._time_to_seconds(normalized.get("time", "00:00"))
        for numeric_key in ("time_seconds", "mistakes", "hints"):
            try:
                normalized[numeric_key] = max(0, int(normalized.get(numeric_key, 0)))
            except (TypeError, ValueError):
                normalized[numeric_key] = 0
        normalized["techniques_used"] = list(normalized.get("techniques_used", normalized.get("techniques", [])) or [])
        normalized["mistake_history"] = list(normalized.get("mistake_history", []) or [])
        return normalized

    def _entry_datetime(self, entry: dict) -> datetime | None:
        stamp = (
            entry.get("completed_at")
            or entry.get("finished_at")
            or entry.get("started_at")
            or ""
        )
        if not stamp:
            return None
        try:
            return datetime.fromisoformat(stamp)
        except ValueError:
            return None

    def _display_date(self, entry: dict) -> str:
        dt = self._entry_datetime(entry)
        return dt.strftime("%Y-%m-%d") if dt else "Unknown"

    def _calculate_streaks(self, completed_games: list[dict]) -> dict[str, int]:
        # One `_display_date` per game, not two. It goes through
        # `_entry_datetime` and `datetime.fromisoformat`, and this function is 18%
        # of a `build_analytics` pass -- instrumented at 10,000 calls for 5,000
        # games, half of them wasted.
        dates = sorted(day for day in map(self._display_date, completed_games) if day != "Unknown")
        if not dates:
            return {"current": 0, "best": 0}
        parsed = [datetime.strptime(day, "%Y-%m-%d").date() for day in dates]
        best = current = 1
        for index in range(1, len(parsed)):
            delta = (parsed[index] - parsed[index - 1]).days
            if delta == 1:
                current += 1
                best = max(best, current)
            else:
                current = 1
        tail = 1
        for index in range(len(parsed) - 1, 0, -1):
            if (parsed[index] - parsed[index - 1]).days == 1:
                tail += 1
            else:
                break
        last_played = parsed[-1]
        gap_to_today = (datetime.now().date() - last_played).days
        current_streak = tail if gap_to_today <= 1 else 0
        return {"current": current_streak, "best": best}

    @staticmethod
    def format_game_id(game_id: int | str) -> str:
        try:
            return f"{int(game_id):06d}"
        except (TypeError, ValueError):
            return "000000"

    @staticmethod
    def _time_to_seconds(time_str: str) -> int:
        try:
            time_parts = str(time_str).split(":")
            if len(time_parts) != 2:
                return 0
            return max(0, int(time_parts[0]) * 60 + int(time_parts[1]))
        except (TypeError, ValueError):
            return 0

    @staticmethod
    def _seconds_to_time(seconds: int) -> str:
        mins = seconds // 60
        secs = seconds % 60
        return f"{mins:02}:{secs:02}"

    @classmethod
    def _times_to_time(cls, times: list[int], best: bool = False, worst: bool = False) -> str:
        if not times:
            return "--"
        if best:
            return cls._seconds_to_time(min(times))
        if worst:
            return cls._seconds_to_time(max(times))
        return cls._seconds_to_time(int(sum(times) / len(times)))

    def export_stats(self, path: Path) -> None:
        _atomic_write_text(path, json.dumps({
            "schema_version": 1,
            "exported_at": datetime.now().isoformat(timespec="seconds"),
            "stats": self.stats,
        }, indent=2))

    def clear_stats(self) -> None:
        self.stats = []
        self.save_stats()

    def delete_game(self, game_id: int | str) -> None:
        self.stats = [g for g in self.stats if g["id"] != game_id]
        for i, g in enumerate(self.stats, start=1):
            g["id"] = i
        self.save_stats()
