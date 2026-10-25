from dataclasses import dataclass
from itertools import combinations

from candidates import CandidateState


@dataclass(frozen=True)
class Deduction:
    technique: str
    placements: tuple[tuple[int, int, int], ...] = ()
    eliminations: tuple[tuple[int, int, int], ...] = ()
    restrictions: tuple[tuple[int, int, tuple[int, ...]], ...] = ()
    cells: tuple[tuple[int, int], ...] = ()
    message: str = ""
    difficulty: int = 1

    def apply_to(self, state):
        for row, col, value in self.placements:
            if value in state.candidates_for(row, col):
                state.toggle_candidate(row, col, value)
                state.set_manual_notes(row, col, {value})
        for row, col, value in self.eliminations:
            if row < state.size and col < state.size and value in state.manual_notes.get((row, col), set()):
                state.toggle_candidate(row, col, value)
        for row, col, values in self.restrictions:
            if not state.board[row][col]:
                state.set_manual_notes(row, col, set(values))
        return state


class StrategyEngine:
    def __init__(self, state):
        if not isinstance(state, CandidateState):
            raise TypeError("StrategyEngine requires CandidateState")
        self.state = state

    def find_all(self):
        return list(self.iter_all())

    def iter_all(self):
        """Every deduction, yielded lazily.

        `find_all` used to build the whole list, which forced a caller that only
        wanted the easiest deduction -- the hint button -- to pay for all of
        them. The four families are yielded in cheapest-first order and the
        per-technique helpers are generators, so a caller that stops at the
        first good hint never runs the ones behind it. `find_all` stays
        available and still returns a list, because the training spread, the
        analysis report and the technique tables genuinely want every
        deduction.
        """
        yield from self._singles()
        yield from self._locked_candidates()
        yield from self._naked_subsets()
        yield from self._hidden_subsets()

    def find_next(self):
        return min(self.iter_all(), key=lambda deduction: deduction.difficulty, default=None)

    def iter_singles(self):
        """Just the naked and hidden singles.

        Split out because singles are the cheapest family in either engine by a
        wide margin and they are the *only* deductions in the project rated
        difficulty 1 -- every other pattern in both engines is rated 2 or worse.
        That makes this family a floor: if a board has any single at all, the
        easiest possible hint is one of them, and the caller can stop without
        running the subset scans or the advanced engine. `HintEngine.get_hint`
        is the caller that does.
        """
        return self._singles()

    def _empty_cells(self, unit):
        return [(row, col) for row, col in unit if not self.state.board[row][col]]

    def _candidates(self, cell):
        return self.state.candidates_for(*cell)

    def _singles(self):
        for row in range(self.state.size):
            for col in range(self.state.size):
                candidates = self._candidates((row, col))
                if len(candidates) == 1:
                    value = next(iter(candidates))
                    yield Deduction("Naked Single", ((row, col, value),), cells=((row, col),), message=f"Cell ({row + 1},{col + 1}) can only be {value}.", difficulty=1)
        for unit in self.state.units():
            for value in range(1, self.state.size + 1):
                cells = [cell for cell in self._empty_cells(unit) if value in self._candidates(cell)]
                if len(cells) == 1:
                    row, col = cells[0]
                    yield Deduction("Hidden Single", ((row, col, value),), cells=tuple(cells), message=f"{value} can only go in ({row + 1},{col + 1}) in this unit.", difficulty=1)

    def _locked_candidates(self):
        for box in self.state.units()[2 * self.state.size:]:
            for value in range(1, self.state.size + 1):
                cells = [cell for cell in self._empty_cells(box) if value in self._candidates(cell)]
                if len(cells) < 2:
                    continue
                rows = {row for row, col in cells}
                cols = {col for row, col in cells}
                if len(rows) == 1:
                    row = next(iter(rows))
                    targets = tuple((row, col, value) for col in range(self.state.size) if (row, col) not in cells and (row, col) in self._empty_cells(self.state.units()[row]) and value in self._candidates((row, col)))
                    if targets:
                        yield Deduction("Locked Candidates / Pointing", eliminations=targets, cells=tuple(cells), message=f"Within the box, {value} is confined to row {row + 1}.", difficulty=2)
                if len(cols) == 1:
                    col = next(iter(cols))
                    targets = tuple((row, col, value) for row in range(self.state.size) if (row, col) not in cells and (row, col) in self._empty_cells(self.state.units()[self.state.size + col]) and value in self._candidates((row, col)))
                    if targets:
                        yield Deduction("Locked Candidates / Claiming", eliminations=targets, cells=tuple(cells), message=f"Within the box, {value} is confined to column {col + 1}.", difficulty=2)

    def _naked_subsets(self):
        for unit in self.state.units():
            cells = self._empty_cells(unit)
            for size, name, difficulty in ((2, "Naked Pair", 2), (3, "Naked Triple", 3), (4, "Naked Quad", 4)):
                for selected in combinations(cells, size):
                    candidate_union = set().union(*(self._candidates(cell) for cell in selected))
                    if len(candidate_union) != size or any(not self._candidates(cell).issubset(candidate_union) for cell in selected):
                        continue
                    targets = tuple((row, col, value) for row, col in unit if (row, col) not in selected for value in candidate_union if value in self._candidates((row, col)))
                    if targets:
                        yield Deduction(name, eliminations=targets, cells=tuple(selected), message=f"{name} cells {self._format_cells(selected)} contain only {sorted(candidate_union)}.", difficulty=difficulty)

    def _hidden_subsets(self):
        for unit in self.state.units():
            cells = self._empty_cells(unit)
            for size, name, difficulty in ((2, "Hidden Pair", 2), (3, "Hidden Triple", 3), (4, "Hidden Quad", 4)):
                for values in combinations(range(1, self.state.size + 1), size):
                    positions = [cell for cell in cells if self._candidates(cell).intersection(values)]
                    if len(positions) != size or any(sum(value in self._candidates(cell) for cell in positions) == 0 for value in values):
                        continue
                    restrictions = tuple((row, col, values) for row, col in positions)
                    yield Deduction(name, restrictions=restrictions, cells=tuple(positions), message=f"{name} values {list(values)} are confined to {self._format_cells(positions)}.", difficulty=difficulty)

    def _format_cells(self, cells):
        return ", ".join(f"({row + 1},{col + 1})" for row, col in cells)
