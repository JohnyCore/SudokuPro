from dataclasses import dataclass

from candidates import CandidateState


@dataclass(frozen=True)
class Explanation:
    technique: str
    difficulty: int
    affected_cells: tuple[tuple[int, int], ...]
    affected_units: tuple[tuple[tuple[int, int], ...], ...]
    chain: tuple[tuple[int, int], ...]
    plain: str
    formal: str
    placements: tuple[tuple[int, int, int], ...]
    eliminations: tuple[tuple[int, int, int], ...]
    restrictions: tuple[tuple[int, int, tuple[int, ...]], ...]

    @property
    def has_action(self):
        return bool(self.placements or self.eliminations or self.restrictions)


class ExplainEngine:
    def __init__(self, state):
        if not isinstance(state, CandidateState):
            raise TypeError("ExplainEngine requires CandidateState")
        self.state = state

    def explain(self, deduction):
        cells = self._affected_cells(deduction)
        units = self._affected_units(cells)
        chain = deduction.cells if "chain" in deduction.technique.lower() or deduction.technique in {"X-Wing", "Swordfish", "Jellyfish", "Squirmbag", "Sashimi Fish"} else ()
        plain = self._plain(deduction)
        formal = self._formal(deduction)
        return Explanation(
            deduction.technique,
            deduction.difficulty,
            cells,
            units,
            chain,
            plain,
            formal,
            deduction.placements,
            deduction.eliminations,
            deduction.restrictions,
        )

    def _affected_cells(self, deduction):
        cells = set(deduction.cells)
        cells.update((row, col) for row, col, _ in deduction.placements)
        cells.update((row, col) for row, col, _ in deduction.eliminations)
        cells.update((row, col) for row, col, _ in deduction.restrictions)
        return tuple(sorted(cells))

    def _affected_units(self, cells):
        units = []
        for row, col in cells:
            for unit in self.state.unit_for(row, col):
                if unit not in units:
                    units.append(unit)
        return tuple(units)

    def _plain(self, deduction):
        if deduction.placements:
            placements = ", ".join(f"put {value} in R{row + 1}C{col + 1}" for row, col, value in deduction.placements)
            if deduction.eliminations:
                eliminations = ", ".join(f"remove {value} from R{row + 1}C{col + 1}" for row, col, value in deduction.eliminations)
                return f"{deduction.technique}: {placements}, and {eliminations}."
            return f"{deduction.technique}: {placements}."
        if deduction.eliminations:
            eliminations = ", ".join(f"remove {value} from R{row + 1}C{col + 1}" for row, col, value in deduction.eliminations)
            return f"{deduction.technique}: {eliminations} because {deduction.message}"
        if deduction.restrictions:
            restrictions = ", ".join(f"R{row + 1}C{col + 1} keeps {list(values)}" for row, col, values in deduction.restrictions)
            return f"{deduction.technique}: {restrictions}. {deduction.message}"
        return f"{deduction.technique}: {deduction.message}"

    def _formal(self, deduction):
        pieces = [f"Technique={deduction.technique}", f"Difficulty={deduction.difficulty}"]
        if deduction.placements:
            pieces.extend(f"r{row + 1}c{col + 1}={value}" for row, col, value in deduction.placements)
        if deduction.eliminations:
            pieces.extend(f"r{row + 1}c{col + 1}-={value}" for row, col, value in deduction.eliminations)
        if deduction.restrictions:
            pieces.extend(f"r{row + 1}c{col + 1}⊆{list(values)}" for row, col, values in deduction.restrictions)
        return "; ".join(pieces)


class StepSession:
    def __init__(self, state, deductions):
        if not isinstance(state, CandidateState):
            raise TypeError("StepSession requires CandidateState")
        self.state = state
        self.deductions = tuple(deductions)
        self.engine = ExplainEngine(state)
        self.index = 0
        self.history = []
        self.applied = set()

    @property
    def current(self):
        if not self.deductions:
            return None
        return self.deductions[self.index]

    def inspect(self, index=None):
        deduction = self.current if index is None else self.deductions[index]
        return self.engine.explain(deduction) if deduction else None

    def apply(self, index=None):
        deduction = self.current if index is None else self.deductions[index]
        if deduction is None:
            return False
        self.history.append((index if index is not None else self.index, self.state.snapshot()))
        deduction.apply_to(self.state)
        actual_index = index if index is not None else self.index
        self.applied.add(actual_index)
        return True

    def undo(self):
        if not self.history:
            return False
        index, snapshot = self.history.pop()
        self.state.restore(snapshot)
        self.applied.discard(index)
        return True

    def next(self):
        if self.index + 1 < len(self.deductions):
            self.index += 1
            return self.inspect()
        return None

    def previous(self):
        if self.index > 0:
            self.index -= 1
            return self.inspect()
        return None

    def has_next(self):
        return self.index + 1 < len(self.deductions)

    def has_previous(self):
        return self.index > 0
