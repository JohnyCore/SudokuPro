from dataclasses import dataclass, field

from advanced_search import AdvancedSearch, TechniquePolicy
from candidates import CandidateState
from explanations import ExplainEngine
from solver import SudokuSolver
from strategies import Deduction, StrategyEngine


@dataclass(frozen=True)
class AnalysisStep:
    index: int
    deduction: Deduction
    explanation: ExplainEngine

    @property
    def technique(self):
        return self.deduction.technique

    @property
    def difficulty(self):
        return self.deduction.difficulty


@dataclass
class AnalysisReport:
    steps: tuple[AnalysisStep, ...]
    uniqueness: str
    deviations: tuple[tuple[int, int], ...] = ()
    solution_paths: tuple[tuple[tuple[int, ...], ...], ...] = ()

    def grouped(self):
        groups: dict = {}
        for step in self.steps:
            groups.setdefault(step.technique, []).append(step)
        return groups

    def filtered(self, minimum_difficulty=None, maximum_difficulty=None, techniques=None, sort="difficulty"):
        selected = list(self.steps)
        if minimum_difficulty is not None:
            selected = [step for step in selected if step.difficulty >= minimum_difficulty]
        if maximum_difficulty is not None:
            selected = [step for step in selected if step.difficulty <= maximum_difficulty]
        if techniques is not None:
            allowed = set(techniques)
            selected = [step for step in selected if step.technique in allowed]
        key = (lambda step: (step.difficulty, step.technique)) if sort == "difficulty" else (lambda step: (-step.difficulty, step.technique))
        return tuple(sorted(selected, key=key))


@dataclass
class AnalysisHistory:
    steps: list[AnalysisStep] = field(default_factory=list)
    snapshots: list[dict] = field(default_factory=list)

    def record(self, step, snapshot):
        self.steps.append(step)
        self.snapshots.append(snapshot)

    def undo(self, state):
        if not self.snapshots:
            return False
        snapshot = self.snapshots.pop()
        self.steps.pop()
        state.restore(snapshot)
        return True


class AnalysisService:
    def __init__(self, board, solution, box_rows=3, box_cols=3, variant="standard", manual_notes=None, show_all=False, cages=None):
        self.state = CandidateState.from_board(board, box_rows, box_cols, variant, manual_notes, show_all, cages=cages)
        self.solution = tuple(tuple(row) for row in solution)
        self.explain_engine = ExplainEngine(self.state)
        self.history = AnalysisHistory()
        self.step_counter = 0

    def all_deductions(self):
        return self._deductions()

    def _deductions(self):
        deductions = StrategyEngine(self.state).find_all()
        advanced = AdvancedSearch(self.state, TechniquePolicy()).find_all()
        unique = []
        seen = set()
        for deduction in deductions + advanced:
            key = (deduction.technique, deduction.placements, deduction.eliminations, deduction.restrictions, deduction.cells)
            if key not in seen:
                seen.add(key)
                unique.append(deduction)
        return unique

    def next_step(self):
        deductions = self._deductions()
        if not deductions:
            return None
        deduction = min(deductions, key=lambda item: item.difficulty)
        return AnalysisStep(self.step_counter, deduction, self.explain_engine.explain(deduction))

    def all_steps(self):
        steps = []
        for index, deduction in enumerate(self._deductions()):
            steps.append(AnalysisStep(self.step_counter + index, deduction, self.explain_engine.explain(deduction)))
        return AnalysisReport(tuple(steps), self.uniqueness())

    def apply_step(self, step):
        snapshot = self.state.snapshot()
        step.deduction.apply_to(self.state)
        self.history.record(step, snapshot)
        return self.state

    def solve_up_to(self, count):
        for _ in range(max(0, count)):
            step = self.next_step()
            if step is None:
                break
            self.apply_step(step)
            self.step_counter += 1
        return self.state

    def uniqueness(self, limit=2):
        result = SudokuSolver([list(row) for row in self.state.board], self.state.box_rows, self.state.box_cols).count_solutions(limit)
        if result.cancelled:
            return "Cancelled"
        if result.count == 0:
            return "No solution"
        if result.count == 1:
            return "Unique solution"
        return "Multiple solutions"

    def solution_paths(self, limit=2):
        solver = SudokuSolver([list(row) for row in self.state.board], self.state.box_rows, self.state.box_cols)
        return tuple(solver.solutions(limit))

    def deviations(self, human_solution=None):
        reference = tuple(tuple(row) for row in (human_solution or self.solution))
        return tuple((row, col) for row in range(self.state.size) for col in range(self.state.size) if self.state.board[row][col] and self.state.board[row][col] != reference[row][col])

    def comparison(self, other_solution=None):
        other = tuple(tuple(row) for row in (other_solution or self.solution))
        return tuple(
            {
                "cell": (row, col),
                "current": self.state.board[row][col],
                "primary": self.solution[row][col],
                "comparison": other[row][col],
                "different": other[row][col] != self.solution[row][col],
            }
            for row in range(self.state.size)
            for col in range(self.state.size)
        )

