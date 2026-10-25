from dataclasses import dataclass, field

from analysis import AnalysisService
from explanations import ExplainEngine

BEGINNER_TECHNIQUES = ("Naked Single", "Hidden Single", "Locked Candidates / Pointing", "Locked Candidates / Claiming", "Naked Pair", "Hidden Pair", "Naked Triple", "X-Wing")
ADVANCED_TECHNIQUES = ("Swordfish", "XY-Wing", "XY-Chain", "Jellyfish")


@dataclass(frozen=True)
class Lesson:
    technique: str
    deduction: object
    explanation: object
    expected_cell: tuple[int, int]
    expected_value: int | None

    @property
    def prompt(self):
        if self.expected_value is None:
            return f"Find the candidate elimination for {self.technique}."
        return f"Apply {self.technique}: what value belongs at R{self.expected_cell[0] + 1}C{self.expected_cell[1] + 1}?"


@dataclass
class TrainingProgress:
    attempts: int = 0
    correct: int = 0
    mistakes: list[dict] = field(default_factory=list)
    completed: list[str] = field(default_factory=list)

    @property
    def accuracy(self):
        return round(self.correct / self.attempts * 100, 1) if self.attempts else 0.0

    def snapshot(self):
        return {"attempts": self.attempts, "correct": self.correct, "mistakes": list(self.mistakes), "completed": list(self.completed)}


class TrainingSession:
    def __init__(self, board, solution, box_rows=3, box_cols=3, variant="standard", techniques=None, first_steps=False):
        self.service = AnalysisService(board, solution, box_rows, box_cols, variant)
        self.techniques = tuple(techniques or (BEGINNER_TECHNIQUES if first_steps else BEGINNER_TECHNIQUES + ADVANCED_TECHNIQUES))
        self.beginner_only = first_steps
        self.progress = TrainingProgress()
        self.lesson = None
        self.start()

    def available_lessons(self):
        deductions = self.service.all_deductions()
        return [deduction for deduction in deductions if deduction.technique in self.techniques and (deduction.placements or deduction.eliminations)]

    def start(self):
        deductions = self.available_lessons()
        if not deductions:
            self.lesson = None
            return None
        deduction = min(deductions, key=lambda item: item.difficulty)
        explanation = ExplainEngine(self.service.state).explain(deduction)
        if deduction.placements:
            row, col, value = deduction.placements[0]
            expected = (row, col, value)
        else:
            row, col, value = deduction.eliminations[0]
            expected = (row, col, None)
        self.lesson = Lesson(deduction.technique, deduction, explanation, (row, col), value if expected[2] is not None else None)
        return self.lesson

    def submit(self, cell, value=None):
        if self.lesson is None:
            return False, "No training lesson is available."
        self.progress.attempts += 1
        cell = tuple(cell)
        if self.lesson.expected_value is None:
            correct = cell == self.lesson.expected_cell and value == self._eliminated_value()
        else:
            correct = cell == self.lesson.expected_cell and value == self.lesson.expected_value
        if correct:
            self.progress.correct += 1
            if self.lesson.technique not in self.progress.completed:
                self.progress.completed.append(self.lesson.technique)
            self.lesson.deduction.apply_to(self.service.state)
            self.start()
            return True, self.lesson.explanation.plain if self.lesson else "Lesson completed."
        mistake = {"technique": self.lesson.technique, "cell": cell, "value": value, "expected_cell": self.lesson.expected_cell, "expected_value": self.lesson.expected_value}
        self.progress.mistakes.append(mistake)
        return False, self.explain_mistake(mistake)

    def _eliminated_value(self):
        return self.lesson.deduction.eliminations[0][2] if self.lesson and self.lesson.deduction.eliminations else None

    def explain_mistake(self, mistake):
        return f"Not quite. {mistake['technique']} points to R{mistake['expected_cell'][0] + 1}C{mistake['expected_cell'][1] + 1}" + (f" with value {mistake['expected_value']}." if mistake["expected_value"] is not None else ".")

    def mistake_review(self):
        return tuple(self.progress.mistakes)

    def first_steps(self):
        self.beginner_only = True
        self.techniques = BEGINNER_TECHNIQUES
        return self.start()
