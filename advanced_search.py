from dataclasses import dataclass
from itertools import combinations

from candidates import CandidateState
from strategies import Deduction

TECHNIQUE_RANK = {
    "Naked Single": 1,
    "Hidden Single": 1,
    "Locked Candidates / Pointing": 2,
    "Locked Candidates / Claiming": 2,
    "Naked Pair": 2,
    "Hidden Pair": 2,
    "Naked Triple": 3,
    "X-Wing": 3,
    "XY-Wing": 3,
    "Naked Quad": 4,
    "Hidden Triple": 4,
    "Hidden Quad": 5,
    "Swordfish": 4,
    "XY-Chain": 4,
    "Skyscraper": 4,
    "Unique Rectangle": 4,
    "Remote Pair": 4,
    "Sashimi Fish": 4,
    "W-Wing": 4,
    "Jellyfish": 5,
    "Squirmbag": 6,
    # ALS is retired for the same reason as the rest: implemented, rated 6, and
    # written up in the reference, but its guard guaranteed it could never emit
    # anything. See `AdvancedSearch._als`.
    # "Dynamic Chain" was listed here too, but `dynamic_chain` is a search API
    # that returns a ChainSearchResult rather than a Deduction, so no analysis
    # ever reported the technique. Removed rather than rated.
    #
    # Death Blossom, Sue de Coq and Almost-Deadly Pattern were listed here with
    # difficulties and their detectors were three `return None` stubs, so the
    # table claimed the app knew three techniques it did not. They are removed
    # rather than implemented blind: see the roadmap's F7.
    #
    # Nice Loop joins them, for a different reason. It was implemented, and it
    # was wrong: `tests/test_deduction_soundness.py` measured 13 wrong
    # eliminations in 25, because the walk asked only that consecutive cells
    # shared a candidate and never that they could see each other. Re-derived so
    # that it is sound, it turned out to be a *strict subset* of a closing
    # XY-Chain -- every one of its deductions was already reported under the
    # plain chain's name. A technique that can never add a new answer is not a
    # technique, so it is removed rather than kept as a duplicate label.
    #
    # Empty Rectangle joins them for a third reason: it was implemented twice,
    # and both implementations struck the digit from cells the rectangle did not
    # constrain at all -- 34 false eliminations in 107 in one place, 1797 in
    # 5082 in the other, and 1296 deductions on an empty grid. Two correct
    # derivations were attempted and both failed; see the docstring on
    # `advanced_strategies._empty_rectangle`, which records why.
    "Forcing Chain": 7,
}


@dataclass(frozen=True)
class TechniquePolicy:
    allowed: frozenset[str] | None = None
    minimum_difficulty: int = 1
    maximum_difficulty: int = 10

    def allows(self, technique):
        difficulty = TECHNIQUE_RANK.get(technique, 10)
        return (self.allowed is None or technique in self.allowed) and self.minimum_difficulty <= difficulty <= self.maximum_difficulty

    @classmethod
    def only(cls, *techniques):
        return cls(frozenset(techniques))


@dataclass(frozen=True)
class ChainSearchResult:
    chain: tuple[tuple[int, int], ...]
    cycle: bool
    exhausted: bool
    visited: int
    explanation: str


class AdvancedSearch:
    def __init__(self, state, policy=None):
        if not isinstance(state, CandidateState):
            raise TypeError("AdvancedSearch requires CandidateState")
        self.state = state
        self.policy = policy or TechniquePolicy()
        self._positions_cache: dict = {}

    def _rank(self, technique):
        return TECHNIQUE_RANK.get(technique, 10)

    def _add(self, result, technique, cells, eliminations, message):
        if self.policy.allows(technique) and eliminations:
            result.append(Deduction(technique, eliminations=tuple(sorted(set(eliminations))), cells=tuple(cells), message=message, difficulty=self._rank(technique)))

    def find_all(self):
        result: list = []
        self._fish_variants(result)
        # `_als` is retired and no longer called; see its docstring.
        # `_empty_rectangle_variants` is retired and no longer called.
        return sorted(result, key=lambda deduction: (deduction.difficulty, deduction.technique))

    def _fish_variants(self, result):
        for digit in range(1, self.state.size + 1):
            for orientation in ("row", "column"):
                lines = self._candidate_lines(digit, orientation)
                for base_count in (2, 3, 4):
                    for base_lines in combinations(lines, base_count):
                        cover = set()
                        valid = True
                        for line in base_lines:
                            positions = self._positions(digit, line, orientation)
                            # `!= base_count`, not `< 2`. A Swordfish must use
                            # three positions in each base line; accepting two
                            # let a "3-column cover" be built from rows that never
                            # held the digit in the third column, so nothing
                            # confined it there. Cover likewise must be exactly
                            # the fish size, not merely at least that large.
                            cover.update(positions)
                            if len(positions) != base_count:
                                valid = False
                                break
                        if not valid or len(cover) != base_count:
                            continue
                        technique = {2: "X-Wing", 3: "Swordfish", 4: "Jellyfish"}.get(base_count)
                        if not technique:
                            continue
                        # An extra line meeting the cover does NOT make this a
                        # different fish. The targets below are derived from the
                        # base lines alone, so a pattern found here reported the
                        # identical eliminations as the plain fish it came from
                        # under a second name -- the same Jellyfish counted
                        # twice in the analysis and the training statistics.
                        # Franken/Mutant/Finned all require base lines beyond
                        # the exact ones, which this engine never builds.
                        targets = []
                        for position in cover:
                            anchor = (0, position) if orientation == "row" else (position, 0)
                            for other in self._perpendicular(anchor, orientation):
                                line = other[0] if orientation == "row" else other[1]
                                if line in base_lines or digit not in self.state.candidates_for(*other):
                                    continue
                                targets.append((*other, digit))
                        cells = [self._cell(line, position, orientation) for line in base_lines for position in cover]
                        self._add(result, technique, cells, targets, f"{technique} pattern for {digit}.")

    def _candidate_lines(self, digit, orientation):
        lines = []
        for line in range(self.state.size):
            if len(self._positions(digit, line, orientation)) >= 2:
                lines.append(line)
        return lines

    def _positions(self, digit, line, orientation):
        # Memoised for the same reason as `AdvancedStrategyEngine._line_positions`:
        # pure function of (digit, line, orientation), recomputed inside the fish
        # loop's triple nesting.
        key = (digit, line, orientation)
        cached = self._positions_cache.get(key)
        if cached is None:
            if orientation == "row":
                cached = frozenset(col for col in range(self.state.size) if not self.state.board[line][col] and digit in self.state.candidates_for(line, col))
            else:
                cached = frozenset(row for row in range(self.state.size) if not self.state.board[row][line] and digit in self.state.candidates_for(row, line))
            self._positions_cache[key] = cached
        return cached

    def _cell(self, line, position, orientation):
        return (line, position) if orientation == "row" else (position, line)

    def _perpendicular(self, position, orientation):
        if orientation == "row":
            return [(row, position[1]) for row in range(self.state.size)]
        return [(position[0], col) for col in range(self.state.size)]

    def _als(self, result):
        """RETIRED. Was here, and it could never have fired.

        The guard and the conclusion contradicted each other. The guard skipped
        a set unless the digit appeared in *no* cell of the unit outside the
        selected cells; the conclusion then built its targets from the cells
        outside the selected ones that *do* have the digit. The guard therefore
        guaranteed the target list was always empty, and `_add` emits nothing
        without eliminations. An Almost-Locked Set was rated difficulty 6 in the
        ranking table and written up in the Technique Reference while the code
        behind it was unreachable -- the same defect as the three `return None`
        stubs the table was already cleaned of once.

        An ALS is a real technique and worth implementing properly. It is not
        worth implementing twice: once wrong.
        """
        return

    def _empty_rectangle_variants(self, result):
        """RETIRED. Was here, and it was the worst offender in the app.

        It took the digits common to four empty rectangle corners and struck
        each one from *every other empty cell on the board* -- there was no
        geometric condition on the target at all. `tests/test_deduction_soundness.py`
        measured 1797 false eliminations in 5082. The sibling detector in
        `advanced_strategies._empty_rectangle` had the same flaw and was retired
        for the same reason; its docstring explains why two derivations of a
        correct Empty Rectangle both failed.
        """
        return

    def dynamic_chain(self, start, max_length=8, max_visits=5000):
        stack = [(start, [start], {start})]
        visited_count = 0
        while stack and visited_count < max_visits:
            current, chain, visited = stack.pop()
            visited_count += 1
            candidates = self.state.candidates_for(*current)
            for next_cell in self._neighbors(current, candidates):
                if next_cell in visited:
                    cycle = chain + [next_cell]
                    return ChainSearchResult(tuple(cycle), True, False, visited_count, "The chain revisits a cell, so it is circular rather than an endless search.")
                next_chain = chain + [next_cell]
                if len(next_chain) > max_length:
                    continue
                stack.append((next_cell, next_chain, visited | {next_cell}))
        return ChainSearchResult((), False, not stack, visited_count, "The search stopped without finding a cycle.")

    def _neighbors(self, cell, candidates):
        for other in range(self.state.size):
            for neighbor in ((other, cell[1]), (cell[0], other)):
                if neighbor != cell and not self.state.board[neighbor[0]][neighbor[1]] and self.state.candidates_for(*neighbor) & candidates:
                    yield neighbor

    def explain_circular_logic(self, chain):
        if not chain:
            return "No circular chain was supplied."
        cells = ", ".join(f"({row + 1},{col + 1})" for row, col in chain)
        return f"The chain {cells} revisits a cell, so using it as a new deduction would only recreate its own assumptions."
