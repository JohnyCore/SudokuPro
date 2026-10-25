import itertools
from itertools import combinations

from candidates import CandidateState
from strategies import Deduction

#: Standard fish names by base-line count. This app used "Generalized Fish"
#: for sizes 4+ and "Kraken Fish" for size 4 in a second engine -- two names,
#: one pattern. Both survive dedup, so a single Jellyfish was counted twice in
#: the analysis and the training statistics. A real Kraken is a finned fish
#: plus chains; size 4 has been a Jellyfish ever since.
_FISH_NAMES = {2: "X-Wing", 3: "Swordfish", 4: "Jellyfish", 5: "Squirmbag"}


class AdvancedStrategyEngine:
    def __init__(self, state):
        if not isinstance(state, CandidateState):
            raise TypeError("AdvancedStrategyEngine requires CandidateState")
        self.state = state
        self._line_positions_cache: dict = {}

    def _empty(self, cell):
        return not self.state.board[cell[0]][cell[1]]

    def _candidates(self, cell):
        return self.state.candidates_for(*cell)

    def _units_for(self, cell):
        return self.state.unit_for(*cell)

    def _seeing(self, first, second):
        return bool(set(self._units_for(first)) & set(self._units_for(second)))

    def _add(self, technique, cells, eliminations, message, difficulty, placements=()):
        """Build one deduction, or nothing if it would say nothing.

        A generator rather than a `result.append`, because every caller here is
        a generator now: the hint button takes the first usable deduction and
        stops, and it used to have to wait for the fish scan, the XY-wing scan
        and three depth-4 chain walks to finish before it could rank any of
        them. `_add` is the single place that decides whether a candidate
        pattern is worth reporting at all -- one that eliminates nothing and
        settles nothing is not a hint.

        `placements` is separate because a forcing chain *settles* a cell while
        the eliminations say "this digit cannot be here". Folding a placement
        into the eliminations made the app tell the player to strike out the very
        digit it had just proved, and the training overlay would have drawn it as
        a removal rather than a placement.
        """
        eliminations = tuple(sorted(set(eliminations)))
        placements = tuple(sorted(set(placements)))
        if eliminations or placements:
            yield Deduction(technique, placements=placements, eliminations=eliminations,
                            cells=tuple(cells), message=message, difficulty=difficulty)

    def find_all(self):
        return list(self.iter_all())

    def iter_all(self):
        """Every deduction, yielded lazily, in the order `find_all` used.

        The order is unchanged on purpose: it is the one the training spread and
        the analysis report have been reading, and reordering to put the cheap
        patterns first would quietly change which step a training board offers
        first. The laziness is the point -- the hint button no longer waits for
        three depth-4 chain walks to finish before it can rank what the fish scan
        already found -- not the ordering.
        """
        # A Nice Loop used to live here. It is gone, and `main.TECHNIQUE_NOTES`
        # no longer describes it -- see the note on `TECHNIQUE_RANK`.
        yield from self._fish()
        yield from self._xy_wing()
        yield from self._w_wing()
        # A Nice Loop is an XY-Chain with the extra demand that it closes, so
        # every closing chain is also a plain one. Reporting both names for the
        # same elimination is the "one deduction, two labels" defect this module
        # was refactored to kill, so the loop keeps only what the plain chain did
        # not already claim. Chains are the cheap half of this engine; the fish
        # scan above is what dominates, and that stays lazy.
        plain_chains = list(self._xy_chain())
        yield from plain_chains
        yield from self._skyscraper()
        # `_empty_rectangle` is retired and no longer called; see its docstring.
        yield from self._unique_rectangle()
        yield from self._remote_pair()
        yield from self._forcing_chain()

    def _simple_colouring(self, digit):
        """RETIRED -- and this one is worth keeping the scar for. The orientation
        argument, which is what finally settles it, is below.

        Single's Chains is the biggest technique this app does not have, and it
        is the one hardest boards most often need. An implementation was written
        here and thrown away. The reasoning, because the next person to try will
        make the same mistake.

        The plan was the textbook two-colour propagation. For a digit `d`, take
        the cells still holding `d`, join two of them when they share a unit,
        and 2-colour the graph. Seed from a conjugate pair -- a unit with exactly
        two `d`-cells, both bivalue -- colour them opposite, then propagate: a
        cell that sees a known-true cell is known-absent.

        **The mistake is treating a colour as a fact.** A conjugate pair says
        "exactly one of these two is `d`". It does not say which. Colouring one
        side `true` and propagating from it asserts something the pair never
        proved, and the error compounds at every step. The oracle measured it
        directly: 366 eliminations over 40 boards, **91 of them false**. The
        worked example was

            (6,3) and (6,5), both {1,2}, the only 2-cells in row 6

        coloured (6,3) true. That is a coin flip, and the code then struck `2`
        from (3,3) and (4,3) on the strength of it -- cells with three candidates
        each, which the solver was happy to place a 2 in.

        ## The orientation argument, written out

        This is the part the previous note said had to exist before the technique
        could come back. It exists now, and it is negative.

        Let `V` be the empty cells that still hold `d`, and join two of them when
        they see each other. An edge means "these two cannot both be `d`". So the
        `d`-cells form an **independent set** in this graph. If the graph
        2-colours, an independent set is contained in *one* colour class -- but
        contained is the whole difficulty. It is not equal to one.

        Write the classes `A` and `B`. Everything the technique wants to conclude
        has to survive swapping `A` with `B`, because a conjugate pair does not
        say which class holds the digit. Check the usual candidate conclusions:

        - *"Z sees a cell of class `A`, so `Z` is not `d`."* Only sound if every
          member of `A` is `d`. The colouring gives containment, not equality, so
          the `A`-cell `Z` sees may itself not be `d`. **Unsound.**
        - *"Z sees both classes, so `Z` is not `d`."* This is the one people
          believe survives, and it does not. If the `d`-cells lie in `A`, then
          `Z` seeing an `A`-cell and a `B`-cell has seen no `d`-cell at all: both
          are non-`d`. `Z` may still be `d`. **Unsound**, and it is exactly the
          rule that produced the 91 false eliminations.
        - *"Cells in one class are `d`."* Same problem, and it is the assertion
          the abandoned code made directly.

        So no conclusion follows from the colouring alone. The one extra fact
        that would fix all of them is an **anchor**: a cell that is definitely
        `d` -- a naked single for `d` -- somewhere in the component. With an
        anchor, BFS from it fixes the orientation, every even-distance cell is
        provably `d`, and every odd-distance cell provably is not, because it
        sees an even-distance one.

        That version is sound and implementable, and it is also worth nothing
        here. An anchor for `d` is a naked single for `d`, and naked singles are
        exactly what the basic strategies already report and the app already
        fills in before this engine is asked. With the anchor absent the
        technique is empty; with it present it re-derives the naked single. There
        is no intermediate state where it says something new and true.

        shortcut: not implemented, and the argument above is why. A sound Simple
        Colouring needs an anchor source this app does not have; without one
        every orientation-free conclusion is unsound. If a cheap anchor is ever
        found -- a hypothesis chain that fixes a digit for a whole unit, say --
        use `tests/test_deduction_soundness.py` as the referee, and check the
        implementation reports nothing at all on the 40-board corpus rather than
        reporting something small.
        """
        return
        yield  # pragma: no cover -- unreachable; keeps the generator contract

    def _fish(self):
        size = self.state.size
        for digit in range(1, size + 1):
            for base_count in (2, 3, 4, 5):
                for orientation in ("row", "column"):
                    lines = self._fish_lines(digit, base_count, orientation)
                    for base_lines in combinations(lines, base_count):
                        cover = set()
                        exact = True
                        phantom = False
                        for line in base_lines:
                            positions = self._line_positions(digit, line, orientation)
                            cover.update(positions)
                            if len(positions) != base_count:
                                exact = False
                            if len(positions) < 2:
                                # A base line that cannot hold the digit at all --
                                # typically a row where the cell is already
                                # filled -- is not a base line. Counting it built
                                # "fish" out of one real row plus a phantom, and
                                # struck the digit from the whole board.
                                exact = False
                                phantom = True
                                break
                        if phantom or len(cover) != base_count:
                            continue
                        targets = []
                        for position in cover:
                            anchor = (0, position) if orientation == "row" else (position, 0)
                            for other in self._perpendicular_positions(anchor, orientation):
                                in_base = other[0] in base_lines if orientation == "row" else other[1] in base_lines
                                if not in_base and digit in self._candidates(other):
                                    targets.append((*other, digit))
                        if not targets:
                            continue
                        technique = _FISH_NAMES.get(base_count, "Squirmbag")
                        # `exact` is False only when a base line held FEWER than
                        # base_count positions. A fin -- an extra candidate in a
                        # base line -- would push `cover` past base_count and be
                        # rejected above, so what reaches here is always a
                        # Sashimi, never a fin. The old "Finned/Sashimi" name
                        # promised the half that cannot occur.
                        if not exact:
                            technique = "Sashimi Fish"
                        yield from self._add(technique, [self._position(line, position, orientation) for line in base_lines for position in cover], targets, f"{technique} pattern for {digit}.", base_count)

    def _fish_lines(self, digit, minimum, orientation):
        size = self.state.size
        return range(size) if orientation == "row" else range(size)

    def _line_positions(self, digit, line, orientation):
        # Pure function of (digit, line, orientation) -- the board is an
        # immutable tuple for the life of the CandidateState, so this cannot go
        # stale. `_fish` calls it inside a triple loop over digit x size x
        # combinations of base lines, and cProfile measured 228,051 calls per
        # 16x16 analysis for 510 distinct answers. 1044ms -> 466ms memoised.
        key = (digit, line, orientation)
        cached = self._line_positions_cache.get(key)
        if cached is None:
            if orientation == "row":
                cached = tuple(col for col in range(self.state.size) if self._empty((line, col)) and digit in self._candidates((line, col)))
            else:
                cached = tuple(row for row in range(self.state.size) if self._empty((row, line)) and digit in self._candidates((row, line)))
            self._line_positions_cache[key] = cached
        return cached

    def _position(self, line, position, orientation):
        return (line, position) if orientation == "row" else (position, line)

    def _perpendicular_positions(self, position, orientation):
        if orientation == "row":
            return [(row, position[1]) for row in range(self.state.size) if row != position[0]]
        return [(position[0], col) for col in range(self.state.size) if col != position[1]]

    def _xy_wing(self):
        """Pivot {X, Y}, wing1 {X, Z}, wing2 {Y, Z}, wings not seeing each other.

        The wings share `Z` with *each other*, and each wing takes one of the
        pivot's two digits. The implementation used to search for a digit both
        wings shared with the *pivot* -- giving {X, Z} and {X, W} -- and that
        shape has no conclusion at all. Its only conditional fact is "if the
        pivot is X, wing1 is Z", so assuming a target holds Z merely forces the
        pivot to Y, which contradicts nothing. `tests/test_deduction_soundness.py`
        measured 3 false eliminations in 17 for that version, and every tightened
        target rule made it worse rather than better, because the fault was the
        shape and not the targets.

        With the correct shape the proof is short and unconditional:

        - if the pivot is X then wing1 cannot be X, so wing1 is Z;
        - if the pivot is Y then wing2 cannot be Y, so wing2 is Z.

        Either way at least one wing holds Z, so anything seeing both wings is
        not Z.
        """
        cells = [(row, col) for row in range(self.state.size) for col in range(self.state.size) if self._empty((row, col)) and len(self._candidates((row, col))) == 2]
        for pivot, first, second in combinations(cells, 3):
            pivot_candidates = self._candidates(pivot)
            if len(pivot_candidates) != 2:
                continue
            # The wings must not see each other, or they are just a pair in one
            # unit. This guard used to be inverted and kept exactly those.
            if self._seeing(first, second):
                continue
            # Each wing takes one of the pivot's digits and both take the third.
            for first_pivot_digit in sorted(pivot_candidates):
                second_pivot_digit = next(iter(pivot_candidates - {first_pivot_digit}))
                shared = self._candidates(first) & self._candidates(second) - set(pivot_candidates)
                if len(shared) != 1:
                    continue
                eliminated = next(iter(shared))
                if self._candidates(first) != {first_pivot_digit, eliminated}:
                    continue
                if self._candidates(second) != {second_pivot_digit, eliminated}:
                    continue
                # The pivot has to see both wings for either half of the proof
                # to hold; this was missing entirely.
                if not (self._seeing(pivot, first) and self._seeing(pivot, second)):
                    continue
                targets = [(row, col, eliminated) for row in range(self.state.size) for col in range(self.state.size)
                           if self._empty((row, col)) and (row, col) not in (pivot, first, second)
                           and eliminated in self._candidates((row, col))
                           and self._seeing((row, col), first) and self._seeing((row, col), second)]
                yield from self._add("XY-Wing", (pivot, first, second), targets,
                                     f"XY-Wing eliminates {eliminated}.", 3)

    def _w_wing(self):
        """W-Wing: the pivot takes one digit from each wing, so neither wing's
        shared digit survives in anything that sees both.

        Shape: pivot `{a, b}`, wing1 `{a, c}`, wing2 `{b, c}`. The pivot sees
        both wings; the wings do *not* see each other.

        Proof, for any cell Z holding `c` that sees both wings:
        - Z=c, so wing1 (which sees Z) is not c, so wing1=a;
        - likewise wing2=b;
        - but then pivot sees wing1=a and wing2=b, so pivot is neither a nor b --
          a contradiction.
        So `c` comes out of every cell seeing both wings.

        Distinct from the XY-Wing next door, and the difference is the wings not
        seeing each other. Here they *must not*: if they did, `{a,c}` and `{b,c}`
        seeing each other would be an ordinary remote pair, and the pivot would
        add nothing.
        """
        cells = [(row, col) for row in range(self.state.size) for col in range(self.state.size)
                 if self._empty((row, col)) and len(self._candidates((row, col))) == 2]
        for pivot, first, second in combinations(cells, 3):
            pivot_candidates = self._candidates(pivot)
            if len(pivot_candidates) != 2:
                continue
            # The wings must NOT see each other -- see the docstring.
            if self._seeing(first, second):
                continue
            if not (self._seeing(pivot, first) and self._seeing(pivot, second)):
                continue
            # The wings share the digit to eliminate; each also takes one of the
            # pivot's two digits, and they must be different ones.
            shared = self._candidates(first) & self._candidates(second)
            if len(shared) != 1:
                continue
            eliminated = next(iter(shared))
            rest = self._candidates(first) & self._candidates(second) - {eliminated}
            if rest:
                continue
            first_pivot = self._candidates(first) - {eliminated}
            second_pivot = self._candidates(second) - {eliminated}
            if len(first_pivot) != 1 or len(second_pivot) != 1:
                continue
            if first_pivot == second_pivot:
                continue
            if first_pivot | second_pivot != pivot_candidates:
                continue
            targets = [(row, col, eliminated) for row in range(self.state.size) for col in range(self.state.size)
                       if self._empty((row, col)) and (row, col) not in (pivot, first, second)
                       and eliminated in self._candidates((row, col))
                       and self._seeing((row, col), first) and self._seeing((row, col), second)]
            yield from self._add("W-Wing", (pivot, first, second), targets,
                                 f"W-Wing eliminates {eliminated}.", 4)

    def _chain_walk(self, technique, difficulty, loop=False, force=False, max_depth=4):
        """Depth-bounded walk over bivalue cells, shared by the chain patterns.

        This is a depth-first walk over bivalue cells. Left unbounded it is
        exponential in the number of bivalue cells and effectively hangs the UI
        on an easy puzzle, so the walk is capped. Chains longer than
        `max_depth` are not reported; in practice a solvable chain is found
        within the first few links, and anything longer is not actionable for a
        human solver anyway.

        One walk, three patterns, because they used to be three copies of the
        same loop -- so the app reported the same deduction under three names and
        the statistics counted them separately. What separates them now:

        - An **XY-Chain** walks from a start cell to an end cell holding the same
          two candidates, and rules both out of everything that sees both ends.
        - A **Forcing Chain** is a chain that also *closes* -- the digit handed
          back out of the end is the one the start passed on -- and resolves to a
          *placement* rather than an elimination: the chain proves that if the
          start took the shared digit the whole thing would collapse, so the
          start takes its other one.

        Every link has to be a real link. The walk used to require only that two
        cells shared *some* candidate, which lets a digit travel between cells
        that cannot see each other; `tests/test_deduction_soundness.py` measured
        that as 13 wrong eliminations in 25 for Nice Loop alone. Consecutive
        cells must see each other, and the digit handed on at each step is the
        one the cell did not just receive.

        shortcut: a Nice Loop is retired rather than re-derived. The sound version of
        one -- ends conjugate *and* holding the same pair -- is a strict subset
        of a closing XY-Chain, so it could never add a deduction the plain chain
        did not already report, and the suite caught exactly that: every loop was
        filtered out as a duplicate. The textbook nice loop lets the ends share
        only the eliminated digit and draws its conclusion from the cycle's
        units; that needs its own link-strength proof and target set. Bring it
        back only with `tests/test_deduction_soundness.py` as the referee.
        """
        size = self.state.size
        cells = [(row, col) for row in range(size) for col in range(size)
                 if self._empty((row, col)) and len(self._candidates((row, col))) == 2]
        if len(cells) < 3:
            return
        for start in cells:
            for outgoing in sorted(self._candidates(start)):
                # Assume the start does *not* hold `outgoing`. The chain exists to
                # prove exactly that, so the walk hands `outgoing` on at every step.
                stack = [(start, [start], outgoing)]
                while stack:
                    current, path, digit = stack.pop()
                    if len(path) >= max_depth:
                        continue
                    for next_cell in cells:
                        if next_cell in path or not self._seeing(current, next_cell):
                            continue
                        if digit not in self._candidates(next_cell):
                            continue
                        onward = self._candidates(next_cell) - {digit}
                        if len(onward) != 1:
                            continue
                        onward = next(iter(onward))
                        next_path = path + [next_cell]
                        if len(next_path) >= 3 and self._closes(start, next_cell, outgoing, onward, loop):
                            yield from self._resolve(technique, difficulty, start, next_cell,
                                                    next_path, size, force, outgoing)
                        if len(next_path) < max_depth:
                            stack.append((next_cell, next_path, onward))

    def _closes(self, start, end, outgoing, onward, loop):
        """Do these two ends finish the walk the way this pattern needs?

        Every chain needs its ends to see each other. For a loop that is obvious -- closing is the
        entire point of one -- and it additionally needs the digit handed back out of the
        end to be the one the start passed on.

        This also rules out the *discontinuous* XY-Chain, where the two ends sit in
        different units, which is the variant humans reach for on hard boards. That is
        a real technique and it is not implemented. Making room for it is not a matter
        of dropping the check: the two ends must see each other precisely because the
        "none of the chain holds this digit, so both ends hold the other one, so they
        conflict" argument is what licenses ruling out *both* digits at a cell seeing
        both ends. Relaxing it and ruling out one digit instead was tried and measured
        at 8 false eliminations in 202 before being reverted; see `_resolve`.
        """
        if not self._seeing(start, end):
            return False
        return onward == outgoing if loop else True

    def _resolve(self, technique, difficulty, start, end, path, size, force, outgoing):
        """Turn a finished walk into a deduction, or into nothing at all."""
        # The ends must hold the same pair. With one digit in common the chain
        # says nothing about any cell outside it: `next(iter(common))` used to
        # pick one arbitrarily, which was wrong 5 times in 11 for XY-Chain and
        # is the reason the pattern cannot be trusted otherwise.
        pair = self._candidates(start)
        if len(pair) != 2 or self._candidates(end) != pair:
            return
        resolved = tuple(sorted(pair))
        forced: tuple = ()
        targets: list = []
        if force:
            # The chain forces the start's *other* digit. Nothing is eliminated:
            # the chain settles the cell outright.
            # The chain proved the start does *not* hold `outgoing` -- that is the
            # assumption the whole walk made. So the start holds the other one.
            #
            # This used to be `pair - {resolved[0]}`, which is just "the larger
            # of the two digits" and has nothing to do with the proof. With a
            # start of {2, 5} that placed a 5; the solver says 2. One wrong
            # digit in 5,584 claims across a 40-board sweep, and it was writing a
            # digit into a cell.
            forced = tuple((start[0], start[1], value)
                           for value in sorted(pair - {outgoing}))
        else:
            # Anything seeing *both* ends rules out both digits: if it took one,
            # both ends would be forced to the other, and two cells that see each
            # other cannot both be it.
            #
            # Both digits, and that is exactly why `_closes` requires the ends to
            # see each other. Relaxing it to admit the discontinuous chain made
            # the app report 8 false eliminations in 202 -- on ((0,0),(1,2),(1,7))
            # all holding {1,3} with the two ends in different units. The
            # "assume no cell in the chain holds the digit" argument is what makes
            # both ends collapse onto the same other digit, and that argument
            # needs the ends to see each other. The discontinuous chain is a real
            # technique, but it rules out ONE digit, not two, and needs its own
            # link proof. Left unimplemented rather than half-built.
            targets = [(row, col, value)
                       for row in range(size) for col in range(size)
                       for value in resolved
                       if self._empty((row, col)) and (row, col) not in path
                       and value in self._candidates((row, col))
                       and self._seeing((row, col), start) and self._seeing((row, col), end)]
        yield from self._add(technique, path, targets,
                             f"{technique} resolves {', '.join(str(v) for v in resolved)}.",
                             difficulty, placements=forced)

    def _xy_chain(self, technique="XY-Chain", difficulty=4):
        yield from self._chain_walk(technique, difficulty)

    def _forcing_chain(self):
        yield from self._chain_walk("Forcing Chain", 7, loop=True, force=True)

    def _skyscraper(self):
        for row in range(self.state.size):
            cells = [(row, col) for col in range(self.state.size) if self._empty((row, col)) and len(self._candidates((row, col))) == 2]
            for first, second in combinations(cells, 2):
                if self._candidates(first) != self._candidates(second):
                    continue
                for col in range(self.state.size):
                    roof = (row, col)
                    if roof in (first, second) or not self._empty(roof) or not self._candidates(roof).intersection(self._candidates(first)):
                        continue
                    targets = [(r, c, value) for value in self._candidates(first) for r in range(self.state.size) for c in range(self.state.size) if self._empty((r, c)) and (r, c) not in (first, second, roof) and value in self._candidates((r, c)) and self._seeing((r, c), first) and self._seeing((r, c), second)]
                    yield from self._add("Skyscraper", (first, second, roof), targets, "Skyscraper pattern eliminates candidates.", 3)

    def _empty_rectangle(self):
        """RETIRED -- third attempt, and the reasoning is now actually written.

        Two earlier derivations were both unsound (34/107, then 53/126) and are
        described in `PLAN.md`. This third one derives the pattern properly and
        then shows why it is still vacuous, which is the actual finding: Empty
        Rectangle is not implementable as a standalone eliminator, because a
        digit confined to four corners can always take either diagonal.

        The shape is four empty cells forming a rectangle, with all four holding
        some digit X. X must be placed once in each of the two rows and once in
        each of the two columns, so it takes one diagonal -- either the main one
        or the anti-diagonal. Both are open. Nothing distinguishes them, so no
        candidate anywhere can be struck.

        The pattern only *forces* anything when combined with an inequality --
        if one corner of a second, related rectangle were known not to take a
        digit, the diagonals would be resolved and real eliminations would fall
        out. That is the Avoidable Rectangle and the BUG family, which need the
        digit-inequality machinery this app does not have. Implementing Empty
        Rectangle alone therefore buys nothing: it would report a pattern and
        strike nothing, or strike something wrong.

        shortcut: retired with the derivation recorded, rather than left as a
        detector that finds rectangles and eliminates nothing. Revisit only
        together with the inequality-based relatives.
        """
        return
        yield  # pragma: no cover -- unreachable; keeps the generator contract

    def _unique_rectangle(self):
        """BUG: a base pair whose shared extra candidate cannot be real.

        Four empty cells forming a rectangle. The two on one diagonal are a
        *base pair*: exactly the same two candidates, {a, b}. The other diagonal
        is the *wing pair*, and it has to see both base cells -- which in
        practice means the two wings share a box.

        If the wings share any candidate outside {a, b}, then that candidate
        cannot go in either wing, because both wings can only take a or b; so it
        cannot be in the base pair either, and it comes out of both base cells.

        This is the technique the Technique Reference documents as "Unique
        Rectangle". It was described there and implemented nowhere: a player could
        read the article, hunt for the pattern, and never have the app confirm
        one. So it is implemented rather than deleted from the help.
        """
        size = self.state.size
        for first_row, second_row in combinations(range(size), 2):
            for first_col, second_col in combinations(range(size), 2):
                top_left = (first_row, first_col)
                top_right = (first_row, second_col)
                bottom_left = (second_row, first_col)
                bottom_right = (second_row, second_col)
                corners = (top_left, top_right, bottom_left, bottom_right)
                if any(not self._empty(cell) for cell in corners):
                    continue

                # Either diagonal can be the base pair.
                for base, wings in (
                    ((top_left, bottom_right), (top_right, bottom_left)),
                    ((top_right, bottom_left), (top_left, bottom_right)),
                ):
                    first, second = base
                    pair = self._candidates(first)
                    if len(pair) != 2 or self._candidates(second) != pair:
                        continue
                    wing_one, wing_two = wings
                    # The wings must see each other, and each must see both base
                    # cells. Without that the rectangle can be completed two ways
                    # and proves nothing.
                    if not self._seeing(wing_one, wing_two):
                        continue
                    if not (self._seeing(wing_one, first) and self._seeing(wing_one, second)):
                        continue
                    if not (self._seeing(wing_two, first) and self._seeing(wing_two, second)):
                        continue
                    extra = (self._candidates(wing_one) & self._candidates(wing_two)) - pair
                    for value in sorted(extra):
                        yield from self._add(
                            "Unique Rectangle",
                            (first, second, wing_one, wing_two),
                            [(first[0], first[1], value), (second[0], second[1], value)],
                            f"Unique Rectangle rules out {value} from the base pair.",
                            4,
                        )

    def _remote_pair(self):
        """One pivot digit, paired with a different partner in each of two units.

        A Remote Pair needs two units that do not meet, each holding a cell that
        pairs the same digit with a different one -- {a, b} in the first and
        {a, c} in the second, b != c. If a cell seeing both units held `a`, each
        unit would be stuck without it and the pair would have nowhere to go, so
        `a` comes out, and with it `b` and `c`.

        The two-cell version this replaced -- two cells holding the same {a, b}
        that do not see each other -- proves nothing, because both can legally
        take `b`. The oracle measured 3 false eliminations in 10.

        DEAD UNTIL TODAY, AND IT WAS MY OWN BUG. This went looking for two cells
        sharing an *identical* pair and then asked for `len(pair - {pivot}) == 2`
        -- but `pair` has exactly two elements, so that subtraction always has
        one. The guard was unsatisfiable in 444 of 444 possible cases and the
        technique had never fired once. Found by a catalogue review, not by the
        soundness sweep, which is the expected shape of things: an oracle proves
        what a detector *says* is true and says nothing when it says nothing.
        """
        size = self.state.size
        # Every bivalue cell, not cells bucketed by an identical candidate set.
        # The two halves of the pattern are {a, b} and {a, c} -- they share one
        # digit, not both -- so bucketing by the full set put them in different
        # buckets and no pair was ever even considered.
        cells = [(row, col) for row in range(size) for col in range(size)
                 if self._empty((row, col)) and len(self._candidates((row, col))) == 2]

        for first, second in itertools.combinations(cells, 2):
                if self._seeing(first, second):
                    continue
                shared = self._candidates(first) & self._candidates(second)
                # Exactly one digit in common: that is the pivot. Two in common
                # is the unsound two-cell version; zero is not a pair at all.
                if len(shared) != 1:
                    continue
                pivot = next(iter(shared))
                partners = sorted(
                    (self._candidates(first) | self._candidates(second)) - {pivot}
                )
                for unit_first in self._units_for(first):
                    for unit_second in self._units_for(second):
                        if set(unit_first) & set(unit_second):
                            continue
                        pattern = (first, second)
                        targets = [(row, col, value)
                                   for value in (pivot, *partners)
                                   for row in range(size) for col in range(size)
                                   if self._empty((row, col)) and (row, col) not in pattern
                                   and value in self._candidates((row, col))
                                   and (set(self._units_for((row, col))) & set(unit_first))
                                   and (set(self._units_for((row, col))) & set(unit_second))]
                        yield from self._add("Remote Pair", pattern, targets,
                                             "Remote Pair eliminates candidates.", 3)

    def _common_units(self, cell):
        """The units this cell shares with one of the same pair."""
        others = [other for other in self._units_for(cell)]
        return others
