# SPDX-License-Identifier: Apache-2.0
# Copyright (c) 2026 Carlo Perassi. Licensed under the Apache License 2.0.
"""The CDCL core: conflict-driven clause learning with two-watched literals.

The architecture is the one established by MiniSat and refined by Glucose and
CaDiCaL.  Every piece is implemented here from scratch; nothing outside the
Python standard library is used.

The main loop is::

    while True:
        conflict = propagate()
        if conflict:
            if decision_level == 0: return UNSAT
            learnt, backjump_level, lbd = analyze(conflict)   # first-UIP
            backtrack(backjump_level)
            record(learnt)              # attaches it and emits a DRAT line
            assign(learnt[0], reason=learnt)
            decay_activities()
        else:
            if restart_due(): backtrack(0); continue
            if db_too_large(): reduce_db()
            lit = pick_branch_literal()  # VSIDS + saved phase
            if lit is None: return SAT
            new_decision_level(); assign(lit, reason=None)

Nontrivial pieces, in the order they matter for performance:

*Two-watched literals* (:meth:`Solver._propagate`).  A clause is only visited
when one of its two watched literals becomes false.  Watch lists are stored per
*literal*: ``watches[p]`` holds the clauses that watch ``~p``, so they are
exactly the clauses that need attention when ``p`` becomes true.  Each watcher
carries a *blocker* -- a second literal of the clause cached inline -- so that a
clause already satisfied by its blocker is skipped without dereferencing the
clause object at all.

*First-UIP learning* (:meth:`Solver._analyze`).  Resolve the conflicting clause
against the reasons of the current-level literals, newest first, until exactly
one literal of the current decision level remains.  That literal is the first
unique implication point; its negation becomes the asserting literal of the
learnt clause.  The clause is then minimised by *recursive self-subsumption*
(:meth:`Solver._lit_redundant`): a literal whose reason's other literals are
all already in the clause (transitively) is redundant and dropped.

*LBD / glue* (:meth:`Solver._lbd`).  The number of distinct decision levels in
a learnt clause predicts its future usefulness far better than its length.
Clauses with LBD <= 2 are kept forever; the rest are ranked by LBD for
deletion, and the LBD moving averages drive the restart policy.

*Restarts.*  Two policies.  Luby: the reluctant-doubling sequence, provably
optimal up to a log factor for heavy-tailed runtimes.  Glucose EMA: restart
when the recent LBD average is much worse than the long-run one.

Independently of either, a *blocking* rule defers a restart when the trail is
unusually deep (which suggests the current branch is close to a model).  It is
on by default and it applies to both policies, so the schedule that actually
runs under `restart="luby"` is Luby *with deferrals* -- the optimality result
above is a statement about the unblocked sequence, and does not carry over.
Set `block_restart=False` for the sequence the theorem describes.

Luby is the default, paired with target phases.  Glucose EMA was the default
for most of this project's life on the reasoning that unsatisfiable instances
dominate the hard cases -- and measurement killed that reasoning.  Over 203
public instances the pair Luby+target went from 1.62x behind kissat to 0.84x
ahead, and it improved *both* halves: satisfiable 3.25x -> 1.02x, and
unsatisfiable 0.84x -> 0.72x.  The refutation argument was not merely
outweighed, it was wrong on its own terms.
"""

from __future__ import annotations

import time
from typing import Iterable, Sequence

from dratify.cnf import CNF, Clause
from .heap import ActivityHeap
from dratify.lits import F, T, U, from_dimacs, to_dimacs

#: probSAT break-count weights, ``(0.9 + brk) ** -2.06``, as literals.
#:
#: Written out rather than computed so both engines use *identical bits*.
#: Python's ``**`` and Rust's ``powf`` each call their platform's ``pow``, and a
#: one-ULP disagreement would silently flip a comparison in the walk and break
#: the bit-exactness the two implementations are checked against.
WALK_WEIGHTS = (
    1.2423971044693904,
    0.2665431844564756,
    0.11154757268716438,
    0.06059083109242785,
    0.0378613482436238,
    0.02582526912626813,
    0.018705566831429692,
    0.0141542933420601,
    0.011072777835612904,
    0.00889183712824521,
    0.007292919406638117,
    0.006086578947728128,
    0.005154484010820045,
    0.004419666621745944,
    0.003830330838618274,
    0.0033505949060830035,
    0.0029549721254695433,
    0.0026249604007938013,
    0.00234686810854462,
    0.0021103897194995175,
    0.001907649796755619,
    0.001732547393265342,
    0.001580297694020363,
    0.0014471059328459816,
    0.0013299317216792165,
    0.0012263162579798836,
    0.0011342539574143936,
    0.0010520959317115543,
    0.000978476599632614,
    0.0009122573099164859,
    0.0008524826176723598,
    0.0007983460721352612,
    0.0007491632244617672,
)

__all__ = ["Solver", "Config", "Stats", "SAT", "UNSAT", "UNKNOWN"]

SAT = "SAT"
UNSAT = "UNSAT"
UNKNOWN = "UNKNOWN"


# --------------------------------------------------------------------------
# configuration and statistics
# --------------------------------------------------------------------------


class Config:
    """Tunable solver parameters.

    The clause-database and decision-heuristic defaults follow Glucose 4.  The
    search defaults no longer do: restarts are Luby, target phases are on, and
    probSAT rephasing runs -- each because it measured better here, not because
    Glucose does it.  See the module docstring and `docs/ALGORITHMS.md` §4.
    """

    __slots__ = (
        "var_decay",
        "var_decay_max",
        "cla_decay",
        "restart",
        "luby_base",
        "ccmin",
        "phase_saving",
        "init_phase",
        "target_phase",
        "target_reset",
        "walk_flips",
        "walk_interval",
        "walk_patience",
        "walk_min_conflicts",
        "first_reduce",
        "reduce_inc",
        "glue_keep",
        "block_restart",
        "rnd_freq",
        "rnd_seed",
        "verbosity",
    )

    def __init__(self, **kw) -> None:
        self.var_decay = 0.8  # ramps up to var_decay_max
        self.var_decay_max = 0.95
        self.cla_decay = 0.999
        self.restart = "luby"  # "glucose" | "luby" | "none"
        self.luby_base = 100
        self.ccmin = "deep"  # "deep" | "basic" | "none"
        self.phase_saving = True
        self.init_phase = False  # first-time polarity for a fresh variable
        # Branch on the assignment from the deepest conflict-free trail ever
        # reached, rather than on the most recently saved one. Saved phases
        # follow wherever the search just was, including into the region a
        # conflict just pushed it out of; the target follows the best place it
        # has ever been.
        #
        # On by default, with `restart="luby"`, because the pair was measured
        # at 1.62x -> 0.84x against kissat over the 203 public instances both
        # solvers decided within the budget. That was run before the corpus
        # grew to 344 (see CHANGELOG) and has not been repeated since. Neither
        # half is worth much alone (target alone 0.97, luby alone 0.75): a
        # target is only useful if the restart schedule leaves the search long
        # enough to reach it. See docs/ALGORITHMS.md.
        self.target_phase = True
        # Restarts after which the target is forgotten and re-learned. 0 keeps
        # the deepest trail ever seen, for the whole run -- which is CaDiCaL's
        # "best" rather than its "target", and goes stale: once the search has
        # moved region, the assignment being branched from is a memory of
        # somewhere it can no longer get to.
        self.target_reset = 0
        # Local-search rephasing (probSAT).  `walk_flips` is the flip budget per
        # invocation, 0 to disable; `walk_interval` is how many restarts apart
        # invocations are.
        #
        # CDCL is weak on satisfiable uniform-random instances and local search
        # is strong on exactly those, which is the measured gap against
        # `kissat --sat`.  The walk never decides anything: it proposes an
        # assignment, that assignment becomes the phases the search branches
        # from, and the search still has to find and verify a model itself.
        # So this is proof-neutral like every other phase mechanism here.
        self.walk_flips = 20_000
        self.walk_interval = 1
        # Consecutive walks that fail to reduce the best unsatisfied-clause
        # count before the walk gives up for the rest of the run.
        #
        # On a satisfiable instance probSAT keeps improving until it lands a
        # model. On an unsatisfiable one it plateaus almost at once and every
        # further flip is waste -- measured at 12% slower across uuf250 when
        # walking unconditionally. This is the cheap way to tell the two apart
        # without being told which you have.
        self.walk_patience = 3
        # Conflicts the CDCL search must spend before local search is allowed
        # to start.
        #
        # The walk is a specialised tool -- it is worth 34x on large random
        # satisfiable instances and a loss on everything else, because its
        # fixed cost dominates whenever the instance was going to be solved
        # quickly anyway. Measured against no walk: graph colouring 1.55x
        # slower, planning 1.68x, small random unsatisfiable 5.2x. Gating on
        # effort already spent asks "is CDCL losing?" rather than "does this
        # look like a random instance?", which is the question that generalises.
        self.walk_min_conflicts = 5000
        self.first_reduce = 2000
        self.reduce_inc = 300
        self.glue_keep = 2  # LBD <= glue_keep is never deleted
        self.block_restart = True
        self.rnd_freq = 0.0
        self.rnd_seed = 91648253
        self.verbosity = 0
        for k, v in kw.items():
            if k not in Config.__slots__:
                raise TypeError(f"unknown config option {k!r}")
            setattr(self, k, v)

    def as_dict(self) -> dict:
        return {k: getattr(self, k) for k in Config.__slots__}


class Stats:
    """Counters.  Cheap to maintain, invaluable for judging a heuristic."""

    __slots__ = (
        "decisions",
        "propagations",
        "conflicts",
        "learned",
        "learned_lits",
        "minimized_lits",
        "restarts",
        "blocked_restarts",
        "walks",
        "walk_flips",
        "reductions",
        "deleted",
        "simplifications",
        "removed_clauses",
        "removed_lits",
        "start_time",
        "solve_time",
        "max_trail",
    )

    def __init__(self) -> None:
        for k in Stats.__slots__:
            setattr(self, k, 0)
        self.start_time = time.perf_counter()
        self.solve_time = 0.0

    def as_dict(self) -> dict:
        return {k: getattr(self, k) for k in Stats.__slots__ if k != "start_time"}

    def report(self) -> str:
        d = self.as_dict()
        t = max(d["solve_time"], 1e-9)
        lines = [
            f"c conflicts    : {d['conflicts']:>12}  ({d['conflicts']/t:>10.0f} /sec)",
            f"c decisions    : {d['decisions']:>12}  ({d['decisions']/t:>10.0f} /sec)",
            f"c propagations : {d['propagations']:>12}  ({d['propagations']/t:>10.0f} /sec)",
            f"c learned      : {d['learned']:>12}  "
            f"(avg len {d['learned_lits']/max(d['learned'],1):.1f}, "
            f"{d['minimized_lits']} lits minimised away)",
            f"c restarts     : {d['restarts']:>12}  ({d['blocked_restarts']} blocked)",
            f"c db reductions: {d['reductions']:>12}  ({d['deleted']} clauses deleted)",
            f"c simplify     : {d['simplifications']:>12}  "
            f"({d['removed_clauses']} clauses, {d['removed_lits']} lits removed)",
            f"c cpu time     : {d['solve_time']:>12.3f} s",
        ]
        return "\n".join(lines)


# --------------------------------------------------------------------------
# restart schedules
# --------------------------------------------------------------------------


def luby(y: float, x: int) -> float:
    """The Luby reluctant-doubling sequence 1,1,2,1,1,2,4,... scaled by ``y``.

    Finds the finite subsequence containing index ``x`` and computes its value
    in O(log x) without materialising the sequence.
    """
    size = 1
    seq = 0
    while size < x + 1:
        seq += 1
        size = 2 * size + 1
    while size - 1 != x:
        size = (size - 1) >> 1
        seq -= 1
        x = x % size
    return y**seq


class _EMA:
    """Exponential moving average with bias correction for the warm-up phase."""

    __slots__ = ("value", "alpha", "beta", "wait", "period")

    def __init__(self, alpha: float) -> None:
        self.value = 0.0
        self.alpha = alpha
        self.beta = 1.0  # starts fast, decays to alpha (Biere's smoothing)
        self.wait = self.period = 0

    def update(self, x: float) -> None:
        self.value += self.beta * (x - self.value)
        if self.beta > self.alpha and self.wait == 0:
            self.beta *= 0.5
            self.period = 2 * self.period + 1
            self.wait = self.period
        elif self.wait:
            self.wait -= 1


# --------------------------------------------------------------------------
# the solver
# --------------------------------------------------------------------------


class Solver:
    """A conflict-driven clause-learning SAT solver.

    Typical use::

        s = Solver()
        a, b = s.new_var(), s.new_var()
        s.add_clause([mk_lit(a), mk_lit(b)])
        if s.solve():
            print(s.model)

    The solver is *incremental*: after a call to :meth:`solve` more clauses may
    be added and :meth:`solve` called again, optionally under assumptions.
    When solving under assumptions returns UNSAT, :attr:`conflict` holds the
    subset of assumptions responsible -- an unsatisfiable core.
    """

    def __init__(
        self,
        nvars: int = 0,
        proof=None,
        config: Config | None = None,
    ) -> None:
        self.cfg = config or Config()
        self.stats = Stats()
        self.proof = proof

        # -- assignment state
        self.nvars = 0
        self.val = bytearray()  # per literal: U / T / F
        self.level: list[int] = []  # per variable
        self.reason: list[Clause | None] = []
        self.trail: list[int] = []
        self.trail_lim: list[int] = []
        self.qhead = 0

        # -- clause database
        self.watches: list[list] = []
        self.clauses: list[Clause] = []
        self.learnts: list[Clause] = []

        # -- heuristics
        self.act: list[float] = []
        self.var_inc = 1.0
        self.cla_inc = 1.0
        self.order = ActivityHeap(self.act)
        self.polarity = bytearray()
        #: phases from the deepest conflict-free trail seen so far, and that
        #: depth. Only meaningful when cfg.target_phase is on.
        self._target = bytearray()
        self._target_size = 0
        self._walk_best = 1 << 30
        self._walk_stale = 0
        self.frozen = bytearray()  # variables excluded from decisions

        # -- scratch
        self.seen = bytearray()
        self._analyze_toclear: list[int] = []
        self._lbd_stamp: list[int] = []
        self._lbd_gen = 0

        # -- control
        self.ok = True
        self.assumptions: list[int] = []
        self.conflict: list[int] = []  # final core, in assumption polarity
        self.model: list[bool] = []
        self._rnd = self.cfg.rnd_seed

        # -- restart / reduce bookkeeping
        self._lbd_fast = _EMA(1.0 / 50)
        self._lbd_slow = _EMA(1.0 / 5000)
        self._trail_ema = _EMA(1.0 / 5000)
        self._next_reduce = self.cfg.first_reduce
        self._reduce_count = 0
        self._restart_index = 0
        self._conflicts_at_restart = 0
        self._simp_props = 0
        self._var_decay = self.cfg.var_decay

        for _ in range(nvars):
            self.new_var()

    # ----------------------------------------------------------------- vars

    def new_var(self, polarity: bool | None = None, decision: bool = True) -> int:
        """Allocate a fresh variable, returning its 0-based index."""
        v = self.nvars
        self.nvars += 1
        self.val.extend((U, U))
        self.level.append(0)
        self.reason.append(None)
        self.watches.append([])
        self.watches.append([])
        self.act.append(0.0)
        self._target.append(0)
        self.polarity.append(
            1 if (self.cfg.init_phase if polarity is None else polarity) else 0
        )
        self.frozen.append(0 if decision else 1)
        self.seen.append(0)
        self._lbd_stamp.append(0)
        self.order.grow(self.nvars)
        if decision:
            self.order.insert(v)
        return v

    def ensure_vars(self, n: int) -> None:
        while self.nvars < n:
            self.new_var()

    def set_decision(self, v: int, on: bool) -> None:
        self.frozen[v] = 0 if on else 1
        if on:
            self.order.insert(v)
        else:
            self.order.remove(v)

    # ------------------------------------------------------------- accessors

    def value(self, lit: int) -> int:
        return self.val[lit]

    def var_value(self, v: int) -> int:
        return self.val[v << 1]

    @property
    def decision_level(self) -> int:
        return len(self.trail_lim)

    def n_assigns(self) -> int:
        return len(self.trail)

    def _lit_level(self, lit: int) -> int:
        return self.level[lit >> 1]

    # ------------------------------------------------------------ clause add

    def add_clause(self, lits: Iterable[int]) -> bool:
        """Add a permanent clause.  Returns False when the formula became UNSAT.

        Must be called at decision level 0 (the caller may be mid-incremental
        use; we backtrack for them).  Literals are deduplicated, tautologies
        are dropped, and literals already false at level 0 are removed -- the
        latter is a strengthening step, so it is logged to the proof.
        """
        if not self.ok:
            return False
        if self.decision_level != 0:
            self._cancel_until(0)

        seen: set[int] = set()
        out: list[int] = []
        original = []
        for l in lits:
            original.append(l)
            if l >= len(self.val):
                self.ensure_vars((l >> 1) + 1)
            if l in seen:
                continue
            if (l ^ 1) in seen:
                return True  # tautology: nothing to add
            seen.add(l)
            v = self.val[l]
            if v == T and self.level[l >> 1] == 0:
                return True  # already satisfied at root
            if v == F and self.level[l >> 1] == 0:
                continue  # root-false literal: drop it
            out.append(l)

        if self.proof is not None and len(out) != len(seen):
            # We are adding a strengthened version of the user's clause.  It is
            # RUP (unit propagation on the root units derives it), so a plain
            # addition line is a valid DRAT step.
            self.proof.add(out)

        if not out:
            self.ok = False
            if self.proof is not None:
                self.proof.add([])
            return False
        if len(out) == 1:
            self._assign(out[0], None)
            if self._propagate() is not None:
                self.ok = False
                if self.proof is not None:
                    self.proof.add([])
                return False
            return True

        c = Clause(out, learnt=False)
        self.clauses.append(c)
        self._attach(c)
        return True

    def add_clause_dimacs(self, dimacs: Iterable[int]) -> bool:
        return self.add_clause(from_dimacs(d) for d in dimacs)

    def add_cnf(self, f: CNF) -> bool:
        """Load an entire :class:`~cdclkit.cnf.CNF`."""
        self.ensure_vars(f.nvars)
        for c in f.clauses:
            if not self.add_clause(c):
                return False
        return True

    # ----------------------------------------------------------- attach/detach

    def _attach(self, c: Clause) -> None:
        lits = c.lits
        self.watches[lits[0] ^ 1].append([c, lits[1]])
        self.watches[lits[1] ^ 1].append([c, lits[0]])

    def _detach(self, c: Clause) -> None:
        lits = c.lits
        for a, b in ((lits[0], lits[1]), (lits[1], lits[0])):
            ws = self.watches[a ^ 1]
            for i, w in enumerate(ws):
                if w[0] is c:
                    del ws[i]
                    break

    def _remove_clause(self, c: Clause, log: bool = True) -> None:
        self._detach(c)
        if log and self.proof is not None:
            self.proof.delete(c.lits)
        if self._locked(c):
            self.reason[c.lits[0] >> 1] = None
        c.deleted = True

    def _locked(self, c: Clause) -> bool:
        l0 = c.lits[0]
        return self.val[l0] == T and self.reason[l0 >> 1] is c

    # ------------------------------------------------------------- assignment

    def _assign(self, lit: int, reason: Clause | None) -> None:
        v = lit >> 1
        self.val[lit] = T
        self.val[lit ^ 1] = F
        self.level[v] = len(self.trail_lim)
        self.reason[v] = reason
        self.trail.append(lit)

    def _cancel_until(self, level: int) -> None:
        if len(self.trail_lim) <= level:
            return
        bound = self.trail_lim[level]
        trail = self.trail
        val = self.val
        order = self.order
        save = self.cfg.phase_saving
        for i in range(len(trail) - 1, bound - 1, -1):
            lit = trail[i]
            v = lit >> 1
            val[lit] = U
            val[lit ^ 1] = U
            self.reason[v] = None
            if save:
                self.polarity[v] = 0 if (lit & 1) else 1
            if not self.frozen[v]:
                order.insert(v)
        del trail[bound:]
        del self.trail_lim[level:]
        self.qhead = len(trail)

    # ------------------------------------------------------------ propagation

    def _propagate(self) -> Clause | None:
        """Unit-propagate to fixpoint; return a conflicting clause or None."""
        val = self.val
        watches = self.watches
        trail = self.trail
        confl: Clause | None = None
        props = 0

        while self.qhead < len(trail):
            p = trail[self.qhead]
            self.qhead += 1
            props += 1
            false_lit = p ^ 1
            ws = watches[p]
            i = j = 0
            n = len(ws)
            while i < n:
                w = ws[i]
                blocker = w[1]
                if val[blocker] == T:
                    ws[j] = w
                    i += 1
                    j += 1
                    continue
                c = w[0]
                lits = c.lits
                # normalise: the false literal sits at index 1
                if lits[0] == false_lit:
                    lits[0] = lits[1]
                    lits[1] = false_lit
                first = lits[0]
                if first != blocker and val[first] == T:
                    w[1] = first
                    ws[j] = w
                    i += 1
                    j += 1
                    continue
                # look for a replacement watch among lits[2:]
                found = False
                for k in range(2, len(lits)):
                    lk = lits[k]
                    if val[lk] != F:
                        lits[1] = lk
                        lits[k] = false_lit
                        watches[lk ^ 1].append([c, first])
                        found = True
                        break
                if found:
                    i += 1
                    continue
                # no replacement: the clause is unit or conflicting
                ws[j] = w
                i += 1
                j += 1
                if val[first] == F:
                    confl = c
                    self.qhead = len(trail)
                    while i < n:
                        ws[j] = ws[i]
                        i += 1
                        j += 1
                    break
                self._assign(first, c)
            del ws[j:]
            if confl is not None:
                break

        self.stats.propagations += props
        if len(trail) > self.stats.max_trail:
            self.stats.max_trail = len(trail)
        return confl

    # -------------------------------------------------------------- activity

    def _bump_var(self, v: int) -> None:
        act = self.act
        a = act[v] + self.var_inc
        act[v] = a
        if a > 1e100:
            for i in range(self.nvars):
                act[i] *= 1e-100
            self.var_inc *= 1e-100
        self.order.bump(v)

    def _decay_var(self) -> None:
        self.var_inc /= self._var_decay

    def _bump_clause(self, c: Clause) -> None:
        c.act += self.cla_inc
        if c.act > 1e20:
            for d in self.learnts:
                d.act *= 1e-20
            self.cla_inc *= 1e-20

    def _decay_clause(self) -> None:
        self.cla_inc /= self.cfg.cla_decay

    # ---------------------------------------------------------------- analyze

    def _abstract_level(self, v: int) -> int:
        return 1 << (self.level[v] & 31)

    def _lbd(self, lits: Sequence[int]) -> int:
        """Literal Block Distance: number of distinct decision levels."""
        self._lbd_gen += 1
        gen = self._lbd_gen
        stamp = self._lbd_stamp
        level = self.level
        n = 0
        for l in lits:
            lv = level[l >> 1]
            if stamp[lv] != gen:
                stamp[lv] = gen
                n += 1
        return n

    def _analyze(self, confl: Clause) -> tuple[list[int], int, int]:
        """First-UIP conflict analysis.

        Returns ``(learnt, backjump_level, lbd)`` where ``learnt[0]`` is the
        asserting literal and ``learnt[1]`` (if any) sits at the backjump
        level, so the clause propagates immediately after backtracking.
        """
        seen = self.seen
        level = self.level
        trail = self.trail
        cur = len(self.trail_lim)

        learnt: list[int] = [0]  # slot 0 reserved for the asserting literal
        counter = 0
        p = -1
        index = len(trail) - 1

        while True:
            c = confl
            if c.learnt:
                self._bump_clause(c)
                if c.lbd > 2:
                    # Glucose's on-the-fly LBD update: a clause whose LBD drops
                    # is more useful than its recorded score suggests.
                    nl = self._lbd(c.lits)
                    if nl < c.lbd:
                        c.lbd = nl
            lits = c.lits
            for k in range(0 if p < 0 else 1, len(lits)):
                q = lits[k]
                v = q >> 1
                if not seen[v] and level[v] > 0:
                    seen[v] = 1
                    self._bump_var(v)
                    if level[v] >= cur:
                        counter += 1
                    else:
                        learnt.append(q)
            while not seen[trail[index] >> 1]:
                index -= 1
            p = trail[index]
            index -= 1
            v = p >> 1
            confl = self.reason[v]
            seen[v] = 0
            counter -= 1
            if counter <= 0:
                break

        learnt[0] = p ^ 1
        raw_len = len(learnt)

        # -- clause minimisation ------------------------------------------
        self._analyze_toclear = learnt[:]
        mode = self.cfg.ccmin
        if mode == "deep":
            abstract = 0
            for l in learnt[1:]:
                abstract |= self._abstract_level(l >> 1)
            keep = [learnt[0]]
            for l in learnt[1:]:
                if self.reason[l >> 1] is None or not self._lit_redundant(l, abstract):
                    keep.append(l)
            learnt = keep
        elif mode == "basic":
            keep = [learnt[0]]
            for l in learnt[1:]:
                r = self.reason[l >> 1]
                if r is None:
                    keep.append(l)
                    continue
                for q in r.lits[1:]:
                    if not seen[q >> 1] and level[q >> 1] > 0:
                        keep.append(l)
                        break
            learnt = keep

        self.stats.minimized_lits += raw_len - len(learnt)

        # -- backjump level -------------------------------------------------
        if len(learnt) == 1:
            bt = 0
        else:
            best = 1
            best_lvl = level[learnt[1] >> 1]
            for i in range(2, len(learnt)):
                lv = level[learnt[i] >> 1]
                if lv > best_lvl:
                    best_lvl = lv
                    best = i
            learnt[1], learnt[best] = learnt[best], learnt[1]
            bt = best_lvl

        lbd = self._lbd(learnt)
        for l in self._analyze_toclear:
            seen[l >> 1] = 0
        self._analyze_toclear = []
        return learnt, bt, lbd

    def _lit_redundant(self, p: int, abstract_levels: int) -> bool:
        """True when ``p`` is implied by the other literals of the learnt clause.

        Depth-first walk of the implication graph backwards from ``p``.  The
        walk succeeds when every reachable antecedent literal is either already
        in the clause (``seen``) or root-level.  ``abstract_levels`` is a
        64-bit-style bloom filter over decision levels: a literal whose level
        is not represented in the learnt clause can never be redundant, and the
        filter rejects it without touching its reason clause.
        """
        seen = self.seen
        level = self.level
        reason = self.reason
        stack = [p]
        top = len(self._analyze_toclear)
        while stack:
            q = stack.pop()
            c = reason[q >> 1]
            if c is None:  # decision literal: not redundant
                for l in self._analyze_toclear[top:]:
                    seen[l >> 1] = 0
                del self._analyze_toclear[top:]
                return False
            for l in c.lits[1:]:
                v = l >> 1
                if seen[v] or level[v] == 0:
                    continue
                if reason[v] is not None and (self._abstract_level(v) & abstract_levels):
                    seen[v] = 1
                    stack.append(l)
                    self._analyze_toclear.append(l)
                else:
                    for m in self._analyze_toclear[top:]:
                        seen[m >> 1] = 0
                    del self._analyze_toclear[top:]
                    return False
        return True

    def _analyze_final(self, p: int) -> list[int]:
        """Build the assumption core explaining why literal ``p`` cannot hold.

        Walks the trail backwards from the top, collecting the decision (i.e.
        assumption) literals that reach ``p``.  The result is returned in
        *assumption polarity*: the literals the caller passed in.
        """
        out = [p]
        if not self.trail_lim:
            # The assumption is contradicted at root level, so it alone is the
            # core.  Note the flip: `out` is accumulated in conflict-clause
            # polarity (negated assumptions) and converted on the way out, so
            # this early return has to convert too.
            return [p ^ 1]
        seen = self.seen
        seen[p >> 1] = 1
        for i in range(len(self.trail) - 1, self.trail_lim[0] - 1, -1):
            v = self.trail[i] >> 1
            if not seen[v]:
                continue
            r = self.reason[v]
            if r is None:
                if self.level[v] > 0:
                    out.append(self.trail[i] ^ 1)
            else:
                for l in r.lits[1:]:
                    if self.level[l >> 1] > 0:
                        seen[l >> 1] = 1
            seen[v] = 0
        seen[p >> 1] = 0
        return [l ^ 1 for l in out]

    # ------------------------------------------------------------- db control

    def _record(self, learnt: list[int], lbd: int) -> Clause | None:
        """Attach a learnt clause and log it to the proof."""
        self.stats.learned += 1
        self.stats.learned_lits += len(learnt)
        if self.proof is not None:
            self.proof.add(learnt)
        if len(learnt) == 1:
            return None
        c = Clause(learnt, learnt=True, lbd=lbd)
        c.act = self.cla_inc
        self.learnts.append(c)
        self._attach(c)
        return c

    def _reduce_db(self) -> None:
        """Delete the least useful half of the learnt clauses.

        Ranking is LBD first (lower is better), clause activity second.  Glue
        clauses (LBD <= ``glue_keep``), binaries and clauses that are currently
        the reason for an assignment are exempt.
        """
        self.stats.reductions += 1
        learnts = self.learnts
        keep_lbd = self.cfg.glue_keep
        candidates = [
            c
            for c in learnts
            if not c.deleted and c.lbd > keep_lbd and len(c.lits) > 2 and not self._locked(c)
        ]
        candidates.sort(key=lambda c: (-c.lbd, c.act))
        limit = len(candidates) // 2
        removed = 0
        for c in candidates[:limit]:
            self._remove_clause(c)
            removed += 1
        self.learnts = [c for c in learnts if not c.deleted]
        self.stats.deleted += removed

    def _simplify(self) -> bool:
        """Root-level simplification: drop satisfied clauses, shrink the rest.

        Only worth running when new root-level units exist, hence the
        propagation counter guard.  Every strengthened clause is emitted to the
        proof as an addition followed by the deletion of the original, which is
        exactly what a DRAT checker expects.
        """
        assert self.decision_level == 0
        if self._propagate() is not None:
            self.ok = False
            if self.proof is not None:
                self.proof.add([])
            return False
        self.stats.simplifications += 1
        val = self.val
        for lst in (self.learnts, self.clauses):
            out = []
            for c in lst:
                if c.deleted:
                    continue
                if self._locked(c):
                    out.append(c)
                    continue
                sat = False
                nfalse = 0
                for l in c.lits:
                    if val[l] == T and self.level[l >> 1] == 0:
                        sat = True
                        break
                    if val[l] == F and self.level[l >> 1] == 0:
                        nfalse += 1
                if sat:
                    self._remove_clause(c)
                    self.stats.removed_clauses += 1
                    continue
                if nfalse:
                    survivors = [
                        l for l in c.lits if not (val[l] == F and self.level[l >> 1] == 0)
                    ]
                    self.stats.removed_lits += nfalse
                    if self.proof is not None:
                        self.proof.add(survivors)
                    self._detach(c)
                    if self.proof is not None:
                        self.proof.delete(c.lits)
                    if len(survivors) == 1:
                        c.deleted = True
                        if val[survivors[0]] == U:
                            self._assign(survivors[0], None)
                        elif val[survivors[0]] == F:
                            self.ok = False
                            if self.proof is not None:
                                self.proof.add([])
                            return False
                        continue
                    c.lits = survivors
                    self._attach(c)
                out.append(c)
            lst[:] = out
        if self._propagate() is not None:
            self.ok = False
            if self.proof is not None:
                self.proof.add([])
            return False
        self._simp_props = self.stats.propagations
        return True

    # ----------------------------------------------------------- decisions

    def _rand(self) -> float:
        # xorshift32, so that runs are reproducible across platforms and
        # independent of the global `random` module's state.
        x = self._rnd
        x ^= (x << 13) & 0xFFFFFFFF
        x ^= x >> 17
        x ^= (x << 5) & 0xFFFFFFFF
        self._rnd = x & 0xFFFFFFFF
        return self._rnd / 4294967296.0

    def _pick_branch_lit(self) -> int:
        """Return a decision literal, or -1 when every variable is assigned."""
        order = self.order
        val = self.val
        # `phase` is whichever array the configuration says to branch from.
        # Bound once rather than tested per decision: this is the hottest loop
        # in the solver after propagation.
        phase = self._target if self.cfg.target_phase else self.polarity
        if self.cfg.rnd_freq > 0.0 and self._rand() < self.cfg.rnd_freq and len(order):
            v = order.heap[int(self._rand() * len(order))]
            if val[v << 1] == U and not self.frozen[v]:
                self.stats.decisions += 1
                return (v << 1) | (0 if phase[v] else 1)
        while True:
            if order.empty():
                return -1
            v = order.pop_max()
            if val[v << 1] == U and not self.frozen[v]:
                self.stats.decisions += 1
                return (v << 1) | (0 if phase[v] else 1)


    # ------------------------------------------------------------ local search

    def _walk_occurrences(self):
        """Occurrence lists over the *original* clauses, rebuilt every call.

        Deliberately not cached. Root simplification deletes and strengthens
        original clauses while the search runs, so a cached index goes stale --
        and it went stale *differently* in the two engines, which showed up as
        the walk diverging on exactly the instances that run long enough to
        simplify. Rebuilding is O(total literals), which is nothing beside the
        thousands of flips that follow it.

        Learnt clauses are excluded on purpose. They are implied by the
        originals, so satisfying the originals satisfies them too, and
        including them would make every flip cost more while the clause set
        churns underneath a cached index.
        """
        clauses = [c.lits for c in self.clauses if not c.deleted and len(c.lits) > 1]
        occ: list[list[int]] = [[] for _ in range(2 * self.nvars)]
        for i, lits in enumerate(clauses):
            for l in lits:
                occ[l].append(i)
        return clauses, occ

    def _walk(self, max_flips: int) -> None:
        """probSAT over the original clauses; the best assignment becomes phases.

        Balint and Schoening's probSAT: repeatedly pick an unsatisfied clause at
        random and flip one of its variables, choosing the variable with
        probability falling off polynomially in its *break count* -- how many
        currently-satisfied clauses the flip would break. No tabu list, no
        greedy tie-breaking, no restarts of its own; the whole heuristic is that
        one probability.

        Deterministic: it draws from the solver's own xorshift32, so a run is
        reproducible and the Rust port reproduces it flip for flip.
        """
        clauses, occ = self._walk_occurrences()
        if not clauses:
            return

        # start from the phases the search would otherwise branch on
        src = self._target if self.cfg.target_phase else self.polarity
        assign = bytearray(src)
        # variables fixed at level 0 are not the walk's to move
        val = self.val
        for v in range(self.nvars):
            if val[v << 1] == T and self.level[v] == 0:
                assign[v] = 1
            elif val[(v << 1) ^ 1] == T and self.level[v] == 0:
                assign[v] = 0

        def sat_count(lits):
            return sum(1 for l in lits if assign[l >> 1] == (0 if (l & 1) else 1))

        ntrue = [sat_count(lits) for lits in clauses]
        unsat = [i for i, n in enumerate(ntrue) if n == 0]
        where = {c: k for k, c in enumerate(unsat)}

        best_unsat = len(unsat)
        best = bytearray(assign)

        for _ in range(max_flips):
            if not unsat:
                break
            lits = clauses[unsat[int(self._rand() * len(unsat))]]

            # break count: clauses this flip would take from 1 true literal to 0
            weights, total = [], 0.0
            for l in lits:
                v = l >> 1
                cur = (v << 1) | (0 if assign[v] else 1)   # literal true now
                brk = sum(1 for ci in occ[cur] if ntrue[ci] == 1)
                w = WALK_WEIGHTS[brk if brk < len(WALK_WEIGHTS) else -1]
                weights.append((v, w))
                total += w

            r = self._rand() * total
            flip = weights[-1][0]
            acc = 0.0
            for v, w in weights:
                acc += w
                if r <= acc:
                    flip = v
                    break

            # apply the flip and repair the counts
            now_true = (flip << 1) | (0 if assign[flip] else 1)
            assign[flip] ^= 1
            new_true = (flip << 1) | (0 if assign[flip] else 1)
            for ci in occ[now_true]:
                ntrue[ci] -= 1
                if ntrue[ci] == 0:
                    where[ci] = len(unsat)
                    unsat.append(ci)
            for ci in occ[new_true]:
                if ntrue[ci] == 0:
                    k = where.pop(ci)
                    last = unsat.pop()
                    if k < len(unsat):
                        unsat[k] = last
                        where[last] = k
                ntrue[ci] += 1

            if len(unsat) < best_unsat:
                best_unsat = len(unsat)
                best = bytearray(assign)

        self.stats.walks += 1
        self.stats.walk_flips += max_flips
        if best_unsat < self._walk_best:
            self._walk_best = best_unsat
            self._walk_stale = 0
        else:
            self._walk_stale += 1
        # the payoff: branch from what the walk found
        self._target[:] = best
        self.polarity[:] = best
        self._target_size = 0   # the target now describes the walk, not a trail

    # -------------------------------------------------------------- restarts

    def _restart_due(self) -> bool:
        mode = self.cfg.restart
        if mode == "none":
            return False
        if mode == "luby":
            budget = self.cfg.luby_base * luby(2.0, self._restart_index)
            return self.stats.conflicts - self._conflicts_at_restart >= budget
        # Glucose: restart when the recent LBD average is 25% worse than the
        # long-run average, after a minimum window.
        if self.stats.conflicts - self._conflicts_at_restart < 50:
            return False
        return self._lbd_fast.value * 0.8 > self._lbd_slow.value

    def _block_restart(self) -> bool:
        """Suppress a restart when the trail is much deeper than usual."""
        if not self.cfg.block_restart:
            return False
        if self.stats.conflicts < 10000:
            return False
        return len(self.trail) > 1.4 * self._trail_ema.value

    # ----------------------------------------------------------------- search

    def _search(self, max_conflicts: int | None,
                deadline: float | None = None) -> str:
        """`deadline` is a `time.perf_counter()` value; None means unbounded.

        A benchmark harness has to bound its own solver the way it bounds the
        competitors. Ours did not: external solvers ran as subprocesses with a
        timeout while cdclkit ran in-process with none, so a SATLIB `par32`
        instance -- 3176 variables, exponential for CDCL without XOR reasoning,
        and one kissat also fails to solve -- ran for 77 minutes while kissat
        would have been killed at 120 seconds.

        Checked every 256 conflicts, which is far below the cost of a conflict
        and keeps `perf_counter` out of the hot path. Leaving it None changes
        nothing, so determinism and the bit-exactness tests are unaffected.
        """
        conflicts = 0
        while True:
            confl = self._propagate()
            if confl is not None:
                self.stats.conflicts += 1
                conflicts += 1
                if self.decision_level == 0:
                    if self.proof is not None:
                        self.proof.add([])
                    self.ok = False
                    return UNSAT
                learnt, bt, lbd = self._analyze(confl)
                self._lbd_fast.update(lbd)
                self._lbd_slow.update(lbd)
                self._trail_ema.update(len(self.trail))
                if self._block_restart():
                    self.stats.blocked_restarts += 1
                    self._conflicts_at_restart = self.stats.conflicts
                self._cancel_until(bt)
                c = self._record(learnt, lbd)
                self._assign(learnt[0], c)
                self._decay_var()
                self._decay_clause()
                if self._var_decay < self.cfg.var_decay_max:
                    self._var_decay = min(self._var_decay + 0.01, self.cfg.var_decay_max)
                if self.stats.conflicts >= self._next_reduce:
                    self._reduce_count += 1
                    self._next_reduce = (
                        self.cfg.first_reduce
                        + self.cfg.reduce_inc * self._reduce_count * self._reduce_count
                    )
                    self._reduce_db()
            else:
                # A new deepest conflict-free trail: remember the assignment
                # that reached it. Copying costs O(|trail|), but only on a
                # strict improvement, and improvements become rare quickly.
                if self.cfg.target_phase and len(self.trail) > self._target_size:
                    self._target_size = len(self.trail)
                    target = self._target
                    for t in self.trail:
                        target[t >> 1] = 0 if (t & 1) else 1

                if max_conflicts is not None and conflicts >= max_conflicts:
                    self._cancel_until(len(self.assumptions_applied))
                    return UNKNOWN
                if (deadline is not None and (conflicts & 255) == 0
                        and time.perf_counter() >= deadline):
                    self._cancel_until(len(self.assumptions_applied))
                    return UNKNOWN
                if self._restart_due():
                    self.stats.restarts += 1
                    self._restart_index += 1
                    self._conflicts_at_restart = self.stats.conflicts
                    if (self.cfg.target_reset
                            and self.stats.restarts % self.cfg.target_reset == 0):
                        self._target_size = 0
                    if (self.cfg.walk_flips
                            and self.stats.conflicts >= self.cfg.walk_min_conflicts
                            and self._walk_stale < self.cfg.walk_patience
                            and self.stats.restarts % self.cfg.walk_interval == 0):
                        self._cancel_until(0)
                        self._walk(self.cfg.walk_flips)
                    self._cancel_until(0)
                    continue
                if self.decision_level == 0 and self.stats.propagations > self._simp_props:
                    if not self._simplify():
                        return UNSAT

                # -- assumptions come before free decisions
                lit = -1
                while self.decision_level < len(self.assumptions):
                    a = self.assumptions[self.decision_level]
                    v = self.val[a]
                    if v == T:
                        self.trail_lim.append(len(self.trail))  # dummy level
                    elif v == F:
                        self.conflict = self._analyze_final(a ^ 1)
                        return UNSAT
                    else:
                        lit = a
                        break
                if lit == -1:
                    lit = self._pick_branch_lit()
                    if lit == -1:
                        self.model = [self.val[v << 1] == T for v in range(self.nvars)]
                        return SAT
                self.trail_lim.append(len(self.trail))
                self._assign(lit, None)

    @property
    def assumptions_applied(self) -> list[int]:
        return self.assumptions

    # ------------------------------------------------------------------ API

    def solve(
        self,
        assumptions: Sequence[int] = (),
        max_conflicts: int | None = None,
        deadline: float | None = None,
    ) -> bool | None:
        """Solve under ``assumptions``.

        Returns True (satisfiable, :attr:`model` set), False (unsatisfiable,
        :attr:`conflict` set when assumptions were used) or None when a
        conflict budget was exhausted.
        """
        t0 = time.perf_counter()
        self.model = []
        self.conflict = []
        self.assumptions = list(assumptions)
        try:
            if not self.ok:
                return False
            self._cancel_until(0)
            status = self._search(max_conflicts, deadline)
            if status == SAT:
                return True
            if status == UNSAT:
                return False
            return None
        finally:
            self._cancel_until(0)
            self.assumptions = []
            self.stats.solve_time += time.perf_counter() - t0

    def solve_dimacs_assumptions(self, dimacs: Sequence[int]) -> bool | None:
        return self.solve([from_dimacs(d) for d in dimacs])

    def model_dimacs(self) -> list[int]:
        return [(v + 1) if b else -(v + 1) for v, b in enumerate(self.model)]

    def core_dimacs(self) -> list[int]:
        return [to_dimacs(l) for l in self.conflict]

    # ------------------------------------------------------- model enumeration

    def enumerate_models(self, projection: Sequence[int] | None = None, limit: int = 0):
        """Yield models, blocking each one as it is produced.

        ``projection`` restricts the blocking clause (and therefore the notion
        of distinctness) to a subset of variables, which is how you count
        solutions of an encoded problem without also counting the different
        internal states of its Tseitin variables.

        Mutates the clause database: each yielded model adds a blocking clause,
        so the solver is left strictly stronger than it started.
        """
        vars_ = list(range(self.nvars)) if projection is None else list(projection)
        n = 0
        while self.solve():
            model = self.model
            yield list(model)
            n += 1
            if limit and n >= limit:
                return
            block = [(v << 1) | (1 if model[v] else 0) for v in vars_]
            if not block or not self.add_clause(block):
                return

    # ------------------------------------------------------------- diagnostics

    def check_watch_invariant(self) -> list[str]:
        """Verify the two-watched-literal bookkeeping.  Test-suite only."""
        errs: list[str] = []
        counted: dict[int, int] = {}
        for p, ws in enumerate(self.watches):
            for c, blocker in ws:
                if c.deleted:
                    errs.append(f"deleted clause still watched by {p}")
                if (p ^ 1) not in (c.lits[0], c.lits[1]):
                    errs.append(f"clause {c} in watches[{p}] but does not watch {p^1}")
                if blocker not in c.lits:
                    errs.append(f"blocker {blocker} not in {c}")
                counted[id(c)] = counted.get(id(c), 0) + 1
        for c in self.clauses + self.learnts:
            if c.deleted:
                continue
            if counted.get(id(c), 0) != 2:
                errs.append(f"clause {c} has {counted.get(id(c),0)} watchers, want 2")
        return errs

    def check_trail_invariant(self) -> list[str]:
        errs = []
        for i, lit in enumerate(self.trail):
            if self.val[lit] != T:
                errs.append(f"trail literal {lit} not true")
            lvl = self.level[lit >> 1]
            if lvl > 0 and self.trail_lim[lvl - 1] > i:
                errs.append(f"trail literal {lit} at position {i} claims level {lvl}")
        return errs
