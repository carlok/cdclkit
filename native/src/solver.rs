// SPDX-License-Identifier: Apache-2.0
// Copyright (c) 2026 Carlo Perassi. Licensed under the Apache License 2.0.
//! Native CDCL search core.
//!
//! Sprint 2 of `PLAN.md`. A faithful port of `cdclkit/solver.py`: two-watched
//! literals with blockers, first-UIP conflict analysis with recursive
//! minimisation, EVSIDS with a binary heap, phase saving, LBD, Glucose EMA and
//! Luby restarts, and LBD-ranked clause database reduction.
//!
//! # Why faithful rather than better
//!
//! The plan's Tier 2 criterion is that this produces **identical conflict
//! counts** to the Python solver while the port is still intentionally
//! faithful. That is a bit-exact comparison, and it catches the class of bug
//! that verdict agreement hides behind luck -- a mis-ordered watch list, a
//! different tie-break in the heap, an off-by-one in an LBD. So every
//! heuristic here reproduces the Python one exactly, including the parts a
//! from-scratch implementation would do differently:
//!
//! * watch lists are compacted in place preserving relative order, because
//!   watch order determines propagation order and therefore which conflict is
//!   found first;
//! * the activity heap breaks ties by lower variable index;
//! * `f64` arithmetic mirrors Python's float operations in the same order
//!   (both are IEEE-754 doubles, so this is reproducible);
//! * the EMA bias correction, the quadratic reduce interval and the restart
//!   thresholds are copied rather than reinvented.
//!
//! The performance-motivated redesigns in `PLAN.md` §7 (specialised binary
//! clauses, `u64`-packed watches, arena compaction) come *after* this is
//! verified, and each one retires a baseline entry deliberately.
//!
//! # Borrowing
//!
//! The clause arena is one `Vec<u32>` and watch lists are `Vec<Watch>`, so the
//! propagation loop wants to read a watch list while mutating clause literals
//! and pushing to a *different* watch list. Rather than reach for unsafe, the
//! loop takes the watch list out with `std::mem::take`, works on it, and puts
//! it back. One pointer swap per propagated literal, and the borrow checker
//! stays satisfied.

use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::Arc;

use crate::{neg, var_of, Lit};

pub const U: u8 = 0;
pub const T: u8 = 1;
pub const F: u8 = 2;

pub const UNDEF: i32 = -1;

/// probSAT break-count weights, `(0.9 + brk) ** -2.06`, as literals.
///
/// Written out rather than computed so both engines use *identical bits*.
/// Python's `**` and Rust's `powf` each call their platform's `pow`, and a
/// one-ULP disagreement would silently flip a comparison inside the walk and
/// break the bit-exactness the two implementations are checked against. These
/// literals are generated from the Python side and must match
/// `cdclkit.solver.WALK_WEIGHTS` exactly.
pub const WALK_WEIGHTS: [f64; 33] = [
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
];

// ---------------------------------------------------------------------------
// configuration
// ---------------------------------------------------------------------------

#[derive(Clone, Debug)]
pub struct Config {
    pub var_decay: f64,
    pub var_decay_max: f64,
    pub cla_decay: f64,
    pub restart: RestartPolicy,
    pub luby_base: f64,
    pub ccmin: CcMin,
    pub phase_saving: bool,
    pub init_phase: bool,
    /// Branch on the assignment from the deepest conflict-free trail ever
    /// reached, rather than the most recently saved one. Mirrors
    /// `Config.target_phase` in cdclkit/solver.py; the two engines must agree
    /// bit-for-bit, so this is not an independent knob.
    pub target_phase: bool,
    /// Restarts after which the target is forgotten and re-learned; 0 keeps it
    /// for the whole run. Mirrors `Config.target_reset` in cdclkit/solver.py.
    pub target_reset: u64,
    /// Flip budget per local-search invocation; 0 disables it.
    pub walk_flips: u64,
    /// Restarts between invocations.
    pub walk_interval: u64,
    /// Consecutive non-improving walks before the walk gives up for the run.
    /// Mirrors `Config.walk_patience` in cdclkit/solver.py.
    pub walk_patience: u64,
    /// Conflicts the search must spend before local search may start.
    /// Mirrors `Config.walk_min_conflicts` in cdclkit/solver.py.
    pub walk_min_conflicts: u64,
    pub first_reduce: u64,
    pub reduce_inc: u64,
    pub glue_keep: u32,
    /// Probability of taking a random decision instead of the highest-activity
    /// one. Zero by default, and the zero is load-bearing: `pick_branch_lit`
    /// tests it *before* drawing, so a zero frequency never advances the PRNG
    /// and both engines consume identical random streams.
    pub rnd_freq: f64,
    /// Seed for the xorshift32 stream. The portfolio varies this per worker so
    /// that duplicated recipes still explore differently.
    pub rnd_seed: u32,
    pub block_restart: bool,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum RestartPolicy {
    Glucose,
    Luby,
    None,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum CcMin {
    Deep,
    Basic,
    None,
}

impl Default for Config {
    fn default() -> Self {
        Self {
            var_decay: 0.8,
            var_decay_max: 0.95,
            cla_decay: 0.999,
            restart: RestartPolicy::Luby,
            luby_base: 100.0,
            ccmin: CcMin::Deep,
            phase_saving: true,
            init_phase: false,
            target_phase: true,
            target_reset: 0,
            walk_flips: 20_000,
            walk_interval: 1,
            walk_patience: 3,
            walk_min_conflicts: 5000,
            first_reduce: 2000,
            reduce_inc: 300,
            glue_keep: 2,
            block_restart: true,
            rnd_freq: 0.0,
            rnd_seed: 91_648_253,
        }
    }
}

#[derive(Default, Clone, Debug)]
pub struct Stats {
    pub decisions: u64,
    pub propagations: u64,
    pub conflicts: u64,
    pub learned: u64,
    pub learned_lits: u64,
    pub minimized_lits: u64,
    pub restarts: u64,
    pub blocked_restarts: u64,
    pub reductions: u64,
    pub deleted: u64,
    pub max_trail: usize,
}

// ---------------------------------------------------------------------------
// restart helpers
// ---------------------------------------------------------------------------

/// Luby's reluctant-doubling sequence, scaled by `y`.  Mirrors `solver.luby`.
pub fn luby(y: f64, mut x: u64) -> f64 {
    let mut size: u64 = 1;
    let mut seq: u32 = 0;
    while size < x + 1 {
        seq += 1;
        size = 2 * size + 1;
    }
    while size - 1 != x {
        size = (size - 1) >> 1;
        seq -= 1;
        x %= size;
    }
    y.powi(seq as i32)
}

/// Exponential moving average with the same bias correction as the Python
/// `_EMA`: the smoothing factor starts at 1 and halves on a schedule until it
/// reaches alpha, so the average is usable immediately instead of crawling
/// away from zero for thousands of conflicts.
#[derive(Clone, Debug)]
struct Ema {
    value: f64,
    alpha: f64,
    beta: f64,
    wait: u64,
    period: u64,
}

impl Ema {
    fn new(alpha: f64) -> Self {
        Self { value: 0.0, alpha, beta: 1.0, wait: 0, period: 0 }
    }

    fn update(&mut self, x: f64) {
        self.value += self.beta * (x - self.value);
        if self.beta > self.alpha && self.wait == 0 {
            self.beta *= 0.5;
            self.period = 2 * self.period + 1;
            self.wait = self.period;
        } else if self.wait > 0 {
            self.wait -= 1;
        }
    }
}

// ---------------------------------------------------------------------------
// clause storage
// ---------------------------------------------------------------------------

#[derive(Clone, Debug)]
struct ClauseHeader {
    offset: u32,
    len: u32,
    learnt: bool,
    deleted: bool,
    lbd: u32,
    act: f64,
}

#[derive(Clone, Copy)]
struct Watch {
    clause: u32,
    blocker: Lit,
}

// ---------------------------------------------------------------------------
// activity heap
// ---------------------------------------------------------------------------

/// Indexed binary max-heap over an external activity array, ties broken by
/// lower variable index -- identical ordering to `cdclkit/heap.py`, which is
/// what makes decision sequences comparable between the two implementations.
struct Heap {
    heap: Vec<u32>,
    pos: Vec<i32>,
}

impl Heap {
    fn new() -> Self {
        Self { heap: Vec::new(), pos: Vec::new() }
    }

    fn grow(&mut self, n: usize) {
        while self.pos.len() < n {
            self.pos.push(-1);
        }
    }

    #[inline]
    fn better(act: &[f64], a: u32, b: u32) -> bool {
        let (aa, ab) = (act[a as usize], act[b as usize]);
        if aa != ab {
            aa > ab
        } else {
            a < b
        }
    }

    fn up(&mut self, act: &[f64], mut i: usize) {
        let v = self.heap[i];
        while i > 0 {
            let parent = (i - 1) >> 1;
            let pv = self.heap[parent];
            if !Self::better(act, v, pv) {
                break;
            }
            self.heap[i] = pv;
            self.pos[pv as usize] = i as i32;
            i = parent;
        }
        self.heap[i] = v;
        self.pos[v as usize] = i as i32;
    }

    fn down(&mut self, act: &[f64], mut i: usize) {
        let n = self.heap.len();
        let v = self.heap[i];
        loop {
            let left = 2 * i + 1;
            if left >= n {
                break;
            }
            let right = left + 1;
            let mut child = left;
            if right < n && Self::better(act, self.heap[right], self.heap[left]) {
                child = right;
            }
            let cv = self.heap[child];
            if !Self::better(act, cv, v) {
                break;
            }
            self.heap[i] = cv;
            self.pos[cv as usize] = i as i32;
            i = child;
        }
        self.heap[i] = v;
        self.pos[v as usize] = i as i32;
    }

    fn insert(&mut self, act: &[f64], v: u32) {
        if v as usize >= self.pos.len() {
            self.grow(v as usize + 1);
        }
        if self.pos[v as usize] >= 0 {
            return;
        }
        self.heap.push(v);
        let i = self.heap.len() - 1;
        self.pos[v as usize] = i as i32;
        self.up(act, i);
    }

    fn bump(&mut self, act: &[f64], v: u32) {
        let i = self.pos[v as usize];
        if i >= 0 {
            self.up(act, i as usize);
        }
    }

    fn pop_max(&mut self, act: &[f64]) -> Option<u32> {
        if self.heap.is_empty() {
            return None;
        }
        let top = self.heap[0];
        let last = self.heap.pop().unwrap();
        self.pos[top as usize] = -1;
        if !self.heap.is_empty() {
            self.heap[0] = last;
            self.pos[last as usize] = 0;
            self.down(act, 0);
        }
        Some(top)
    }

}

// ---------------------------------------------------------------------------
// the solver
// ---------------------------------------------------------------------------

pub struct Solver {
    pub cfg: Config,
    pub stats: Stats,
    pub nvars: u32,

    // clause storage
    lits: Vec<Lit>,
    headers: Vec<ClauseHeader>,
    clauses: Vec<u32>,
    learnts: Vec<u32>,

    // assignment
    val: Vec<u8>,
    level: Vec<u32>,
    reason: Vec<i32>,
    trail: Vec<Lit>,
    trail_lim: Vec<u32>,
    qhead: usize,

    // watches
    watches: Vec<Vec<Watch>>,

    // heuristics
    act: Vec<f64>,
    var_inc: f64,
    cla_inc: f64,
    order: Heap,
    polarity: Vec<bool>,
    /// Phases from the deepest conflict-free trail seen so far, and that
    /// depth. Only read when `cfg.target_phase` is set.
    target: Vec<bool>,
    target_size: usize,
    /// xorshift32, mirroring `Solver._rand` in cdclkit/solver.py so the walk
    /// reproduces flip for flip.
    rnd: u32,
    walk_best: usize,
    walk_stale: u64,
    deadline: Option<std::time::Instant>,

    // scratch
    seen: Vec<bool>,
    analyze_toclear: Vec<Lit>,
    lbd_stamp: Vec<u64>,
    lbd_gen: u64,

    // control
    pub ok: bool,
    pub model: Vec<bool>,

    lbd_fast: Ema,
    lbd_slow: Ema,
    trail_ema: Ema,
    next_reduce: u64,
    reduce_count: u64,
    restart_index: u64,
    conflicts_at_restart: u64,
    var_decay: f64,
    simp_props: u64,

    /// DRAT steps, as (is_deletion, literals).  Collected only when proof
    /// logging is on, because an UNSAT answer nobody can check is exactly the
    /// thing this project exists to avoid (PLAN.md Tier 1).
    pub proof: Vec<(bool, Vec<Lit>)>,
    pub logging: bool,
    /// Set once clauses start arriving.  Proof logging has to be switched on
    /// before that: `add_clause` can itself emit the empty clause, and a proof
    /// that starts midway through is not a proof.
    pub sealed: bool,

    /// Cooperative cancellation for the threaded portfolio.
    ///
    /// Checked once per conflict, which is free relative to what a conflict
    /// costs, and `Relaxed` because there is nothing to order against it --
    /// the only requirement is that the flag becomes visible eventually. This
    /// is the *entire* shared state between portfolio threads: every solver
    /// owns its clause arena, watches, trail and heap outright, so there is no
    /// lock anywhere and no data race to reason about.
    pub stop: Option<Arc<AtomicBool>>,
}

impl Solver {
    pub fn new(nvars: u32, cfg: Config) -> Self {
        // read before `cfg` is moved into the struct
        let rnd_seed = cfg.rnd_seed;
        let mut s = Self {
            var_decay: cfg.var_decay,
            cfg,
            stats: Stats::default(),
            nvars: 0,
            lits: Vec::new(),
            headers: Vec::new(),
            clauses: Vec::new(),
            learnts: Vec::new(),
            val: Vec::new(),
            level: Vec::new(),
            reason: Vec::new(),
            trail: Vec::new(),
            trail_lim: Vec::new(),
            qhead: 0,
            watches: Vec::new(),
            act: Vec::new(),
            var_inc: 1.0,
            cla_inc: 1.0,
            order: Heap::new(),
            polarity: Vec::new(),
            target: Vec::new(),
            target_size: 0,
            rnd: rnd_seed,
            walk_best: usize::MAX,
            walk_stale: 0,
            deadline: None,
            seen: Vec::new(),
            analyze_toclear: Vec::new(),
            lbd_stamp: Vec::new(),
            lbd_gen: 0,
            ok: true,
            model: Vec::new(),
            lbd_fast: Ema::new(1.0 / 50.0),
            lbd_slow: Ema::new(1.0 / 5000.0),
            trail_ema: Ema::new(1.0 / 5000.0),
            next_reduce: 0,
            reduce_count: 0,
            restart_index: 0,
            conflicts_at_restart: 0,
            simp_props: 0,
            proof: Vec::new(),
            logging: false,
            sealed: false,
            stop: None,
        };
        s.next_reduce = s.cfg.first_reduce;
        for _ in 0..nvars {
            s.new_var();
        }
        s
    }

    pub fn new_var(&mut self) -> u32 {
        let v = self.nvars;
        self.nvars += 1;
        self.val.push(U);
        self.val.push(U);
        self.level.push(0);
        self.reason.push(UNDEF);
        self.watches.push(Vec::new());
        self.watches.push(Vec::new());
        self.act.push(0.0);
        self.polarity.push(self.cfg.init_phase);
        self.target.push(false);
        self.seen.push(false);
        self.lbd_stamp.push(0);
        self.order.grow(self.nvars as usize);
        let act = &self.act;
        self.order.insert(act, v);
        v
    }

    fn ensure_vars(&mut self, n: u32) {
        while self.nvars < n {
            self.new_var();
        }
    }

    // -- clause access ------------------------------------------------------

    #[inline]
    fn cl(&self, c: u32) -> &[Lit] {
        let h = &self.headers[c as usize];
        let o = h.offset as usize;
        &self.lits[o..o + h.len as usize]
    }

    #[inline]
    fn cl_mut(&mut self, c: u32) -> &mut [Lit] {
        let h = &self.headers[c as usize];
        let o = h.offset as usize;
        let n = h.len as usize;
        &mut self.lits[o..o + n]
    }

    #[inline]
    fn decision_level(&self) -> u32 {
        self.trail_lim.len() as u32
    }

    #[inline]
    pub fn value(&self, l: Lit) -> u8 {
        self.val[l as usize]
    }

    fn alloc_clause(&mut self, lits: &[Lit], learnt: bool, lbd: u32) -> u32 {
        let offset = self.lits.len() as u32;
        self.lits.extend_from_slice(lits);
        self.headers.push(ClauseHeader {
            offset,
            len: lits.len() as u32,
            learnt,
            deleted: false,
            lbd,
            act: 0.0,
        });
        (self.headers.len() - 1) as u32
    }

    fn attach(&mut self, c: u32) {
        let (a, b, len) = {
            let l = self.cl(c);
            (l[0], l[1], l.len())
        };
        let _ = len;
        self.watches[neg(a) as usize].push(Watch { clause: c, blocker: b });
        self.watches[neg(b) as usize].push(Watch { clause: c, blocker: a });
    }

    fn detach(&mut self, c: u32) {
        let (a, b, len) = {
            let l = self.cl(c);
            (l[0], l[1], l.len())
        };
        let _ = len;
        for lit in [a, b] {
            let ws = &mut self.watches[neg(lit) as usize];
            if let Some(i) = ws.iter().position(|w| w.clause == c) {
                ws.remove(i);
            }
        }
    }

    fn locked(&self, c: u32) -> bool {
        let l0 = self.cl(c)[0];
        self.val[l0 as usize] == T && self.reason[var_of(l0) as usize] == c as i32
    }

    #[inline]
    fn proof_add(&mut self, lits: &[Lit]) {
        if self.logging {
            self.proof.push((false, lits.to_vec()));
        }
    }

    #[inline]
    fn proof_del(&mut self, lits: &[Lit]) {
        if self.logging {
            self.proof.push((true, lits.to_vec()));
        }
    }

    // -- clause addition ----------------------------------------------------

    /// Add a permanent clause.  False means the formula became unsatisfiable.
    pub fn add_clause(&mut self, input: &[Lit]) -> bool {
        self.sealed = true;
        if !self.ok {
            return false;
        }
        if self.decision_level() != 0 {
            self.cancel_until(0);
        }
        let mut seen: Vec<Lit> = Vec::with_capacity(input.len());
        let mut out: Vec<Lit> = Vec::with_capacity(input.len());
        for &l in input {
            self.ensure_vars(var_of(l) + 1);
            if seen.contains(&l) {
                continue;
            }
            if seen.contains(&neg(l)) {
                return true; // tautology
            }
            seen.push(l);
            let v = self.val[l as usize];
            if v == T && self.level[var_of(l) as usize] == 0 {
                return true; // already satisfied at root
            }
            if v == F && self.level[var_of(l) as usize] == 0 {
                continue; // root-false literal
            }
            out.push(l);
        }
        if out.is_empty() {
            self.proof_add(&[]);
            self.ok = false;
            return false;
        }
        if out.len() == 1 {
            self.assign(out[0], UNDEF);
            if self.propagate().is_some() {
                self.proof_add(&[]);
                self.ok = false;
                return false;
            }
            return true;
        }
        let c = self.alloc_clause(&out, false, 0);
        self.clauses.push(c);
        self.attach(c);
        true
    }

    // -- assignment ---------------------------------------------------------

    #[inline]
    fn assign(&mut self, lit: Lit, reason: i32) {
        let v = var_of(lit) as usize;
        self.val[lit as usize] = T;
        self.val[neg(lit) as usize] = F;
        self.level[v] = self.trail_lim.len() as u32;
        self.reason[v] = reason;
        self.trail.push(lit);
    }

    fn cancel_until(&mut self, level: u32) {
        if self.trail_lim.len() as u32 <= level {
            return;
        }
        let bound = self.trail_lim[level as usize] as usize;
        for i in (bound..self.trail.len()).rev() {
            let lit = self.trail[i];
            let v = var_of(lit) as usize;
            self.val[lit as usize] = U;
            self.val[neg(lit) as usize] = U;
            self.reason[v] = UNDEF;
            if self.cfg.phase_saving {
                self.polarity[v] = (lit & 1) == 0;
            }
            let act = &self.act;
            self.order.insert(act, v as u32);
        }
        self.trail.truncate(bound);
        self.trail_lim.truncate(level as usize);
        self.qhead = self.trail.len();
    }

    // -- propagation --------------------------------------------------------

    /// Unit-propagate to fixpoint; returns the conflicting clause if any.
    fn propagate(&mut self) -> Option<u32> {
        let mut confl: Option<u32> = None;
        let mut props: u64 = 0;

        while self.qhead < self.trail.len() {
            let p = self.trail[self.qhead];
            self.qhead += 1;
            props += 1;
            let false_lit = neg(p);

            // Take the list out so clause literals and other watch lists can
            // be mutated while we walk it.
            let mut ws = std::mem::take(&mut self.watches[p as usize]);
            let n = ws.len();
            let mut i = 0usize;
            let mut j = 0usize;

            while i < n {
                let w = ws[i];
                if self.val[w.blocker as usize] == T {
                    ws[j] = w;
                    i += 1;
                    j += 1;
                    continue;
                }
                let c = w.clause;
                // normalise: the false literal sits at index 1
                {
                    let lits = self.cl_mut(c);
                    if lits[0] == false_lit {
                        lits[0] = lits[1];
                        lits[1] = false_lit;
                    }
                }
                let first = self.cl(c)[0];
                if first != w.blocker && self.val[first as usize] == T {
                    ws[j] = Watch { clause: c, blocker: first };
                    i += 1;
                    j += 1;
                    continue;
                }

                // look for a replacement watch among lits[2..]
                let len = self.headers[c as usize].len as usize;
                let mut found = false;
                for k in 2..len {
                    let lk = self.cl(c)[k];
                    if self.val[lk as usize] != F {
                        {
                            let lits = self.cl_mut(c);
                            lits[1] = lk;
                            lits[k] = false_lit;
                        }
                        self.watches[neg(lk) as usize]
                            .push(Watch { clause: c, blocker: first });
                        found = true;
                        break;
                    }
                }
                if found {
                    i += 1;
                    continue;
                }

                // unit or conflicting
                ws[j] = w;
                i += 1;
                j += 1;
                if self.val[first as usize] == F {
                    confl = Some(c);
                    self.qhead = self.trail.len();
                    while i < n {
                        ws[j] = ws[i];
                        i += 1;
                        j += 1;
                    }
                    break;
                }
                self.assign(first, c as i32);
            }
            ws.truncate(j);
            self.watches[p as usize] = ws;

            if confl.is_some() {
                break;
            }
        }

        self.stats.propagations += props;
        if self.trail.len() > self.stats.max_trail {
            self.stats.max_trail = self.trail.len();
        }
        confl
    }

    // -- activity -----------------------------------------------------------

    fn bump_var(&mut self, v: u32) {
        let a = self.act[v as usize] + self.var_inc;
        self.act[v as usize] = a;
        if a > 1e100 {
            for x in self.act.iter_mut() {
                *x *= 1e-100;
            }
            self.var_inc *= 1e-100;
        }
        let act = &self.act;
        self.order.bump(act, v);
    }

    fn bump_clause(&mut self, c: u32) {
        self.headers[c as usize].act += self.cla_inc;
        if self.headers[c as usize].act > 1e20 {
            for &d in &self.learnts {
                self.headers[d as usize].act *= 1e-20;
            }
            self.cla_inc *= 1e-20;
        }
    }

    // -- conflict analysis --------------------------------------------------

    #[inline]
    fn abstract_level(&self, v: u32) -> u32 {
        1u32 << (self.level[v as usize] & 31)
    }

    fn lbd(&mut self, lits: &[Lit]) -> u32 {
        self.lbd_gen += 1;
        let gen = self.lbd_gen;
        let mut n = 0;
        for &l in lits {
            let lv = self.level[var_of(l) as usize] as usize;
            if self.lbd_stamp[lv] != gen {
                self.lbd_stamp[lv] = gen;
                n += 1;
            }
        }
        n
    }

    /// First-UIP analysis.  Returns (learnt clause, backjump level, LBD).
    fn analyze(&mut self, confl: u32) -> (Vec<Lit>, u32, u32) {
        let cur = self.trail_lim.len() as u32;
        let mut learnt: Vec<Lit> = vec![0]; // slot 0 reserved for the asserting literal
        let mut counter: i32 = 0;
        let mut p: i64 = -1;
        let mut index = self.trail.len() as i64 - 1;
        let mut confl = confl;

        loop {
            if self.headers[confl as usize].learnt {
                self.bump_clause(confl);
                if self.headers[confl as usize].lbd > 2 {
                    let lits: Vec<Lit> = self.cl(confl).to_vec();
                    let nl = self.lbd(&lits);
                    if nl < self.headers[confl as usize].lbd {
                        self.headers[confl as usize].lbd = nl;
                    }
                }
            }
            let start = if p < 0 { 0 } else { 1 };
            let len = self.headers[confl as usize].len as usize;
            for k in start..len {
                let q = self.cl(confl)[k];
                let v = var_of(q);
                if !self.seen[v as usize] && self.level[v as usize] > 0 {
                    self.seen[v as usize] = true;
                    self.bump_var(v);
                    if self.level[v as usize] >= cur {
                        counter += 1;
                    } else {
                        learnt.push(q);
                    }
                }
            }
            while !self.seen[var_of(self.trail[index as usize]) as usize] {
                index -= 1;
            }
            let pl = self.trail[index as usize];
            p = pl as i64;
            index -= 1;
            let v = var_of(pl);
            let r = self.reason[v as usize];
            self.seen[v as usize] = false;
            counter -= 1;
            if counter <= 0 {
                learnt[0] = neg(pl);
                break;
            }
            confl = r as u32;
        }

        let raw_len = learnt.len();

        // -- minimisation
        self.analyze_toclear = learnt.clone();
        match self.cfg.ccmin {
            CcMin::Deep => {
                let mut abstract_levels: u32 = 0;
                for &l in &learnt[1..] {
                    abstract_levels |= self.abstract_level(var_of(l));
                }
                let mut keep = vec![learnt[0]];
                for idx in 1..learnt.len() {
                    let l = learnt[idx];
                    if self.reason[var_of(l) as usize] == UNDEF
                        || !self.lit_redundant(l, abstract_levels)
                    {
                        keep.push(l);
                    }
                }
                learnt = keep;
            }
            CcMin::Basic => {
                let mut keep = vec![learnt[0]];
                for idx in 1..learnt.len() {
                    let l = learnt[idx];
                    let r = self.reason[var_of(l) as usize];
                    if r == UNDEF {
                        keep.push(l);
                        continue;
                    }
                    let len = self.headers[r as usize].len as usize;
                    for k in 1..len {
                        let q = self.cl(r as u32)[k];
                        let v = var_of(q);
                        if !self.seen[v as usize] && self.level[v as usize] > 0 {
                            keep.push(l);
                            break;
                        }
                    }
                }
                learnt = keep;
            }
            CcMin::None => {}
        }
        self.stats.minimized_lits += (raw_len - learnt.len()) as u64;

        // -- backjump level
        let bt = if learnt.len() == 1 {
            0
        } else {
            let mut best = 1usize;
            let mut best_lvl = self.level[var_of(learnt[1]) as usize];
            for i in 2..learnt.len() {
                let lv = self.level[var_of(learnt[i]) as usize];
                if lv > best_lvl {
                    best_lvl = lv;
                    best = i;
                }
            }
            learnt.swap(1, best);
            best_lvl
        };

        let lbd = self.lbd(&learnt);
        let toclear = std::mem::take(&mut self.analyze_toclear);
        for l in toclear {
            self.seen[var_of(l) as usize] = false;
        }
        (learnt, bt, lbd)
    }

    /// True when `p` is implied by the other literals of the learnt clause.
    fn lit_redundant(&mut self, p: Lit, abstract_levels: u32) -> bool {
        let mut stack: Vec<Lit> = vec![p];
        let top = self.analyze_toclear.len();
        while let Some(q) = stack.pop() {
            let c = self.reason[var_of(q) as usize];
            if c == UNDEF {
                for l in self.analyze_toclear.drain(top..) {
                    self.seen[var_of(l) as usize] = false;
                }
                return false;
            }
            let len = self.headers[c as usize].len as usize;
            for k in 1..len {
                let l = self.cl(c as u32)[k];
                let v = var_of(l);
                if self.seen[v as usize] || self.level[v as usize] == 0 {
                    continue;
                }
                if self.reason[v as usize] != UNDEF
                    && (self.abstract_level(v) & abstract_levels) != 0
                {
                    self.seen[v as usize] = true;
                    stack.push(l);
                    self.analyze_toclear.push(l);
                } else {
                    for l2 in self.analyze_toclear.drain(top..) {
                        self.seen[var_of(l2) as usize] = false;
                    }
                    return false;
                }
            }
        }
        true
    }

    // -- database -----------------------------------------------------------

    fn record(&mut self, learnt: &[Lit], lbd: u32) -> i32 {
        self.stats.learned += 1;
        self.stats.learned_lits += learnt.len() as u64;
        self.proof_add(learnt);
        if learnt.len() == 1 {
            return UNDEF;
        }
        let c = self.alloc_clause(learnt, true, lbd);
        self.headers[c as usize].act = self.cla_inc;
        self.learnts.push(c);
        self.attach(c);
        c as i32
    }

    fn reduce_db(&mut self) {
        self.stats.reductions += 1;
        let keep_lbd = self.cfg.glue_keep;
        let mut candidates: Vec<u32> = self
            .learnts
            .iter()
            .copied()
            .filter(|&c| {
                let h = &self.headers[c as usize];
                !h.deleted && h.lbd > keep_lbd && h.len > 2 && !self.locked(c)
            })
            .collect();
        // same ranking as Python: worst LBD first, then lowest activity.
        // Both sorts are stable, so ties keep insertion order.
        candidates.sort_by(|&a, &b| {
            let (ha, hb) = (&self.headers[a as usize], &self.headers[b as usize]);
            match hb.lbd.cmp(&ha.lbd) {
                std::cmp::Ordering::Equal => ha
                    .act
                    .partial_cmp(&hb.act)
                    .unwrap_or(std::cmp::Ordering::Equal),
                other => other,
            }
        });
        let limit = candidates.len() / 2;
        for idx in 0..limit {
            let c = candidates[idx];
            let lits: Vec<Lit> = self.cl(c).to_vec();
            self.proof_del(&lits);
            self.detach(c);
            if self.locked(c) {
                let l0 = self.cl(c)[0];
                self.reason[var_of(l0) as usize] = UNDEF;
            }
            self.headers[c as usize].deleted = true;
            self.stats.deleted += 1;
        }
        let headers = &self.headers;
        self.learnts.retain(|&c| !headers[c as usize].deleted);
    }


    // -- root simplification ------------------------------------------------

    /// Root-level simplification: drop clauses already satisfied at level 0
    /// and delete root-false literals from the rest.
    ///
    /// Mirrors `Solver._simplify`.  Strengthening in an arena is cheaper than
    /// it looks: the surviving literals are written back over the clause's own
    /// span and the length shrinks, leaving a gap that a later compaction
    /// reclaims.  What it must *not* do is reorder anything, since clause and
    /// watch order decide propagation order and therefore which conflict is
    /// found first.
    fn simplify(&mut self) -> bool {
        debug_assert_eq!(self.decision_level(), 0);
        if self.propagate().is_some() {
            self.proof_add(&[]);
            self.ok = false;
            return false;
        }
        for learnt_pass in [true, false] {
            let list = if learnt_pass { self.learnts.clone() } else { self.clauses.clone() };
            let mut out: Vec<u32> = Vec::with_capacity(list.len());
            for c in list {
                if self.headers[c as usize].deleted {
                    continue;
                }
                if self.locked(c) {
                    out.push(c);
                    continue;
                }
                let lits: Vec<Lit> = self.cl(c).to_vec();
                let mut sat = false;
                let mut nfalse = 0usize;
                for &l in &lits {
                    let v = var_of(l) as usize;
                    if self.val[l as usize] == T && self.level[v] == 0 {
                        sat = true;
                        break;
                    }
                    if self.val[l as usize] == F && self.level[v] == 0 {
                        nfalse += 1;
                    }
                }
                if sat {
                    self.proof_del(&lits);
                    self.detach(c);
                    self.headers[c as usize].deleted = true;
                    continue;
                }
                if nfalse > 0 {
                    let survivors: Vec<Lit> = lits
                        .iter()
                        .copied()
                        .filter(|&l| {
                            !(self.val[l as usize] == F && self.level[var_of(l) as usize] == 0)
                        })
                        .collect();
                    self.proof_add(&survivors);
                    self.detach(c);
                    self.proof_del(&lits);
                    if survivors.len() == 1 {
                        self.headers[c as usize].deleted = true;
                        let s0 = survivors[0];
                        if self.val[s0 as usize] == U {
                            self.assign(s0, UNDEF);
                        } else if self.val[s0 as usize] == F {
                            self.proof_add(&[]);
                            self.ok = false;
                            return false;
                        }
                        continue;
                    }
                    let offset = self.headers[c as usize].offset as usize;
                    for (k, &l) in survivors.iter().enumerate() {
                        self.lits[offset + k] = l;
                    }
                    self.headers[c as usize].len = survivors.len() as u32;
                    self.attach(c);
                }
                out.push(c);
            }
            if learnt_pass {
                self.learnts = out;
            } else {
                self.clauses = out;
            }
        }
        if self.propagate().is_some() {
            self.proof_add(&[]);
            self.ok = false;
            return false;
        }
        self.simp_props = self.stats.propagations;
        true
    }

    // -- decisions ----------------------------------------------------------

    fn pick_branch_lit(&mut self) -> i64 {
        // Destructure so the heap can be borrowed mutably while the activity
        // array is borrowed immutably.  The obvious `self.order.pop_max(&self.act)`
        // does not compile, and the obvious workaround -- cloning `act` -- costs
        // an allocation and a full copy of the activity vector on *every
        // iteration of this loop*, which on a 250-variable instance with
        // 200k decisions is tens of millions of wasted f64 copies.
        // Random decisions, gated exactly as the Python engine gates them.
        // The short-circuit order matters for bit-exactness: `rnd_freq > 0.0`
        // is tested first, so the default configuration never draws and the
        // PRNG stream stays aligned with the walk's use of it.
        //
        // Python also checks `not self.frozen[v]` here. There is no `frozen`
        // array on this side because nothing in the package ever creates a
        // non-decision variable -- `new_var(decision=False)` is public API with
        // no in-tree caller -- so the test is vacuously true. If that changes,
        // it has to change here too.
        if self.cfg.rnd_freq > 0.0
            && self.rand() < self.cfg.rnd_freq
            && !self.order.heap.is_empty()
        {
            let idx = (self.rand() * self.order.heap.len() as f64) as usize;
            let v = self.order.heap[idx];
            if self.val[(v << 1) as usize] == U {
                self.stats.decisions += 1;
                let phase: &Vec<bool> =
                    if self.cfg.target_phase { &self.target } else { &self.polarity };
                let l = (v << 1) | if phase[v as usize] { 0 } else { 1 };
                return l as i64;
            }
            // Falls through to the activity heap, exactly as Python does when
            // the sampled variable is already assigned.
        }
        let Self { order, act, val, polarity, target, cfg, stats, .. } = self;
        // Bind the source array once rather than testing per decision: this is
        // the hottest loop after propagation.
        let phase: &Vec<bool> = if cfg.target_phase { target } else { polarity };
        loop {
            let v = match order.pop_max(act) {
                None => return -1,
                Some(v) => v,
            };
            if val[(v << 1) as usize] == U {
                stats.decisions += 1;
                let l = (v << 1) | if phase[v as usize] { 0 } else { 1 };
                return l as i64;
            }
        }
    }


    // -- local search -------------------------------------------------------

    /// xorshift32, identical to `Solver._rand` in cdclkit/solver.py.
    #[inline]
    fn rand(&mut self) -> f64 {
        let mut x = self.rnd;
        x ^= x << 13;
        x ^= x >> 17;
        x ^= x << 5;
        self.rnd = x;
        self.rnd as f64 / 4294967296.0
    }

    /// Rebuilt on every call, never cached -- see `_walk_occurrences` in
    /// cdclkit/solver.py for why a cache diverged between the two engines.
    fn walk_occurrences(&mut self) -> (Vec<Vec<Lit>>, Vec<Vec<u32>>) {
        let mut clauses: Vec<Vec<Lit>> = Vec::new();
        for (ci, h) in self.headers.iter().enumerate() {
            if h.learnt || h.deleted || h.len <= 1 {
                continue;
            }
            let _ = ci;
            let off = h.offset as usize;
            clauses.push(self.lits[off..off + h.len as usize].to_vec());
        }
        let mut occ: Vec<Vec<u32>> = vec![Vec::new(); 2 * self.nvars as usize];
        for (i, lits) in clauses.iter().enumerate() {
            for &l in lits {
                occ[l as usize].push(i as u32);
            }
        }
        (clauses, occ)
    }

    /// probSAT over the original clauses; the best assignment becomes phases.
    ///
    /// Mirrors `Solver._walk` in cdclkit/solver.py flip for flip: same RNG, same
    /// weight table, same swap-remove order in the unsatisfied list. The order
    /// matters because the next clause is drawn by index into that list.
    fn walk(&mut self, max_flips: u64) {
        let (clauses, occ) = self.walk_occurrences();
        if clauses.is_empty() {
            return;
        }

        let mut assign: Vec<bool> =
            if self.cfg.target_phase { self.target.clone() } else { self.polarity.clone() };
        for v in 0..self.nvars as usize {
            if self.level[v] == 0 {
                if self.val[v << 1] == T {
                    assign[v] = true;
                } else if self.val[(v << 1) ^ 1] == T {
                    assign[v] = false;
                }
            }
        }

        let mut ntrue: Vec<u32> = clauses
            .iter()
            .map(|lits| {
                lits.iter()
                    .filter(|&&l| assign[(l >> 1) as usize] == ((l & 1) == 0))
                    .count() as u32
            })
            .collect();
        let mut unsat: Vec<u32> = Vec::new();
        let mut where_: Vec<i64> = vec![-1; clauses.len()];
        for (i, &n) in ntrue.iter().enumerate() {
            if n == 0 {
                where_[i] = unsat.len() as i64;
                unsat.push(i as u32);
            }
        }

        let mut best_unsat = unsat.len();
        let mut best = assign.clone();

        for _ in 0..max_flips {
            if unsat.is_empty() {
                break;
            }
            let pick = (self.rand() * unsat.len() as f64) as usize;
            let lits = clauses[unsat[pick] as usize].clone();

            let mut weights: Vec<(u32, f64)> = Vec::with_capacity(lits.len());
            let mut total = 0.0f64;
            for &l in &lits {
                let v = (l >> 1) as usize;
                let cur = ((v as u32) << 1) | if assign[v] { 0 } else { 1 };
                let brk = occ[cur as usize].iter().filter(|&&ci| ntrue[ci as usize] == 1).count();
                let w = WALK_WEIGHTS[brk.min(WALK_WEIGHTS.len() - 1)];
                weights.push((v as u32, w));
                total += w;
            }

            let r = self.rand() * total;
            let mut flip = weights[weights.len() - 1].0;
            let mut acc = 0.0f64;
            for &(v, w) in &weights {
                acc += w;
                if r <= acc {
                    flip = v;
                    break;
                }
            }

            let fv = flip as usize;
            let now_true = (flip << 1) | if assign[fv] { 0 } else { 1 };
            assign[fv] = !assign[fv];
            let new_true = (flip << 1) | if assign[fv] { 0 } else { 1 };
            for &ci in &occ[now_true as usize] {
                let c = ci as usize;
                ntrue[c] -= 1;
                if ntrue[c] == 0 {
                    where_[c] = unsat.len() as i64;
                    unsat.push(ci);
                }
            }
            for &ci in &occ[new_true as usize] {
                let c = ci as usize;
                if ntrue[c] == 0 {
                    let k = where_[c] as usize;
                    where_[c] = -1;
                    let last = unsat.pop().unwrap();
                    if k < unsat.len() {
                        unsat[k] = last;
                        where_[last as usize] = k as i64;
                    }
                }
                ntrue[c] += 1;
            }

            if unsat.len() < best_unsat {
                best_unsat = unsat.len();
                best.copy_from_slice(&assign);
            }
        }

        if best_unsat < self.walk_best {
            self.walk_best = best_unsat;
            self.walk_stale = 0;
        } else {
            self.walk_stale += 1;
        }
        self.target.copy_from_slice(&best);
        self.polarity.copy_from_slice(&best);
        self.target_size = 0;
    }

    // -- restarts -----------------------------------------------------------

    fn restart_due(&self) -> bool {
        match self.cfg.restart {
            RestartPolicy::None => false,
            RestartPolicy::Luby => {
                let budget = self.cfg.luby_base * luby(2.0, self.restart_index);
                (self.stats.conflicts - self.conflicts_at_restart) as f64 >= budget
            }
            RestartPolicy::Glucose => {
                if self.stats.conflicts - self.conflicts_at_restart < 50 {
                    return false;
                }
                self.lbd_fast.value * 0.8 > self.lbd_slow.value
            }
        }
    }

    fn block_restart(&self) -> bool {
        if !self.cfg.block_restart || self.stats.conflicts < 10000 {
            return false;
        }
        self.trail.len() as f64 > 1.4 * self.trail_ema.value
    }

    // -- search -------------------------------------------------------------

    /// Returns Some(true) SAT, Some(false) UNSAT, None if the budget ran out.
    /// `deadline` bounds wall-clock time; `None` leaves the search unbounded.
    /// Mirrors the `deadline` argument of `Solver.solve` in cdclkit/solver.py --
    /// checked every 256 conflicts so `Instant::now` stays out of the hot path,
    /// and inert when `None`, so determinism and bit-exactness are unaffected.
    pub fn solve_until(
        &mut self,
        max_conflicts: Option<u64>,
        deadline: Option<std::time::Instant>,
    ) -> Option<bool> {
        self.deadline = deadline;
        let r = self.solve(max_conflicts);
        self.deadline = None;
        r
    }

    pub fn solve(&mut self, max_conflicts: Option<u64>) -> Option<bool> {
        self.sealed = true;
        if !self.ok {
            return Some(false);
        }
        self.model.clear();
        self.cancel_until(0);
        let mut conflicts_here: u64 = 0;

        loop {
            if let Some(confl) = self.propagate() {
                self.stats.conflicts += 1;
                conflicts_here += 1;
                if let Some(ref stop) = self.stop {
                    if stop.load(Ordering::Relaxed) {
                        self.cancel_until(0);
                        return None; // another thread answered first
                    }
                }
                if self.decision_level() == 0 {
                    self.proof_add(&[]);
                    self.ok = false;
                    return Some(false);
                }
                let (learnt, bt, lbd) = self.analyze(confl);
                self.lbd_fast.update(lbd as f64);
                self.lbd_slow.update(lbd as f64);
                self.trail_ema.update(self.trail.len() as f64);
                if self.block_restart() {
                    self.stats.blocked_restarts += 1;
                    self.conflicts_at_restart = self.stats.conflicts;
                }
                self.cancel_until(bt);
                let cref = self.record(&learnt, lbd);
                self.assign(learnt[0], cref);
                self.var_inc /= self.var_decay;
                self.cla_inc /= self.cfg.cla_decay;
                if self.var_decay < self.cfg.var_decay_max {
                    self.var_decay = (self.var_decay + 0.01).min(self.cfg.var_decay_max);
                }
                if self.stats.conflicts >= self.next_reduce {
                    self.reduce_count += 1;
                    self.next_reduce = self.cfg.first_reduce
                        + self.cfg.reduce_inc * self.reduce_count * self.reduce_count;
                    self.reduce_db();
                }
            } else {
                // A new deepest conflict-free trail: remember the assignment
                // that reached it. O(|trail|), but only on a strict
                // improvement, and improvements become rare quickly.
                if self.cfg.target_phase && self.trail.len() > self.target_size {
                    self.target_size = self.trail.len();
                    for &t in &self.trail {
                        self.target[(t >> 1) as usize] = (t & 1) == 0;
                    }
                }
                if let Some(budget) = max_conflicts {
                    if conflicts_here >= budget {
                        self.cancel_until(0);
                        return None;
                    }
                }
                if let Some(dl) = self.deadline {
                    if conflicts_here & 255 == 0 && std::time::Instant::now() >= dl {
                        self.cancel_until(0);
                        return None;
                    }
                }
                if self.restart_due() {
                    self.stats.restarts += 1;
                    self.restart_index += 1;
                    self.conflicts_at_restart = self.stats.conflicts;
                    if self.cfg.target_reset != 0
                        && self.stats.restarts % self.cfg.target_reset == 0
                    {
                        self.target_size = 0;
                    }
                    if self.cfg.walk_flips != 0
                        && self.stats.conflicts >= self.cfg.walk_min_conflicts
                        && self.walk_stale < self.cfg.walk_patience
                        && self.stats.restarts % self.cfg.walk_interval == 0
                    {
                        self.cancel_until(0);
                        self.walk(self.cfg.walk_flips);
                    }
                    self.cancel_until(0);
                    continue;
                }
                if self.decision_level() == 0
                    && self.stats.propagations > self.simp_props
                    && !self.simplify()
                {
                    return Some(false);
                }
                let lit = self.pick_branch_lit();
                if lit < 0 {
                    self.model = (0..self.nvars)
                        .map(|v| self.val[(v << 1) as usize] == T)
                        .collect();
                    return Some(true);
                }
                self.trail_lim.push(self.trail.len() as u32);
                self.assign(lit as Lit, UNDEF);
            }
        }
    }

    // -- diagnostics --------------------------------------------------------

    /// Verify the two-watched-literal bookkeeping.  Test-suite only.
    pub fn check_watch_invariant(&self) -> Vec<String> {
        let mut errs = Vec::new();
        let mut counted = vec![0usize; self.headers.len()];
        for (p, ws) in self.watches.iter().enumerate() {
            for w in ws {
                let h = &self.headers[w.clause as usize];
                if h.deleted {
                    errs.push(format!("deleted clause still watched by {p}"));
                }
                let lits = self.cl(w.clause);
                let want = neg(p as Lit);
                if lits[0] != want && lits[1] != want {
                    errs.push(format!("clause {} in watches[{p}] does not watch it", w.clause));
                }
                counted[w.clause as usize] += 1;
            }
        }
        for &c in self.clauses.iter().chain(self.learnts.iter()) {
            if self.headers[c as usize].deleted {
                continue;
            }
            if counted[c as usize] != 2 {
                errs.push(format!(
                    "clause {c} has {} watchers, want 2",
                    counted[c as usize]
                ));
            }
        }
        errs
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn php(holes: u32) -> (u32, Vec<Vec<Lit>>) {
        let pigeons = holes + 1;
        let nv = pigeons * holes;
        let idx = |i: u32, j: u32| i * holes + j;
        let mut cs = Vec::new();
        for i in 0..pigeons {
            cs.push((0..holes).map(|j| idx(i, j) << 1).collect());
        }
        for j in 0..holes {
            for i in 0..pigeons {
                for k in (i + 1)..pigeons {
                    cs.push(vec![(idx(i, j) << 1) | 1, (idx(k, j) << 1) | 1]);
                }
            }
        }
        (nv, cs)
    }

    #[test]
    fn solves_a_trivial_formula() {
        let mut s = Solver::new(2, Config::default());
        assert!(s.add_clause(&[0, 2]));
        assert_eq!(s.solve(None), Some(true));
        assert!(s.model[0] || s.model[1]);
    }

    #[test]
    fn detects_a_trivial_contradiction() {
        let mut s = Solver::new(1, Config::default());
        assert!(s.add_clause(&[0]));
        assert!(!s.add_clause(&[1]));
        assert_eq!(s.solve(None), Some(false));
    }

    #[test]
    fn refutes_pigeonhole() {
        for holes in 3..=6 {
            let (nv, cs) = php(holes);
            let mut s = Solver::new(nv, Config::default());
            let mut ok = true;
            for c in &cs {
                if !s.add_clause(c) {
                    ok = false;
                    break;
                }
            }
            let res = if ok { s.solve(None) } else { Some(false) };
            assert_eq!(res, Some(false), "PHP({}, {holes}) must be UNSAT", holes + 1);
            assert!(s.check_watch_invariant().is_empty());
        }
    }

    #[test]
    fn luby_prefix_matches_the_reference() {
        let expected = [1.0, 1.0, 2.0, 1.0, 1.0, 2.0, 4.0, 1.0, 1.0, 2.0];
        for (i, &want) in expected.iter().enumerate() {
            assert_eq!(luby(2.0, i as u64), want, "luby index {i}");
        }
    }
}

#[cfg(test)]
mod layout_tests {
    use super::*;

    #[test]
    fn watch_entry_is_already_one_word() {
        // PLAN.md 7 proposes packing (clause, blocker) into a u64.  Two u32
        // fields already lay out as exactly that, so the "packing" win is
        // already banked and the proposal needs no code.
        assert_eq!(std::mem::size_of::<Watch>(), 8);
    }
}
