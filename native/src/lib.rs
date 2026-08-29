// SPDX-License-Identifier: Apache-2.0
// Copyright (c) 2026 Carlo Perassi. Licensed under the Apache License 2.0.
//! Native data layer for cdclkit: packed literals and a flat clause arena.
//!
//! Sprint 1 of the port described in `PLAN.md`. This is deliberately *only*
//! the data layout -- no search, no propagation. Getting the representation
//! right and proving it round-trips against the Python reference is the whole
//! job, because everything later is built on it.
//!
//! # Literals
//!
//! Identical encoding to `cdclkit/lits.py`: variable `v` becomes `2v`
//! (positive) or `2v+1` (negative), so negation is `^1` and the variable is
//! `>>1`. Keeping the two implementations bit-identical is what makes
//! differential testing meaningful -- a literal means the same number on both
//! sides, so a divergence is a real disagreement rather than a translation
//! artefact.
//!
//! # The arena
//!
//! The Python version stores each clause as a `Clause` object holding a
//! `list[int]`. Walking a watch list therefore chases a pointer per clause
//! into scattered heap memory, and profiling put ~14% of runtime in `len()`
//! and `list.append` alone.
//!
//! Here every clause lives in one contiguous `Vec<u32>`, with a side table of
//! `(offset, length)`. Consequences:
//!
//! * a clause is a `&[u32]` slice -- no indirection, no per-clause allocation;
//! * clauses added together are adjacent in memory, so a propagation that
//!   visits several of them stays inside a few cache lines;
//! * a clause reference is a `u32` index, which is half the size of a pointer
//!   and lets a watch entry pack a clause reference *and* a blocker literal
//!   into a single `u64` in Sprint 2.
//!
//! The cost is that clause deletion cannot be left to a garbage collector:
//! Sprint 2 will need explicit compaction with offset relocation.

pub mod checker;
pub mod portfolio;
pub mod preprocess;
pub mod solver;

use pyo3::exceptions::PyValueError;
use pyo3::prelude::*;

/// One portfolio worker's configuration, extracted from a Python dict.
///
/// Named rather than positional: pyo3 has no `FromPyObject` for tuples beyond
/// 12 elements, and more importantly a positional tuple mis-binds silently
/// when a field is inserted in the middle. `phase_saving` and `target_phase`
/// are both `bool` and adjacent, so a swap would compile and simply produce
/// the wrong search.
#[derive(FromPyObject)]
#[pyo3(from_item_all)]
struct WorkerConfig {
    restart: String,
    ccmin: String,
    phase_saving: bool,
    init_phase: bool,
    target_phase: bool,
    target_reset: u64,
    walk_flips: u64,
    walk_interval: u64,
    walk_patience: u64,
    walk_min_conflicts: u64,
    var_decay: f64,
    var_decay_max: f64,
    cla_decay: f64,
    luby_base: f64,
    first_reduce: u64,
    reduce_inc: u64,
    glue_keep: u32,
    block_restart: bool,
}



/// A literal in the doubled-index encoding.
pub type Lit = u32;

#[inline]
pub fn neg(l: Lit) -> Lit {
    l ^ 1
}

#[inline]
pub fn var_of(l: Lit) -> u32 {
    l >> 1
}

#[inline]
pub fn is_neg(l: Lit) -> bool {
    (l & 1) == 1
}

#[inline]
pub fn mk_lit(v: u32, negated: bool) -> Lit {
    (v << 1) | (negated as u32)
}

#[inline]
pub fn from_dimacs(d: i32) -> Lit {
    let v = (d.unsigned_abs() - 1) as u32;
    (v << 1) | ((d < 0) as u32)
}

#[inline]
pub fn to_dimacs(l: Lit) -> i32 {
    let v = (l >> 1) as i32 + 1;
    if is_neg(l) {
        -v
    } else {
        v
    }
}

// ---------------------------------------------------------------------------
// arena
// ---------------------------------------------------------------------------

/// A flat clause database: all literals in one allocation.
#[derive(Default)]
pub struct ClauseArena {
    /// Every clause's literals, back to back.
    pub lits: Vec<Lit>,
    /// Start of clause `i` inside `lits`.
    pub offsets: Vec<u32>,
    /// Length of clause `i`.
    pub lengths: Vec<u32>,
    /// Highest variable index seen, plus one.
    pub nvars: u32,
}

impl ClauseArena {
    pub fn with_vars(nvars: u32) -> Self {
        Self {
            nvars,
            ..Default::default()
        }
    }

    pub fn num_clauses(&self) -> usize {
        self.offsets.len()
    }

    pub fn num_lits(&self) -> usize {
        self.lits.len()
    }

    /// Literals of clause `i`.
    #[inline]
    pub fn clause(&self, i: usize) -> &[Lit] {
        let start = self.offsets[i] as usize;
        let len = self.lengths[i] as usize;
        &self.lits[start..start + len]
    }

    /// Add a clause, applying the same normalisation as `cdclkit.cnf.CNF.add`:
    /// duplicate literals collapse, tautologies are rejected, and the
    /// variable count grows to cover what was seen.
    ///
    /// Returns `false` for a tautology (nothing was added), matching the
    /// Python return convention exactly -- the round-trip test compares both
    /// the stored clauses *and* these return values.
    pub fn add(&mut self, input: &[Lit]) -> bool {
        let start = self.lits.len();
        for &l in input {
            let mut duplicate = false;
            for &existing in &self.lits[start..] {
                if existing == l {
                    duplicate = true;
                    break;
                }
                if existing == (l ^ 1) {
                    // tautology: undo the partial clause and reject
                    self.lits.truncate(start);
                    return false;
                }
            }
            if duplicate {
                continue;
            }
            self.lits.push(l);
            let v = (l >> 1) + 1;
            if v > self.nvars {
                self.nvars = v;
            }
        }
        self.offsets.push(start as u32);
        self.lengths.push((self.lits.len() - start) as u32);
        true
    }

    /// Bytes actually occupied by the clause data.
    pub fn memory_bytes(&self) -> usize {
        self.lits.capacity() * std::mem::size_of::<Lit>()
            + self.offsets.capacity() * std::mem::size_of::<u32>()
            + self.lengths.capacity() * std::mem::size_of::<u32>()
    }
}

// ---------------------------------------------------------------------------
// python bindings
// ---------------------------------------------------------------------------

/// A clause database living in native memory.
#[pyclass(name = "ClauseDb")]
pub struct PyClauseDb {
    inner: ClauseArena,
}

#[pymethods]
impl PyClauseDb {
    #[new]
    #[pyo3(signature = (nvars = 0))]
    fn new(nvars: u32) -> Self {
        Self {
            inner: ClauseArena::with_vars(nvars),
        }
    }

    /// Add a clause of internal literals.  False means it was a tautology.
    fn add_clause(&mut self, lits: Vec<u32>) -> PyResult<bool> {
        for &l in &lits {
            if l == u32::MAX {
                return Err(PyValueError::new_err("literal out of range"));
            }
        }
        Ok(self.inner.add(&lits))
    }

    /// Add a clause of signed 1-based DIMACS literals.
    fn add_dimacs(&mut self, lits: Vec<i32>) -> PyResult<bool> {
        let mut internal = Vec::with_capacity(lits.len());
        for d in lits {
            if d == 0 {
                return Err(PyValueError::new_err(
                    "0 is not a DIMACS literal (it terminates a clause)",
                ));
            }
            internal.push(from_dimacs(d));
        }
        Ok(self.inner.add(&internal))
    }

    /// Literals of clause `i`.
    fn clause(&self, i: usize) -> PyResult<Vec<u32>> {
        if i >= self.inner.num_clauses() {
            return Err(PyValueError::new_err(format!(
                "clause index {i} out of range ({} clauses)",
                self.inner.num_clauses()
            )));
        }
        Ok(self.inner.clause(i).to_vec())
    }

    /// Every clause, as a list of lists -- the round-trip out of the arena.
    fn clauses(&self) -> Vec<Vec<u32>> {
        (0..self.inner.num_clauses())
            .map(|i| self.inner.clause(i).to_vec())
            .collect()
    }

    #[getter]
    fn num_vars(&self) -> u32 {
        self.inner.nvars
    }

    #[getter]
    fn num_clauses(&self) -> usize {
        self.inner.num_clauses()
    }

    #[getter]
    fn num_lits(&self) -> usize {
        self.inner.num_lits()
    }

    #[getter]
    fn memory_bytes(&self) -> usize {
        self.inner.memory_bytes()
    }

    fn __len__(&self) -> usize {
        self.inner.num_clauses()
    }

    fn __repr__(&self) -> String {
        format!(
            "<ClauseDb vars={} clauses={} lits={} bytes={}>",
            self.inner.nvars,
            self.inner.num_clauses(),
            self.inner.num_lits(),
            self.inner.memory_bytes()
        )
    }
}


// ---------------------------------------------------------------------------
// solver binding
// ---------------------------------------------------------------------------

/// The native CDCL search core (Sprint 2).
///
/// Deliberately mirrors `cdclkit.solver.Solver` so the two can be compared
/// bit-for-bit while the port is intentionally faithful.
#[pyclass(name = "Solver")]
pub struct PySolver {
    inner: solver::Solver,
}

#[pymethods]
impl PySolver {
    #[new]
    // These defaults MUST equal `solver::Config::default()`, which must in turn
    // equal `Config()` in cdclkit/solver.py. Three places, and nothing in the
    // type system ties them together -- when the default flipped to Luby plus
    // target phases, this signature kept the old values and every caller that
    // omitted an argument silently got a different search. The Tier 2
    // bit-exactness test caught it; `tests/test_native_solver.py` now also
    // asserts the no-argument constructors agree, which is the direct check.
    #[pyo3(signature = (nvars = 0, restart = "luby", ccmin = "deep",
                        phase_saving = true, init_phase = false,
                        target_phase = true, target_reset = 0,
                        walk_flips = 20000, walk_interval = 1, walk_patience = 3,
                        walk_min_conflicts = 5000,
                        var_decay = 0.8, var_decay_max = 0.95,
                        cla_decay = 0.999, luby_base = 100.0,
                        first_reduce = 2000, reduce_inc = 300,
                        glue_keep = 2, block_restart = true))]
    #[allow(clippy::too_many_arguments)]
    fn new(
        nvars: u32, restart: &str, ccmin: &str, phase_saving: bool,
        init_phase: bool, target_phase: bool, target_reset: u64,
        walk_flips: u64, walk_interval: u64, walk_patience: u64,
        walk_min_conflicts: u64,
        var_decay: f64, var_decay_max: f64, cla_decay: f64,
        luby_base: f64, first_reduce: u64, reduce_inc: u64, glue_keep: u32,
        block_restart: bool,
    ) -> PyResult<Self> {
        let restart = match restart {
            "glucose" => solver::RestartPolicy::Glucose,
            "luby" => solver::RestartPolicy::Luby,
            "none" => solver::RestartPolicy::None,
            other => return Err(PyValueError::new_err(format!("unknown restart {other:?}"))),
        };
        let ccmin = match ccmin {
            "deep" => solver::CcMin::Deep,
            "basic" => solver::CcMin::Basic,
            "none" => solver::CcMin::None,
            other => return Err(PyValueError::new_err(format!("unknown ccmin {other:?}"))),
        };
        let cfg = solver::Config {
            var_decay, var_decay_max, cla_decay, restart, luby_base, ccmin,
            phase_saving, init_phase, target_phase, target_reset,
            walk_flips, walk_interval, walk_patience, walk_min_conflicts,
            first_reduce, reduce_inc, glue_keep, block_restart,
        };
        Ok(Self { inner: solver::Solver::new(nvars, cfg) })
    }

    fn new_var(&mut self) -> u32 { self.inner.new_var() }

    /// Turn on DRAT proof logging.  Must be called before any clause is added,
    /// since a proof that starts midway through is not a proof.
    fn enable_proof(&mut self) -> PyResult<()> {
        if self.inner.sealed {
            return Err(PyValueError::new_err(
                "enable_proof() must be called before any clause is added: a \
                 proof that starts midway through the formula is not a proof",
            ));
        }
        self.inner.logging = true;
        Ok(())
    }

    /// The recorded proof as (kind, dimacs_literals) pairs, kind in {"a","d"}.
    fn proof_steps(&self) -> Vec<(String, Vec<i32>)> {
        self.inner
            .proof
            .iter()
            .map(|(is_del, lits)| {
                (
                    (if *is_del { "d" } else { "a" }).to_string(),
                    lits.iter().map(|&l| to_dimacs(l)).collect(),
                )
            })
            .collect()
    }

    fn add_clause(&mut self, lits: Vec<u32>) -> bool { self.inner.add_clause(&lits) }

    #[pyo3(signature = (max_conflicts = None, seconds = None))]
    fn solve(&mut self, max_conflicts: Option<u64>, seconds: Option<f64>) -> Option<bool> {
        let deadline = seconds.map(|s| {
            std::time::Instant::now() + std::time::Duration::from_secs_f64(s)
        });
        self.inner.solve_until(max_conflicts, deadline)
    }

    #[getter] fn model(&self) -> Vec<bool> { self.inner.model.clone() }
    #[getter] fn nvars(&self) -> u32 { self.inner.nvars }
    #[getter] fn ok(&self) -> bool { self.inner.ok }
    #[getter] fn conflicts(&self) -> u64 { self.inner.stats.conflicts }
    #[getter] fn decisions(&self) -> u64 { self.inner.stats.decisions }
    #[getter] fn propagations(&self) -> u64 { self.inner.stats.propagations }
    #[getter] fn restarts(&self) -> u64 { self.inner.stats.restarts }
    #[getter] fn learned(&self) -> u64 { self.inner.stats.learned }
    #[getter] fn minimized_lits(&self) -> u64 { self.inner.stats.minimized_lits }
    #[getter] fn reductions(&self) -> u64 { self.inner.stats.reductions }

    fn check_watch_invariant(&self) -> Vec<String> {
        self.inner.check_watch_invariant()
    }

    fn __repr__(&self) -> String {
        format!("<native.Solver vars={} conflicts={}>",
                self.inner.nvars, self.inner.stats.conflicts)
    }
}


/// Native preprocessor: subsumption, self-subsuming resolution, pure literals
/// and bounded variable elimination.
#[pyclass(name = "Preprocessor")]
pub struct PyPreprocessor {
    inner: preprocess::Preprocessor,
}

#[pymethods]
impl PyPreprocessor {
    #[new]
    #[pyo3(signature = (nvars = 0, do_bve = true, max_resolvent_len = 20, with_proof = false))]
    fn new(nvars: u32, do_bve: bool, max_resolvent_len: usize, with_proof: bool) -> Self {
        let mut inner = preprocess::Preprocessor::new(nvars);
        inner.do_bve = do_bve;
        inner.max_resolvent_len = max_resolvent_len;
        inner.logging = with_proof;
        Self { inner }
    }

    fn add_clause(&mut self, lits: Vec<u32>) { self.inner.add_clause(&lits); }

    fn freeze(&mut self, v: u32) { self.inner.freeze(v); }

    #[pyo3(signature = (rounds = 3))]
    fn run(&mut self, rounds: u32) -> bool { self.inner.run(rounds) }

    fn reduced(&self) -> Vec<Vec<u32>> { self.inner.reduced() }

    fn reconstruct(&self, model: Vec<bool>) -> PyResult<Vec<bool>> {
        self.inner
            .reconstruct(&model)
            .map_err(PyValueError::new_err)
    }

    fn proof_steps(&self) -> Vec<(String, Vec<i32>)> {
        self.inner
            .proof
            .iter()
            .map(|(d, lits)| {
                ((if *d { "d" } else { "a" }).to_string(),
                 lits.iter().map(|&l| to_dimacs(l)).collect())
            })
            .collect()
    }

    #[getter] fn unsat(&self) -> bool { self.inner.unsat }
    #[getter] fn nvars(&self) -> u32 { self.inner.nvars }
    #[getter] fn units(&self) -> u64 { self.inner.stats.units }
    #[getter] fn subsumed(&self) -> u64 { self.inner.stats.subsumed }
    #[getter] fn strengthened(&self) -> u64 { self.inner.stats.strengthened }
    #[getter] fn eliminated_vars(&self) -> u64 { self.inner.stats.eliminated_vars }
    #[getter] fn resolvents(&self) -> u64 { self.inner.stats.resolvents }
    #[getter] fn pure(&self) -> u64 { self.inner.stats.pure }

    fn __repr__(&self) -> String {
        format!("<native.Preprocessor vars={} eliminated={} subsumed={}>",
                self.inner.nvars, self.inner.stats.eliminated_vars,
                self.inner.stats.subsumed)
    }
}


/// Run a threaded portfolio over one formula and return the first answer.
///
/// Releases the GIL for the duration: without that the Python interpreter lock
/// would be held across the whole solve and the threads would serialise, which
/// would make the entire exercise pointless.
#[pyfunction]
#[pyo3(name = "solve_portfolio")]
#[pyo3(signature = (nvars, clauses, configs, alt = None, alt_threads = 0, want_proof = false))]
fn py_solve_portfolio(
    py: Python<'_>,
    nvars: u32,
    clauses: Vec<Vec<u32>>,
    configs: Vec<WorkerConfig>,
    alt: Option<Vec<Vec<u32>>>,
    alt_threads: usize,
    want_proof: bool,
) -> PyResult<Option<(usize, usize, bool, Vec<bool>, u64, u64, u64, u64,
                     Vec<(bool, Vec<i32>)>)>> {
    let mut cfgs = Vec::with_capacity(configs.len());
    for c in configs {
        let WorkerConfig {
            restart, ccmin, phase_saving, init_phase, target_phase, target_reset,
            walk_flips, walk_interval, walk_patience, walk_min_conflicts, var_decay, var_decay_max, cla_decay, luby_base, first_reduce,
            reduce_inc, glue_keep, block_restart,
        } = c;
        cfgs.push(solver::Config {
            restart: match restart.as_str() {
                "glucose" => solver::RestartPolicy::Glucose,
                "luby" => solver::RestartPolicy::Luby,
                "none" => solver::RestartPolicy::None,
                o => return Err(PyValueError::new_err(format!("unknown restart {o:?}"))),
            },
            ccmin: match ccmin.as_str() {
                "deep" => solver::CcMin::Deep,
                "basic" => solver::CcMin::Basic,
                "none" => solver::CcMin::None,
                o => return Err(PyValueError::new_err(format!("unknown ccmin {o:?}"))),
            },
            phase_saving, init_phase, target_phase, target_reset, walk_flips,
            walk_interval, walk_patience, walk_min_conflicts, var_decay, var_decay_max, cla_decay, luby_base, first_reduce, reduce_inc,
            glue_keep, block_restart,
        });
    }

    let out = py.detach(|| {
        portfolio::solve_portfolio(nvars, &clauses, &cfgs,
                                   alt.as_deref(), alt_threads, want_proof)
    });
    Ok(out.map(|o| {
        let proof = o.proof.iter()
            .map(|(d, lits)| (*d, lits.iter().map(|&l| to_dimacs(l)).collect()))
            .collect();
        (o.winner, o.clause_set, o.sat, o.model, o.stats.conflicts,
         o.stats.decisions, o.stats.propagations, o.stats.restarts, proof)
    }))
}


/// Check a DRAT proof against a formula.
///
/// Returns the same shape `cdclkit.proof.CheckResult` carries, so the Python
/// wrapper can present one interface over either implementation.
#[pyfunction]
#[pyo3(name = "check_proof")]
#[pyo3(signature = (nvars, clauses, steps, check_rat = true, apply_deletions = true))]
fn py_check_proof(
    py: Python<'_>,
    nvars: u32,
    clauses: Vec<Vec<u32>>,
    steps: Vec<(bool, Vec<u32>)>,
    check_rat: bool,
    apply_deletions: bool,
) -> (bool, String, u64, u64, u64, u64, u64, u64, i64, bool) {
    let r = py.detach(|| {
        let mut c = checker::Checker::new(nvars, &clauses, check_rat, apply_deletions);
        c.check(&steps)
    });
    (r.ok, r.reason, r.steps, r.rup_steps, r.rat_steps, r.deletions,
     r.ignored_deletions, r.resolvents_checked, r.failed_step, r.reached_empty)
}

// -- literal helpers, exported so the encodings can be differentially tested --

#[pyfunction]
#[pyo3(name = "neg")]
fn py_neg(l: u32) -> u32 {
    neg(l)
}

#[pyfunction]
#[pyo3(name = "var_of")]
fn py_var_of(l: u32) -> u32 {
    var_of(l)
}

#[pyfunction]
#[pyo3(name = "is_neg")]
fn py_is_neg(l: u32) -> bool {
    is_neg(l)
}

#[pyfunction]
#[pyo3(name = "mk_lit")]
#[pyo3(signature = (v, negated = false))]
fn py_mk_lit(v: u32, negated: bool) -> u32 {
    mk_lit(v, negated)
}

#[pyfunction]
#[pyo3(name = "from_dimacs")]
fn py_from_dimacs(d: i32) -> PyResult<u32> {
    if d == 0 {
        return Err(PyValueError::new_err(
            "0 is not a DIMACS literal (it terminates a clause)",
        ));
    }
    Ok(from_dimacs(d))
}

#[pyfunction]
#[pyo3(name = "to_dimacs")]
fn py_to_dimacs(l: u32) -> i32 {
    to_dimacs(l)
}

#[pymodule]
fn cdclkit_native(m: &Bound<'_, PyModule>) -> PyResult<()> {
    m.add("__doc__", "Native engine for cdclkit (clause arena + CDCL search core)")?;
    m.add("__version__", env!("CARGO_PKG_VERSION"))?;
    m.add_class::<PyClauseDb>()?;
    m.add_class::<PySolver>()?;
    m.add_class::<PyPreprocessor>()?;
    m.add_function(wrap_pyfunction!(py_solve_portfolio, m)?)?;
    m.add_function(wrap_pyfunction!(py_check_proof, m)?)?;
    m.add_function(wrap_pyfunction!(py_neg, m)?)?;
    m.add_function(wrap_pyfunction!(py_var_of, m)?)?;
    m.add_function(wrap_pyfunction!(py_is_neg, m)?)?;
    m.add_function(wrap_pyfunction!(py_mk_lit, m)?)?;
    m.add_function(wrap_pyfunction!(py_from_dimacs, m)?)?;
    m.add_function(wrap_pyfunction!(py_to_dimacs, m)?)?;
    Ok(())
}

// ---------------------------------------------------------------------------
// rust-side unit tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn literal_encoding_round_trips() {
        for v in 0..1000u32 {
            for negated in [false, true] {
                let l = mk_lit(v, negated);
                assert_eq!(var_of(l), v);
                assert_eq!(is_neg(l), negated);
                assert_eq!(neg(neg(l)), l);
                assert_eq!(from_dimacs(to_dimacs(l)), l);
            }
        }
    }

    #[test]
    fn arena_stores_and_returns_clauses() {
        let mut a = ClauseArena::default();
        assert!(a.add(&[0, 2, 4]));
        assert!(a.add(&[1, 5]));
        assert_eq!(a.num_clauses(), 2);
        assert_eq!(a.clause(0), &[0, 2, 4]);
        assert_eq!(a.clause(1), &[1, 5]);
        assert_eq!(a.nvars, 3);
    }

    #[test]
    fn tautologies_are_rejected_and_leave_no_residue() {
        let mut a = ClauseArena::default();
        assert!(a.add(&[0, 2]));
        let lits_before = a.num_lits();
        assert!(!a.add(&[4, 6, 5])); // 4 and 5 are x2 and ~x2
        assert_eq!(a.num_clauses(), 1, "a rejected clause must not be stored");
        assert_eq!(a.num_lits(), lits_before, "partial clause must be unwound");
    }

    #[test]
    fn duplicate_literals_collapse() {
        let mut a = ClauseArena::default();
        assert!(a.add(&[2, 2, 4, 2]));
        assert_eq!(a.clause(0), &[2, 4]);
    }

    #[test]
    fn empty_clause_is_representable() {
        let mut a = ClauseArena::default();
        assert!(a.add(&[]));
        assert_eq!(a.num_clauses(), 1);
        assert_eq!(a.clause(0).len(), 0);
    }
}
