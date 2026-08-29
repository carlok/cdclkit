// SPDX-License-Identifier: Apache-2.0
// Copyright (c) 2026 Carlo Perassi. Licensed under the Apache License 2.0.
//! Threaded portfolio: N differently-configured solvers, first answer wins.
//!
//! # Why threads rather than processes
//!
//! The Python portfolio uses `multiprocessing`, because CPython's GIL makes
//! threads useless for a pure-Python solver. It works, but it pays **~60 ms of
//! process startup per solve**, and over a 17-instance benchmark that is a
//! ~1 s floor no amount of worker speed can get under. It is why the
//! process-based native portfolio (2.04 s) lost to a plain sequential native
//! solve with preprocessing (1.69 s), despite every worker being 18x faster
//! than the Python one it replaced.
//!
//! A thread spawn is ~50 µs. Same design, a thousandth of the overhead.
//!
//! # What is shared: almost nothing
//!
//! Each thread owns its solver outright -- clause arena, watch lists, trail,
//! activity heap. The **only** shared state is one `AtomicBool` that says
//! "someone answered, you can stop", checked once per conflict. No locks, no
//! contention, and nothing that needs `unsafe`.
//!
//! That is a deliberate choice, not laziness. Sharing learnt clauses between
//! threads is where the real parallel speedup lives, and it would destroy the
//! property this project exists for: an imported clause is not RUP in the
//! importing thread's proof stream, so its DRAT proof would no longer be a
//! valid refutation. With no sharing, the winning thread's proof is a complete
//! standalone refutation of the original formula, exactly as the sequential
//! solver's is.
//!
//! # The GIL
//!
//! The binding in `lib.rs` wraps the call in `Python::allow_threads`. Without
//! that the Python interpreter lock would be held for the whole solve and the
//! threads would serialise -- the entire exercise would be pointless.

use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::mpsc;
use std::sync::Arc;

use crate::solver::{Config, Solver, Stats};
use crate::Lit;

/// What one thread came back with.
pub struct PortfolioOutcome {
    pub winner: usize,
    /// Which clause set the winning thread solved: 0 = the formula as given,
    /// 1 = the alternative (in practice, a preprocessed copy).  The caller
    /// needs this to know whether the model requires reconstruction.
    pub clause_set: usize,
    pub sat: bool,
    pub model: Vec<bool>,
    pub stats: Stats,
    /// The winning thread's DRAT proof, when one was asked for.
    ///
    /// Because threads share no clauses, each buffer is already a complete
    /// standalone refutation of the formula that thread solved -- there is
    /// nothing to merge. That is the payoff of the no-sharing decision: a
    /// parallel solver whose UNSAT answers are still certifiable.
    pub proof: Vec<(bool, Vec<Lit>)>,
}

/// Run `configs.len()` solvers over the same formula and return the first
/// definitive answer.
///
/// Every thread solves the same formula, so whichever finishes first is
/// authoritative. Returns `None` only if every thread was cancelled without
/// answering, which cannot happen unless the caller cancels externally.
/// `alt` is an optional second formula -- in practice a preprocessed copy of
/// the first -- and the last `alt_threads` configurations solve it instead.
///
/// Preprocessing is worth 1.3-1.5x on structured instances and a loss on easy
/// ones, and which is which cannot be told from the formula. Running it as one
/// of the parallel strategies rather than as a decision sidesteps the question:
/// when it helps, that thread wins; when it does not, it costs nothing on the
/// critical path because the other threads were running anyway.
pub fn solve_portfolio(
    nvars: u32,
    clauses: &[Vec<Lit>],
    configs: &[Config],
    alt: Option<&[Vec<Lit>]>,
    alt_threads: usize,
    want_proof: bool,
) -> Option<PortfolioOutcome> {
    if configs.is_empty() {
        return None;
    }
    let alt_threads = match alt {
        Some(_) => alt_threads.min(configs.len()),
        None => 0,
    };
    if configs.len() == 1 {
        // No thread at all for a single configuration: keeps the one-worker
        // path identical to a plain sequential solve, which is what makes it
        // usable as a control in the benchmarks.
        let (set, cls) = if alt_threads == 1 {
            (1, alt.unwrap())
        } else {
            (0, clauses)
        };
        let mut out = run_one(0, nvars, cls, &configs[0], None, want_proof);
        out.clause_set = set;
        return Some(out);
    }

    let stop = Arc::new(AtomicBool::new(false));
    let (tx, rx) = mpsc::channel::<PortfolioOutcome>();

    let outcome = std::thread::scope(|scope| {
        let first_alt = configs.len() - alt_threads;
        for (i, cfg) in configs.iter().enumerate() {
            let tx = tx.clone();
            let stop = Arc::clone(&stop);
            let (set, cls) = if i >= first_alt {
                (1usize, alt.unwrap())
            } else {
                (0usize, clauses)
            };
            scope.spawn(move || {
                let mut out = run_one(i, nvars, cls, cfg, Some(stop.clone()), want_proof);
                out.clause_set = set;
                // A cancelled thread reports nothing; only a real answer counts.
                if !stop.load(Ordering::Relaxed) {
                    stop.store(true, Ordering::Relaxed);
                    let _ = tx.send(out);
                }
            });
        }
        // Drop the original sender so the channel closes once every thread has
        // finished, rather than blocking forever if all of them were cancelled.
        drop(tx);
        rx.recv().ok()
    });

    outcome
}

fn run_one(
    index: usize,
    nvars: u32,
    clauses: &[Vec<Lit>],
    cfg: &Config,
    stop: Option<Arc<AtomicBool>>,
    want_proof: bool,
) -> PortfolioOutcome {
    let mut s = Solver::new(nvars, cfg.clone());
    s.stop = stop;
    if want_proof {
        s.logging = true; // must precede the first clause
    }
    let mut ok = true;
    for c in clauses {
        if !s.add_clause(c) {
            ok = false;
            break;
        }
    }
    let res = if ok { s.solve(None) } else { Some(false) };
    PortfolioOutcome {
        winner: index,
        clause_set: 0,
        sat: res == Some(true),
        model: if res == Some(true) {
            std::mem::take(&mut s.model)
        } else {
            Vec::new()
        },
        stats: s.stats.clone(),
        proof: if want_proof && res == Some(false) {
            std::mem::take(&mut s.proof)
        } else {
            Vec::new()
        },
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::solver::{CcMin, RestartPolicy};

    fn configs(n: usize) -> Vec<Config> {
        // Mirrors the diversity axes of cdclkit/portfolio.py::default_configs.
        // Index 0 must be `Config::default()`, so a one-worker portfolio
        // reproduces the sequential solver -- that is what the test below
        // asserts. When the default moved to Luby this list still led with
        // Glucose and the invariant broke.
        let recipes: [(RestartPolicy, CcMin, bool); 4] = [
            (RestartPolicy::Luby, CcMin::Deep, true),
            (RestartPolicy::Glucose, CcMin::Deep, true),
            (RestartPolicy::Glucose, CcMin::Deep, false),
            (RestartPolicy::Luby, CcMin::Basic, true),
        ];
        (0..n)
            .map(|i| {
                let (restart, ccmin, phase) = recipes[i % recipes.len()];
                Config {
                    restart,
                    ccmin,
                    phase_saving: phase,
                    walk_flips: 0,
                    walk_interval: 4,
                    ..Default::default()
                }
            })
            .collect()
    }

    fn php(holes: u32) -> (u32, Vec<Vec<Lit>>) {
        let pigeons = holes + 1;
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
        (pigeons * holes, cs)
    }

    #[test]
    fn refutes_pigeonhole_in_parallel() {
        let (nv, cs) = php(6);
        let out = solve_portfolio(nv, &cs, &configs(4), None, 0, false).expect("an answer");
        assert!(!out.sat);
        assert!(out.winner < 4);
    }

    #[test]
    fn finds_a_model_in_parallel() {
        let clauses = vec![vec![0u32, 2], vec![1, 4]];
        let out = solve_portfolio(3, &clauses, &configs(4), None, 0, false).expect("an answer");
        assert!(out.sat);
        // the model must actually satisfy the formula
        for c in &clauses {
            assert!(c
                .iter()
                .any(|&l| out.model[(l >> 1) as usize] != ((l & 1) == 1)));
        }
    }

    #[test]
    fn single_config_takes_the_sequential_path() {
        let (nv, cs) = php(5);
        let out = solve_portfolio(nv, &cs, &configs(1), None, 0, false).expect("an answer");
        assert!(!out.sat);
        assert_eq!(out.winner, 0);

        let mut s = Solver::new(nv, Config::default());
        for c in &cs {
            s.add_clause(c);
        }
        s.solve(None);
        assert_eq!(out.stats.conflicts, s.stats.conflicts,
                   "one worker must reproduce the sequential solver exactly");
    }

    #[test]
    fn every_thread_is_joined() {
        // thread::scope guarantees it, but a leak here would be invisible
        // until it exhausted the process, so run enough to notice.
        for _ in 0..20 {
            let (nv, cs) = php(4);
            assert!(solve_portfolio(nv, &cs, &configs(4), None, 0, false).is_some());
        }
    }

    #[test]
    fn alternative_formula_threads_use_it() {
        // the alternative here is trivially unsatisfiable, so if an alt thread
        // wins it must report clause_set 1
        let (nv, cs) = php(4);
        let alt: Vec<Vec<Lit>> = vec![vec![0], vec![1]];
        let out = solve_portfolio(nv, &cs, &configs(4), Some(&alt), 2, false).expect("answer");
        assert!(!out.sat);
        assert!(out.clause_set <= 1);
    }

    #[test]
    fn the_winning_thread_returns_a_proof_when_asked() {
        let (nv, cs) = php(5);
        let out = solve_portfolio(nv, &cs, &configs(4), None, 0, true).expect("answer");
        assert!(!out.sat);
        assert!(!out.proof.is_empty(), "an UNSAT answer must carry a proof");
        // it must end with the empty clause
        assert!(out.proof.iter().any(|(d, l)| !d && l.is_empty()));
    }

    #[test]
    fn no_proof_is_collected_when_not_asked() {
        let (nv, cs) = php(4);
        let out = solve_portfolio(nv, &cs, &configs(4), None, 0, false).expect("answer");
        assert!(out.proof.is_empty());
    }

    #[test]
    fn empty_config_list_is_rejected() {
        let (nv, cs) = php(3);
        assert!(solve_portfolio(nv, &cs, &[], None, 0, false).is_none());
    }
}
