// SPDX-License-Identifier: Apache-2.0
// Copyright (c) 2026 Carlo Perassi. Licensed under the Apache License 2.0.
//! Native forward DRAT checker: the RUP and RAT rules, at native speed.
//!
//! # Why this exists
//!
//! `cdclkit/proof.py` is correct and is the reference, but it had become the
//! slowest stage of any unsatisfiable run: **26x the solve time** on php(9,8),
//! and the ratio grows with instance size. Verification that expensive is
//! verification people switch off with a flag, which defeats the point of a
//! project whose premise is that every answer carries a checkable certificate.
//!
//! # Why the Python one stays
//!
//! It is not replaced, it is joined. The Python checker remains in the test
//! suite and both must agree on every proof, including the deliberately
//! corrupted ones. That matters more here than anywhere else in the codebase:
//! a checker exists to disagree with a buggy solver, so a checker written by
//! the same author against the same mental model is exactly the thing to be
//! suspicious of. Two implementations that agree, plus proofs from CaDiCaL and
//! kissat that neither implementation authored, is the strongest statement
//! available.
//!
//! # The rules
//!
//! **RUP** (reverse unit propagation): clause `C` is RUP with respect to `F`
//! when assigning every literal of `C` false and propagating yields a conflict.
//! Every clause a CDCL solver learns is RUP by construction.
//!
//! **RAT** (resolution asymmetric tautology): `C` is RAT on its first literal
//! `p` when, for every clause `D` containing `~p`, the resolvent
//! `C ∪ (D \ {~p})` is RUP. RAT clauses need not be entailed -- they only
//! preserve satisfiability -- which is what lets a proof justify
//! blocked-clause addition and extended resolution.
//!
//! Checking is **forward**: every step is verified against the clauses present
//! at that moment. Backward checking (drat-trim's default) is faster because it
//! skips lines that never contribute to the empty clause, but forward checking
//! is what you want when validating your own solver, since it exercises the
//! rarely-taken inferences where bugs live rather than trimming them away.

use std::collections::HashMap;

use crate::{neg, var_of, Lit};

const U: u8 = 0;
const T: u8 = 1;
const F: u8 = 2;

#[derive(Default, Clone, Debug)]
pub struct CheckResult {
    pub ok: bool,
    pub reason: String,
    pub steps: u64,
    pub rup_steps: u64,
    pub rat_steps: u64,
    pub deletions: u64,
    pub ignored_deletions: u64,
    pub resolvents_checked: u64,
    /// 1-based index of the first step that failed, or -1.
    pub failed_step: i64,
    pub failed_clause: Vec<Lit>,
    pub reached_empty: bool,
}

/// A minimal two-watched-literal propagator, separate from the solver's.
///
/// Deliberately plain: no heuristics, no learning, no deletion during
/// propagation. Correctness here is worth more than speed, because it is what
/// everything else is checked against.
struct Prop {
    nvars: u32,
    val: Vec<u8>,
    trail: Vec<Lit>,
    watches: Vec<Vec<u32>>,
    units: Vec<Lit>,
    clauses: Vec<Option<Vec<Lit>>>,
}

impl Prop {
    fn new(nvars: u32) -> Self {
        Self {
            nvars,
            val: vec![U; 2 * nvars as usize],
            trail: Vec::new(),
            watches: vec![Vec::new(); 2 * nvars as usize],
            units: Vec::new(),
            clauses: Vec::new(),
        }
    }

    fn grow(&mut self, nvars: u32) {
        while self.nvars < nvars {
            self.nvars += 1;
            self.val.push(U);
            self.val.push(U);
            self.watches.push(Vec::new());
            self.watches.push(Vec::new());
        }
    }

    fn attach(&mut self, lits: Vec<Lit>) -> u32 {
        let h = self.clauses.len() as u32;
        if lits.len() >= 2 {
            self.watches[neg(lits[0]) as usize].push(h);
            self.watches[neg(lits[1]) as usize].push(h);
        } else if lits.len() == 1 {
            self.units.push(lits[0]);
        }
        self.clauses.push(Some(lits));
        h
    }

    fn detach(&mut self, h: u32) {
        let lits = match self.clauses[h as usize].take() {
            None => return,
            Some(l) => l,
        };
        if lits.len() >= 2 {
            for a in [lits[0], lits[1]] {
                let ws = &mut self.watches[neg(a) as usize];
                if let Some(i) = ws.iter().position(|&x| x == h) {
                    ws.swap_remove(i);
                }
            }
        }
    }

    /// Set `lit` true.  False means that contradicts the trail.
    fn assign(&mut self, lit: Lit) -> bool {
        match self.val[lit as usize] {
            T => true,
            F => false,
            _ => {
                self.val[lit as usize] = T;
                self.val[neg(lit) as usize] = F;
                self.trail.push(lit);
                true
            }
        }
    }

    fn backtrack(&mut self, size: usize) {
        for i in (size..self.trail.len()).rev() {
            let lit = self.trail[i];
            self.val[lit as usize] = U;
            self.val[neg(lit) as usize] = U;
        }
        self.trail.truncate(size);
    }

    /// Propagate from `qhead`.  True means a conflict was found.
    fn propagate(&mut self, mut qhead: usize) -> bool {
        while qhead < self.trail.len() {
            let p = self.trail[qhead];
            qhead += 1;
            let false_lit = neg(p);
            let mut ws = std::mem::take(&mut self.watches[p as usize]);
            let n = ws.len();
            let (mut i, mut j) = (0usize, 0usize);
            let mut conflict = false;

            while i < n {
                let h = ws[i];
                let lits = match &mut self.clauses[h as usize] {
                    None => {
                        i += 1;
                        continue;
                    }
                    Some(l) => l,
                };
                if lits[0] == false_lit {
                    lits.swap(0, 1);
                }
                let first = lits[0];
                if self.val[first as usize] == T {
                    ws[j] = h;
                    i += 1;
                    j += 1;
                    continue;
                }
                let len = lits.len();
                let mut found = false;
                for k in 2..len {
                    let lk = lits[k];
                    if self.val[lk as usize] != F {
                        lits[1] = lk;
                        lits[k] = false_lit;
                        self.watches[neg(lk) as usize].push(h);
                        found = true;
                        break;
                    }
                }
                if found {
                    i += 1;
                    continue;
                }
                ws[j] = h;
                i += 1;
                j += 1;
                if self.val[first as usize] == F {
                    conflict = true;
                    while i < n {
                        ws[j] = ws[i];
                        i += 1;
                        j += 1;
                    }
                    break;
                }
                self.assign(first);
            }
            ws.truncate(j);
            self.watches[p as usize] = ws;
            if conflict {
                return true;
            }
        }
        false
    }
}

pub struct Checker {
    prop: Prop,
    occ: Vec<Vec<u32>>,
    index: HashMap<Vec<Lit>, Vec<u32>>,
    root_conflict: bool,
    check_rat: bool,
    apply_deletions: bool,
    result: CheckResult,
}

fn key(lits: &[Lit]) -> Vec<Lit> {
    let mut k: Vec<Lit> = lits.to_vec();
    k.sort_unstable();
    k.dedup();
    k
}

impl Checker {
    pub fn new(
        nvars: u32,
        clauses: &[Vec<Lit>],
        check_rat: bool,
        apply_deletions: bool,
    ) -> Self {
        let mut c = Self {
            prop: Prop::new(nvars),
            occ: vec![Vec::new(); 2 * nvars as usize],
            index: HashMap::new(),
            root_conflict: false,
            check_rat,
            apply_deletions,
            result: CheckResult { failed_step: -1, ..Default::default() },
        };
        for cl in clauses {
            if cl.is_empty() {
                // the input already contains the empty clause
                c.root_conflict = true;
            }
            c.insert(cl.clone());
        }
        c.root_conflict = c.root_conflict || c.propagate_root();
        c
    }

    fn grow(&mut self, lits: &[Lit]) {
        let need = lits.iter().map(|&l| var_of(l) + 1).max().unwrap_or(0);
        if need > self.prop.nvars {
            self.prop.grow(need);
            while self.occ.len() < 2 * self.prop.nvars as usize {
                self.occ.push(Vec::new());
            }
        }
    }

    fn insert(&mut self, lits: Vec<Lit>) -> u32 {
        self.grow(&lits);
        let k = key(&lits);
        let h = self.prop.attach(lits.clone());
        self.index.entry(k).or_default().push(h);
        for &l in &lits {
            self.occ[l as usize].push(h);
        }
        h
    }

    fn erase(&mut self, lits: &[Lit]) -> bool {
        let k = key(lits);
        let h = match self.index.get_mut(&k) {
            None => return false,
            Some(v) => match v.pop() {
                None => return false,
                Some(h) => h,
            },
        };
        let stored = self.prop.clauses[h as usize].clone();
        self.prop.detach(h);
        if let Some(st) = stored {
            for l in st {
                let o = &mut self.occ[l as usize];
                if let Some(i) = o.iter().position(|&x| x == h) {
                    o.swap_remove(i);
                }
            }
        }
        true
    }

    fn propagate_root(&mut self) -> bool {
        let units = self.prop.units.clone();
        for u in units {
            if !self.prop.assign(u) {
                return true;
            }
        }
        self.prop.propagate(0)
    }

    /// True when negating `lits` and propagating yields a conflict.
    fn is_rup(&mut self, lits: &[Lit]) -> bool {
        if self.root_conflict {
            return true;
        }
        let mark = self.prop.trail.len();
        let mut conflict = false;
        for &l in lits {
            if self.prop.val[l as usize] == T {
                // already satisfied at root: negating it is immediately
                // inconsistent, so RUP holds trivially
                conflict = true;
                break;
            }
            if !self.prop.assign(neg(l)) {
                conflict = true;
                break;
            }
        }
        if !conflict {
            conflict = self.prop.propagate(mark);
        }
        self.prop.backtrack(mark);
        conflict
    }

    /// RAT on the first literal, the pivot convention DRAT mandates.
    fn is_rat(&mut self, lits: &[Lit]) -> bool {
        if lits.is_empty() {
            return false;
        }
        let pivot = lits[0];
        let n = neg(pivot);
        if n as usize >= self.occ.len() {
            return true; // nothing contains ~pivot: vacuously RAT
        }
        let clause_set: std::collections::HashSet<Lit> = lits.iter().copied().collect();
        for h in self.occ[n as usize].clone() {
            let d = match &self.prop.clauses[h as usize] {
                None => continue,
                Some(d) => d.clone(),
            };
            let mut resolvent: Vec<Lit> = lits.to_vec();
            let mut tautology = false;
            for &l in &d {
                if l == n {
                    continue;
                }
                if clause_set.contains(&neg(l)) {
                    tautology = true;
                    break;
                }
                if !clause_set.contains(&l) {
                    resolvent.push(l);
                }
            }
            if tautology {
                continue;
            }
            self.result.resolvents_checked += 1;
            if !self.is_rup(&resolvent) {
                return false;
            }
        }
        true
    }

    pub fn check_step(&mut self, is_deletion: bool, lits: &[Lit]) -> bool {
        self.result.steps += 1;
        if !lits.is_empty() {
            // a proof may introduce variables the formula never mentions --
            // that is exactly what an extended-resolution step does
            self.grow(lits);
        }
        if is_deletion {
            if lits.len() <= 1 {
                // Deleting a unit already propagated into the root assignment
                // cannot be cleanly retracted, and every mainstream checker
                // skips it. Safe because RUP is monotone in the formula.
                self.result.ignored_deletions += 1;
                return true;
            }
            if self.apply_deletions {
                if self.erase(lits) {
                    self.result.deletions += 1;
                } else {
                    self.result.ignored_deletions += 1;
                }
            }
            return true;
        }

        if self.is_rup(lits) {
            self.result.rup_steps += 1;
        } else if self.check_rat && self.is_rat(lits) {
            self.result.rat_steps += 1;
        } else {
            self.result.failed_step = self.result.steps as i64;
            self.result.failed_clause = lits.to_vec();
            self.result.reason = if self.check_rat {
                "clause is neither RUP nor RAT with respect to the clauses \
                 available at this point"
                    .to_string()
            } else {
                "clause is not RUP (RAT checking disabled)".to_string()
            };
            return false;
        }

        if lits.is_empty() {
            self.result.reached_empty = true;
            return true;
        }
        self.insert(lits.to_vec());
        if lits.len() == 1 {
            if !self.prop.assign(lits[0]) {
                self.root_conflict = true;
            } else {
                let from = self.prop.trail.len().saturating_sub(1);
                if self.prop.propagate(from) {
                    self.root_conflict = true;
                }
            }
        }
        true
    }

    pub fn check(&mut self, steps: &[(bool, Vec<Lit>)]) -> CheckResult {
        if self.root_conflict {
            self.result.ok = true;
            self.result.reached_empty = true;
            self.result.reason =
                "input formula is refuted by unit propagation alone".to_string();
            return self.result.clone();
        }
        for (is_del, lits) in steps {
            if !self.check_step(*is_del, lits) {
                self.result.ok = false;
                return self.result.clone();
            }
            if self.result.reached_empty {
                break;
            }
        }
        if self.result.reached_empty {
            self.result.ok = true;
            self.result.reason = "empty clause derived and every step verified".to_string();
        } else {
            self.result.ok = false;
            self.result.reason =
                "every step verified, but the proof never derives the empty clause"
                    .to_string();
        }
        self.result.clone()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn refutes_a_formula_already_containing_the_empty_clause() {
        let r = Checker::new(2, &[vec![]], true, true).check(&[]);
        assert!(r.ok);
    }

    #[test]
    fn contradictory_units_are_refuted_by_propagation() {
        let r = Checker::new(1, &[vec![0], vec![1]], true, true).check(&[]);
        assert!(r.ok);
        assert!(r.reason.contains("unit propagation"));
    }

    #[test]
    fn a_valid_rup_chain_verifies() {
        // (a v b) (~a v b) (a v ~b) (~a v ~b) is unsatisfiable
        let f = vec![vec![0, 2], vec![1, 2], vec![0, 3], vec![1, 3]];
        let steps = vec![(false, vec![2]), (false, vec![3]), (false, vec![])];
        let r = Checker::new(2, &f, true, true).check(&steps);
        assert!(r.ok, "{}", r.reason);
        assert!(r.reached_empty);
    }

    #[test]
    fn claiming_the_empty_clause_on_a_satisfiable_formula_is_rejected() {
        let f = vec![vec![0, 2]];
        let r = Checker::new(2, &f, true, true).check(&[(false, vec![])]);
        assert!(!r.ok);
        assert_eq!(r.failed_step, 1);
    }

    #[test]
    fn rat_accepts_what_rup_rejects() {
        // F = { ~a v b }.  (a v ~b) is not RUP but is RAT on a: the only clause
        // containing ~a is (~a v b), and the resolvent is a tautology.
        let f = vec![vec![1, 2]];
        let clause = vec![0u32, 3];

        let mut rup_only = Checker::new(2, &f, false, true);
        assert!(!rup_only.check_step(false, &clause));

        let mut with_rat = Checker::new(2, &f, true, true);
        assert!(with_rat.check_step(false, &clause));
        assert_eq!(with_rat.result.rat_steps, 1);
    }

    #[test]
    fn proof_introducing_a_fresh_variable_does_not_panic() {
        // extended resolution: define d <-> (a & b) on a variable the formula
        // never mentions
        let f = vec![vec![0, 2]];
        let mut c = Checker::new(2, &f, true, true);
        for clause in [vec![5u32, 0], vec![5, 2], vec![4, 1, 3]] {
            assert!(c.check_step(false, &clause), "rejected {clause:?}");
        }
    }
}
