// SPDX-License-Identifier: Apache-2.0
// Copyright (c) 2026 Carlo Perassi. Licensed under the Apache License 2.0.
//! Native preprocessing: unit propagation, subsumption, self-subsuming
//! resolution, pure literals and bounded variable elimination.
//!
//! Sprint 4 of `PLAN.md`, done after the measurement that justifies it rather
//! than because the roadmap listed it. On the structured instances added to
//! `bench/run_bench.py` (adder miters, LFSR unrollings, multiplier factoring)
//! preprocessing is worth ~1.35x, and it wins by roughly halving the clause
//! count rather than by reducing conflicts -- on factor(18b) the conflict count
//! actually rises while the time falls. Fewer clauses, cheaper propagation.
//!
//! The Python preprocessor costs 0.13-0.23 s on those instances, which is ~10%
//! of a long solve and more than 100% of a short one; that overhead is what
//! this removes.
//!
//! # Equisatisfiable, not equivalent
//!
//! Variable elimination and pure-literal elimination discard clauses whose
//! information cannot be recovered from the reduced formula. Every such step
//! is pushed onto an elimination stack and [`Preprocessor::reconstruct`]
//! replays it backwards to turn a model of the reduced formula into a model of
//! the original. Getting that wrong is the classic preprocessing bug: the
//! solver reports SAT and hands back an assignment that does not satisfy the
//! user's input.
//!
//! # Proofs
//!
//! Every clause added is logged before it is used and every clause removed
//! after, so a DRAT checker can follow along. Resolvents from variable
//! elimination are RUP -- negate the resolvent and both parents become unit on
//! opposite polarities of the pivot -- so no special support is needed on the
//! checker side.

use crate::{neg, var_of, Lit};

/// 64-bit occurrence signature, used to reject subsumption candidates cheaply.
#[inline]
fn signature(lits: &[Lit]) -> u64 {
    let mut s = 0u64;
    for &l in lits {
        s |= 1u64 << (var_of(l) & 63);
    }
    s
}

#[derive(Default, Clone, Debug)]
pub struct PreStats {
    pub rounds: u32,
    pub units: u64,
    pub subsumed: u64,
    pub strengthened: u64,
    pub eliminated_vars: u64,
    pub resolvents: u64,
    pub removed_clauses: u64,
    pub pure: u64,
    pub tautologies: u64,
    pub tried_vars: u64,
}

pub struct Preprocessor {
    pub nvars: u32,
    clauses: Vec<Option<Vec<Lit>>>,
    sigs: Vec<u64>,
    occ: Vec<Vec<u32>>,
    /// 0 = unset, 1 = true, 2 = false
    pub value: Vec<u8>,
    eliminated: Vec<(u32, Vec<Vec<Lit>>)>,
    frozen: Vec<bool>,
    pub unsat: bool,
    pub stats: PreStats,

    pub proof: Vec<(bool, Vec<Lit>)>,
    pub logging: bool,

    pub max_resolvent_len: usize,
    pub elim_growth: usize,
    pub do_bve: bool,
    pub subsumption_budget: i64,
}

impl Preprocessor {
    pub fn new(nvars: u32) -> Self {
        Self {
            nvars,
            clauses: Vec::new(),
            sigs: Vec::new(),
            occ: vec![Vec::new(); 2 * nvars as usize],
            value: vec![0; nvars as usize],
            eliminated: Vec::new(),
            frozen: vec![false; nvars as usize],
            unsat: false,
            stats: PreStats::default(),
            proof: Vec::new(),
            logging: false,
            max_resolvent_len: 20,
            elim_growth: 0,
            do_bve: true,
            subsumption_budget: 2_000_000,
        }
    }

    fn grow(&mut self, nvars: u32) {
        if nvars <= self.nvars && !self.occ.is_empty() {
            return;
        }
        self.nvars = self.nvars.max(nvars);
        self.occ.resize(2 * self.nvars as usize, Vec::new());
        self.value.resize(self.nvars as usize, 0);
        self.frozen.resize(self.nvars as usize, false);
    }

    pub fn freeze(&mut self, v: u32) {
        self.grow(v + 1);
        self.frozen[v as usize] = true;
    }

    // -- proof ---------------------------------------------------------

    #[inline]
    fn log_add(&mut self, lits: &[Lit]) {
        if self.logging {
            self.proof.push((false, lits.to_vec()));
        }
    }

    #[inline]
    fn log_del(&mut self, lits: &[Lit]) {
        if self.logging {
            self.proof.push((true, lits.to_vec()));
        }
    }

    // -- clause store --------------------------------------------------

    pub fn add_clause(&mut self, lits: &[Lit]) {
        let mut out: Vec<Lit> = Vec::with_capacity(lits.len());
        for &l in lits {
            self.grow(var_of(l) + 1);
            if out.contains(&l) {
                continue;
            }
            if out.contains(&neg(l)) {
                return; // tautology
            }
            out.push(l);
        }
        self.insert(out, false);
    }

    fn insert(&mut self, lits: Vec<Lit>, log: bool) -> u32 {
        if log {
            self.log_add(&lits);
        }
        let id = self.clauses.len() as u32;
        self.sigs.push(signature(&lits));
        for &l in &lits {
            self.occ[l as usize].push(id);
        }
        self.clauses.push(Some(lits));
        id
    }

    fn remove(&mut self, id: u32, log: bool) {
        let lits = match self.clauses[id as usize].take() {
            None => return,
            Some(l) => l,
        };
        for &l in &lits {
            let o = &mut self.occ[l as usize];
            if let Some(i) = o.iter().position(|&x| x == id) {
                o.swap_remove(i);
            }
        }
        if log {
            self.log_del(&lits);
        }
        self.stats.removed_clauses += 1;
    }

    fn replace(&mut self, id: u32, lits: Vec<Lit>) {
        let old = self.clauses[id as usize].clone().unwrap_or_default();
        self.log_add(&lits);
        for &l in &old {
            let o = &mut self.occ[l as usize];
            if let Some(i) = o.iter().position(|&x| x == id) {
                o.swap_remove(i);
            }
        }
        self.sigs[id as usize] = signature(&lits);
        for &l in &lits {
            self.occ[l as usize].push(id);
        }
        self.clauses[id as usize] = Some(lits);
        self.log_del(&old);
    }

    fn alive(&self) -> Vec<u32> {
        (0..self.clauses.len() as u32)
            .filter(|&i| self.clauses[i as usize].is_some())
            .collect()
    }

    // -- unit propagation ----------------------------------------------

    pub fn propagate(&mut self) -> bool {
        let mut queue: Vec<Lit> = self
            .alive()
            .into_iter()
            .filter_map(|i| {
                let c = self.clauses[i as usize].as_ref().unwrap();
                if c.len() == 1 {
                    Some(c[0])
                } else {
                    None
                }
            })
            .collect();

        while let Some(l) = queue.pop() {
            let v = var_of(l) as usize;
            let want = if (l & 1) == 0 { 1u8 } else { 2u8 };
            if self.value[v] != 0 {
                if self.value[v] != want {
                    self.unsat = true;
                    self.log_add(&[]);
                    return false;
                }
                continue;
            }
            self.value[v] = want;
            self.stats.units += 1;

            for id in self.occ[l as usize].clone() {
                self.remove(id, true);
            }
            for id in self.occ[neg(l) as usize].clone() {
                let c = match &self.clauses[id as usize] {
                    None => continue,
                    Some(c) => c.clone(),
                };
                let rest: Vec<Lit> = c.iter().copied().filter(|&x| x != neg(l)).collect();
                if rest.is_empty() {
                    self.unsat = true;
                    self.log_add(&[]);
                    return false;
                }
                let unit = if rest.len() == 1 { Some(rest[0]) } else { None };
                self.replace(id, rest);
                if let Some(u) = unit {
                    queue.push(u);
                }
            }
        }
        true
    }

    // -- subsumption ----------------------------------------------------

    pub fn subsume(&mut self) {
        let mut work = self.alive();
        work.sort_by_key(|&i| self.clauses[i as usize].as_ref().unwrap().len());
        let mut budget = self.subsumption_budget;

        for i in work {
            let c = match &self.clauses[i as usize] {
                None => continue,
                Some(c) => c.clone(),
            };
            // scan the occurrence list of the rarest literal
            let best = *c
                .iter()
                .min_by_key(|&&l| self.occ[l as usize].len() + self.occ[neg(l) as usize].len())
                .unwrap();
            let si = self.sigs[i as usize];
            for pol in [best, neg(best)] {
                for j in self.occ[pol as usize].clone() {
                    if j == i {
                        continue;
                    }
                    let d = match &self.clauses[j as usize] {
                        None => continue,
                        Some(d) => d.clone(),
                    };
                    if d.len() < c.len() {
                        continue;
                    }
                    budget -= 1;
                    if budget < 0 {
                        return;
                    }
                    if si & !self.sigs[j as usize] != 0 {
                        continue;
                    }
                    let mut missing: Option<Lit> = None;
                    let mut ok = true;
                    for &l in &c {
                        if d.contains(&l) {
                            continue;
                        }
                        if missing.is_some() {
                            ok = false;
                            break;
                        }
                        missing = Some(l);
                    }
                    if !ok {
                        continue;
                    }
                    match missing {
                        None => {
                            self.remove(j, true);
                            self.stats.subsumed += 1;
                        }
                        Some(l) if d.contains(&neg(l)) => {
                            // self-subsuming resolution: strengthen d
                            let new: Vec<Lit> =
                                d.iter().copied().filter(|&x| x != neg(l)).collect();
                            if new.is_empty() {
                                self.unsat = true;
                                self.log_add(&[]);
                                return;
                            }
                            self.replace(j, new);
                            self.stats.strengthened += 1;
                        }
                        _ => {}
                    }
                }
            }
        }
    }

    // -- resolution -----------------------------------------------------

    fn resolvent(&self, c: &[Lit], d: &[Lit], pivot: Lit) -> Option<Vec<Lit>> {
        let mut out: Vec<Lit> = c.iter().copied().filter(|&x| x != pivot).collect();
        for &x in d {
            if x == neg(pivot) {
                continue;
            }
            if out.contains(&neg(x)) {
                return None; // tautology
            }
            if !out.contains(&x) {
                out.push(x);
            }
        }
        Some(out)
    }

    fn pure_literals(&mut self) {
        for v in 0..self.nvars {
            if self.value[v as usize] != 0 || self.frozen[v as usize] {
                continue;
            }
            let pos = self.occ[(v << 1) as usize].len();
            let negc = self.occ[((v << 1) | 1) as usize].len();
            if pos > 0 && negc == 0 {
                self.eliminate_pure(v, true);
            } else if negc > 0 && pos == 0 {
                self.eliminate_pure(v, false);
            }
        }
    }

    fn eliminate_pure(&mut self, v: u32, positive: bool) {
        let lit = (v << 1) | if positive { 0 } else { 1 };
        let ids = self.occ[lit as usize].clone();
        let stored: Vec<Vec<Lit>> = ids
            .iter()
            .filter_map(|&i| self.clauses[i as usize].clone())
            .collect();
        if stored.is_empty() {
            return;
        }
        self.eliminated.push((v, stored));
        for id in ids {
            self.remove(id, true);
        }
        self.stats.pure += 1;
        self.stats.eliminated_vars += 1;
    }

    pub fn eliminate_vars(&mut self) -> bool {
        let mut order: Vec<u32> = (0..self.nvars)
            .filter(|&v| self.value[v as usize] == 0 && !self.frozen[v as usize])
            .collect();
        order.sort_by_key(|&v| {
            self.occ[(v << 1) as usize].len() * self.occ[((v << 1) | 1) as usize].len()
        });

        for v in order {
            if self.value[v as usize] != 0 {
                continue;
            }
            let pos_ids = self.occ[(v << 1) as usize].clone();
            let neg_ids = self.occ[((v << 1) | 1) as usize].clone();
            let pos: Vec<Vec<Lit>> = pos_ids
                .iter()
                .filter_map(|&i| self.clauses[i as usize].clone())
                .collect();
            let negs: Vec<Vec<Lit>> = neg_ids
                .iter()
                .filter_map(|&i| self.clauses[i as usize].clone())
                .collect();
            self.stats.tried_vars += 1;
            if pos.is_empty() && negs.is_empty() {
                continue;
            }
            if pos.len() * negs.len() > 400 {
                continue; // cheap guard against quadratic blowup
            }

            let mut resolvents: Vec<Vec<Lit>> = Vec::new();
            let mut too_big = false;
            'outer: for c in &pos {
                for d in &negs {
                    match self.resolvent(c, d, v << 1) {
                        None => {
                            self.stats.tautologies += 1;
                        }
                        Some(r) if r.is_empty() => {
                            self.log_add(&[]);
                            self.unsat = true;
                            return false;
                        }
                        Some(r) => {
                            if r.len() > self.max_resolvent_len {
                                too_big = true;
                                break 'outer;
                            }
                            resolvents.push(r);
                        }
                    }
                }
            }
            if too_big || resolvents.len() > pos.len() + negs.len() + self.elim_growth {
                continue;
            }

            // add resolvents first (they are RUP given the parents), then
            // delete the parents
            for r in &resolvents {
                self.insert(r.clone(), true);
                self.stats.resolvents += 1;
            }
            let mut stored = pos;
            stored.extend(negs);
            self.eliminated.push((v, stored));
            for id in pos_ids.into_iter().chain(neg_ids) {
                self.remove(id, true);
            }
            self.stats.eliminated_vars += 1;
        }
        true
    }

    // -- driver ---------------------------------------------------------

    pub fn run(&mut self, rounds: u32) -> bool {
        for _ in 0..rounds {
            self.stats.rounds += 1;
            let before = (
                self.stats.subsumed,
                self.stats.strengthened,
                self.stats.eliminated_vars,
            );
            if !self.propagate() {
                return false;
            }
            self.subsume();
            if self.unsat {
                return false;
            }
            self.pure_literals();
            if self.do_bve && !self.eliminate_vars() {
                return false;
            }
            if !self.propagate() {
                return false;
            }
            let after = (
                self.stats.subsumed,
                self.stats.strengthened,
                self.stats.eliminated_vars,
            );
            if before == after {
                break;
            }
        }
        true
    }

    pub fn reduced(&self) -> Vec<Vec<Lit>> {
        if self.unsat {
            return vec![vec![]];
        }
        self.alive()
            .into_iter()
            .map(|i| self.clauses[i as usize].clone().unwrap())
            .collect()
    }

    /// Extend a model of the reduced formula back to the original variables.
    pub fn reconstruct(&self, model: &[bool]) -> Result<Vec<bool>, String> {
        let mut full = vec![false; self.nvars as usize];
        for (v, slot) in full.iter_mut().enumerate() {
            if v < model.len() {
                *slot = model[v];
            }
        }
        for v in 0..self.nvars as usize {
            match self.value[v] {
                1 => full[v] = true,
                2 => full[v] = false,
                _ => {}
            }
        }
        let sat = |clause: &[Lit], m: &[bool]| -> bool {
            clause
                .iter()
                .any(|&l| m[var_of(l) as usize] != ((l & 1) == 1))
        };
        for (v, clauses) in self.eliminated.iter().rev() {
            let unsat_clauses: Vec<&Vec<Lit>> =
                clauses.iter().filter(|c| !sat(c, &full)).collect();
            if unsat_clauses.is_empty() {
                continue;
            }
            // Every unsatisfied clause must contain the same polarity of v:
            // if both polarities were unsatisfied their resolvent on v would
            // be unsatisfied too, and that resolvent is still in the reduced
            // formula which the model satisfies.
            let pos = unsat_clauses.iter().any(|c| c.contains(&(v << 1)));
            let negp = unsat_clauses.iter().any(|c| c.contains(&((v << 1) | 1)));
            if pos && negp {
                return Err(format!(
                    "reconstruction invariant violated for x{v}: clauses of \
                     both polarities are unsatisfied"
                ));
            }
            full[*v as usize] = pos;
            if !clauses.iter().all(|c| sat(c, &full)) {
                return Err(format!("reconstruction failed for x{v}"));
            }
        }
        Ok(full)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn propagates_units_away() {
        let mut p = Preprocessor::new(3);
        p.add_clause(&[0]); // x0
        p.add_clause(&[1, 2]); // ~x0 v x1
        p.add_clause(&[3, 4]); // ~x1 v x2
        assert!(p.run(3));
        assert!(p.reduced().is_empty(), "everything should propagate away");
        assert_eq!(p.value[0], 1);
        assert_eq!(p.value[1], 1);
        assert_eq!(p.value[2], 1);
    }

    #[test]
    fn detects_contradiction() {
        let mut p = Preprocessor::new(1);
        p.add_clause(&[0]);
        p.add_clause(&[1]);
        assert!(!p.run(3));
        assert!(p.unsat);
    }

    #[test]
    fn subsumes_the_weaker_clause() {
        let mut p = Preprocessor::new(3);
        p.do_bve = false;
        p.add_clause(&[0, 2]);
        p.add_clause(&[0, 2, 4]);
        p.run(1);
        assert_eq!(p.stats.subsumed, 1);
    }

    #[test]
    fn eliminates_a_variable_when_it_does_not_grow_the_formula() {
        let mut p = Preprocessor::new(3);
        p.add_clause(&[0, 2]); // x0 v x1
        p.add_clause(&[1, 4]); // ~x0 v x2
        assert!(p.run(1));
        assert!(p.stats.eliminated_vars >= 1);
    }

    #[test]
    fn reconstruction_restores_a_model() {
        let mut p = Preprocessor::new(2);
        p.add_clause(&[0, 2]);
        p.add_clause(&[0, 3]);
        assert!(p.run(3));
        let full = p.reconstruct(&[false, false]).expect("reconstruction");
        // the original clauses must hold under the reconstructed assignment
        for c in [[0u32, 2u32], [0u32, 3u32]] {
            assert!(c.iter().any(|&l| full[var_of(l) as usize] != ((l & 1) == 1)));
        }
    }

    #[test]
    fn tautologies_are_never_stored() {
        let mut p = Preprocessor::new(2);
        p.add_clause(&[0, 1]);
        assert_eq!(p.reduced().len(), 0);
    }
}
