// SPDX-License-Identifier: Apache-2.0
// Copyright (c) 2026 Carlo Perassi. Licensed under the Apache License 2.0.

//! Checking a DRAT proof from Rust.
//!
//! Literals use a doubled index: variable `v` is `2v` when positive and
//! `2v + 1` when negated. So DIMACS `1` is literal `0`, DIMACS `-1` is `1`,
//! DIMACS `2` is `2`, DIMACS `-2` is `3`.

use dratify::{Checker, Lit};

/// Convert a DIMACS literal (1-based, signed) into the internal encoding.
fn lit(d: i32) -> Lit {
    let v = (d.unsigned_abs() - 1) as Lit;
    (v << 1) | if d < 0 { 1 } else { 0 }
}

fn main() {
    // (a v b) (a v ~b) (~a v b) (~a v ~b)  -- unsatisfiable
    let formula: Vec<Vec<Lit>> = vec![
        vec![lit(1), lit(2)],
        vec![lit(1), lit(-2)],
        vec![lit(-1), lit(2)],
        vec![lit(-1), lit(-2)],
    ];

    // A DRAT proof: derive "a", then the empty clause. Each step is
    // (is_deletion, literals).
    let proof: Vec<(bool, Vec<Lit>)> = vec![
        (false, vec![lit(1)]),
        (false, vec![]),
    ];

    let mut checker = Checker::new(2, &formula, true, true);
    let r = checker.check(&proof);

    println!("verified:      {}", r.ok);
    println!("empty clause:  {}", r.reached_empty);
    println!("steps checked: {} ({} by RUP, {} by RAT)", r.steps, r.rup_steps, r.rat_steps);

    // Now a dishonest proof: claim the empty clause with nothing to back it.
    let bogus: Vec<(bool, Vec<Lit>)> = vec![(false, vec![])];
    let mut c2 = Checker::new(2, &vec![vec![lit(1)]], true, true);
    let bad = c2.check(&bogus);
    println!();
    println!("bogus refutation accepted: {}", bad.ok);
    println!("reason: {}", bad.reason);
}
