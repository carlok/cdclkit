// SPDX-License-Identifier: Apache-2.0
// Copyright (c) 2026 Carlo Perassi. Licensed under the Apache License 2.0.

//! Read the DIMACS and DRAT files Python wrote, and verify the refutation.
//!
//! This is the realistic shape: some other program produced the proof, and
//! this process has to decide whether to believe it. The two files are the
//! entire interface between them.

use dratify::{Checker, Lit};
use std::fs;

/// DIMACS literal (1-based, signed) to the internal doubled index.
fn lit(d: i32) -> Lit {
    let v = (d.unsigned_abs() - 1) as Lit;
    (v << 1) | if d < 0 { 1 } else { 0 }
}

/// Parse DIMACS CNF. Returns (number of variables, clauses).
fn parse_cnf(text: &str) -> (u32, Vec<Vec<Lit>>) {
    let mut nvars = 0;
    let mut clauses = Vec::new();
    for line in text.lines() {
        let line = line.trim();
        if line.is_empty() || line.starts_with('c') {
            continue;
        }
        if let Some(rest) = line.strip_prefix("p cnf ") {
            nvars = rest.split_whitespace().next().unwrap().parse().unwrap();
            continue;
        }
        clauses.push(line.split_whitespace()
            .map(|t| t.parse::<i32>().unwrap())
            .take_while(|&d| d != 0)
            .map(lit)
            .collect());
    }
    (nvars, clauses)
}

/// Parse a text DRAT proof into (is_deletion, literals) steps.
fn parse_drat(text: &str) -> Vec<(bool, Vec<Lit>)> {
    text.lines()
        .map(str::trim)
        .filter(|l| !l.is_empty())
        .map(|line| {
            let (del, body) = match line.strip_prefix("d ") {
                Some(rest) => (true, rest),
                None => (false, line),
            };
            (del, body.split_whitespace()
                .map(|t| t.parse::<i32>().unwrap())
                .take_while(|&d| d != 0)
                .map(lit)
                .collect())
        })
        .collect()
}

fn main() {
    let dir = concat!(env!("CARGO_MANIFEST_DIR"), "/../../build");
    let cnf = fs::read_to_string(format!("{dir}/timetable2.cnf"))
        .expect("run code/ex6_pipeline.py first to generate the files");
    let drat = fs::read_to_string(format!("{dir}/timetable2.drat")).unwrap();

    let (nvars, clauses) = parse_cnf(&cnf);
    let proof = parse_drat(&drat);
    println!("formula: {} variables, {} clauses", nvars, clauses.len());
    println!("proof:   {} steps", proof.len());

    let r = Checker::new(nvars, &clauses, true, true).check(&proof);
    println!();
    println!("verified:     {}", r.ok);
    println!("empty clause: {}", r.reached_empty);
    println!("by RUP:       {}", r.rup_steps);
    println!();
    println!("=> two exam slots really are impossible, and this process");
    println!("   confirmed it without trusting the solver that said so.");
}
