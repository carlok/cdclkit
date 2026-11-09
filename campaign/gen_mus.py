# SPDX-License-Identifier: Apache-2.0
# Copyright (c) 2026 Carlo Perassi. Licensed under the Apache License 2.0.
"""Soundness campaign, corner MUS: unsatisfiable, and minimally so.

The claim under test, from ``cdclkit/mus.py``: the returned set is unsatisfiable
and removing any one clause from it makes it satisfiable; a satisfiable input
gives ``[]``. Every result of every entry point is judged by ``campaign.oracle``
(``campaign.dpll`` past its 16 variables), never by ``MUSExtractor.verify``.

Entry points covered: ``mus`` with its default, ``"deletion"``, ``"quickxplain"``
and unknown methods; ``MUSExtractor.deletion``, ``.quickxplain`` (each with and
without ``use_core``, with and without ``subset``), ``.core``, ``.is_unsat``,
``.verify``; ``shrink_core``; and ``cdclkit mus --method ... [--verify]``.

Where a formula has at most ``ENUM_MAX`` clauses every MUS is enumerated from
the oracle's truth tables. The returned set must be one of them, and each MUS
handed back as ``subset`` must come back whole.

    python -m campaign.gen_mus                # the reported numbers
    python -m campaign.gen_mus --write        # also write results/mus.json
    python -m campaign.gen_mus --self-test    # wrong stubs must be flagged
"""

from __future__ import annotations

import argparse
import collections
import contextlib
import io
import json
import os
import random
import re
import sys
import tempfile
import time

from campaign import dpll, oracle, status

from cdclkit import cli as cdclkit_cli
from cdclkit.mus import MUSExtractor, mus as real_mus, shrink_core as real_shrink_core
from dratify.cnf import CNF, parse_dimacs

ENUM_MAX = 11           # clauses; all 2**n subsets are walked
SUBSET_MUS_CAP = 6      # enumerated MUSes handed back as `subset`, per instance
RECORD_CAP = 25         # mismatches kept in full

# Every category claimed in the report. A zero here fails the run.
REQUIRED = (
    "instances_unsat", "instances_sat",
    "inst_empty_formula", "inst_empty_clause", "inst_only_empty_clause",
    "inst_several_empty_clauses", "inst_duplicate_clause_unsat",
    "inst_duplicate_literal", "inst_tautology_dropped", "inst_free_vars",
    "inst_enumerated", "inst_several_muses", "inst_muses_of_different_sizes",
    "inst_methods_returned_different_muses",
    "mus_default", "mus_deletion", "mus_quickxplain", "mus_unknown_method_rejected",
    "ex_deletion_core", "ex_deletion_nocore", "ex_quickxplain_core",
    "ex_quickxplain_nocore", "ex_core", "shrink_core",
    "subset_calls", "subset_satisfiable", "subset_unsat", "subset_empty",
    "subset_repeated_index", "subset_tuple", "subset_mus_returned_whole",
    "is_unsat_true", "is_unsat_false",
    "verify_true", "verify_redundant", "verify_satisfiable", "verify_repeated_index",
    "result_one_copy_of_duplicate", "result_mus_size_1", "result_mus_size_ge_8",
    "core_not_minimal", "core_smaller_than_input", "core_equals_input",
    "cli_deletion", "cli_quickxplain", "cli_core", "cli_verify_ok",
    "cli_core_verify_not_minimal", "cli_satisfiable",
    "solver_conflicts", "solver_restarts", "solver_reductions", "solver_walks",
    "judged_by_oracle", "judged_by_dpll",
)


# -- the thing under test, replaceable by a wrong stub --------------------------

class Target:
    def __init__(self, extractor=MUSExtractor, mus=real_mus,
                 shrink_core=real_shrink_core, cli=cdclkit_cli.main):
        self.extractor = extractor
        self.mus = mus
        self.shrink_core = shrink_core
        self.cli = cli


# -- judging --------------------------------------------------------------------

def normalise(clauses):
    """What CNF.add documents: repeated literals collapse, tautologies drop."""
    out = []
    for c in clauses:
        seen = []
        taut = False
        for l in c:
            if -l in seen:
                taut = True
            if l not in seen:
                seen.append(l)
        if not taut:
            out.append(seen)
    return out


def decode(lit):
    """Internal literal to DIMACS, written out here rather than imported."""
    return -((lit >> 1) + 1) if lit & 1 else (lit >> 1) + 1


class Judge:
    """Satisfiability of index subsets of one formula, by the oracle."""

    def __init__(self, clauses, counts):
        self.clauses = clauses
        self.counts = counts
        self.memo = {}

    def sat(self, indices):
        key = frozenset(indices)
        got = self.memo.get(key)
        if got is None:
            sub = [self.clauses[i] for i in key]
            if len({abs(l) for c in sub for l in c}) <= oracle.MAX_VARS:
                self.counts["judged_by_oracle"] += 1
                got = oracle.satisfiable(sub)
            else:
                self.counts["judged_by_dpll"] += 1
                got = dpll.satisfiable(sub)
            self.memo[key] = got
        self.counts["steps"] += 1
        return got

    def is_mus(self, indices):
        s = set(indices)
        if self.sat(s):
            return False
        return all(self.sat(s - {i}) for i in s)


def enumerate_muses(clauses):
    """Every MUS, as a sorted tuple of indices, from the oracle's truth tables."""
    n = len(clauses)
    tables, full = oracle._masks([frozenset(c) for c in clauses])
    conj = [full] * (1 << n)
    for mask in range(1, 1 << n):
        low = mask & -mask
        conj[mask] = conj[mask ^ low] & tables[low.bit_length() - 1]
    found = []
    for mask in range(1, 1 << n):
        if conj[mask]:
            continue
        m = mask
        while m:
            low = m & -m
            if not conj[mask ^ low]:
                break
            m ^= low
        else:
            found.append(tuple(i for i in range(n) if mask >> i & 1))
    return found


class Run:
    def __init__(self, target, rng):
        self.t = target
        self.rng = rng
        self.counts = collections.Counter()
        self.mismatches = []
        self.total_mismatches = 0
        self.by_check = collections.Counter()
        self.by_label = collections.Counter()
        self.live = []          # extractors whose solver stats are still to count
        self.shared = None      # the one extractor reused across calls

    def bad(self, check, clauses, detail, label=None):
        self.total_mismatches += 1
        self.by_check[check] += 1
        self.by_label[label or "UNEXPLAINED"] += 1
        if len(self.mismatches) < RECORD_CAP:
            self.mismatches.append(
                {"check": check, "label": label, "formula": clauses, "detail": detail})

    def absorb(self, ex):
        st = getattr(getattr(ex, "solver", None), "stats", None)
        if st is None:
            return
        self.counts["solver_conflicts"] += st.conflicts
        self.counts["solver_restarts"] += st.restarts
        self.counts["solver_reductions"] += st.reductions
        self.counts["solver_walks"] += st.walks
        self.counts["solver_learned"] += st.learned

    # -- one returned set ---------------------------------------------------

    def check_result(self, check, res, scope, judge, clauses, must_be_minimal=True):
        """``res`` from a call over ``scope``. True when it is a MUS of it."""
        self.counts[check] += 1
        scope = set(scope)
        if not isinstance(res, list) or len(set(res)) != len(res) or res != sorted(res):
            self.bad(check + ":shape", clauses, f"not a sorted set of indices: {res!r}")
            return False
        if not set(res) <= scope:
            self.bad(check + ":outside_scope", clauses,
                     f"returned {res} from outside {sorted(scope)}")
            return False
        if judge.sat(scope):
            if res:
                self.bad(check + ":nonempty_on_sat", clauses,
                         f"scope {sorted(scope)} is satisfiable, returned {res}")
                return False
            return False
        if not res:
            self.bad(check + ":empty_on_unsat", clauses,
                     f"scope {sorted(scope)} is unsatisfiable, returned []")
            return False
        if judge.sat(res):
            self.bad(check + ":result_satisfiable", clauses,
                     f"scope {sorted(scope)}, returned {res}, which is satisfiable")
            return False
        if must_be_minimal:
            for i in res:
                if not judge.sat(set(res) - {i}):
                    self.bad(check + ":not_minimal", clauses,
                             f"returned {res}; still unsatisfiable without clause {i}")
                    return False
        return True

    def call(self, check, fn, clauses, repeated=False):
        """A crash on valid input is a mismatch, not the end of the run."""
        try:
            return True, fn()
        except Exception as e:  # noqa: BLE001 - the harness reports it
            known = repeated and isinstance(e, IndexError)
            self.bad(check + ":raised", clauses, f"{type(e).__name__}: {e}",
                     "mus-1" if known else None)
            if known:
                self.counts["repeated_index_raised"] += 1
            return False, None

    def after_crash(self, f, judge, raw):
        """What the extractor says once it has raised, then replace it.

        Nothing should be asked of it, and nothing said here is about the
        method that raised: these are separate mismatches, with their own name,
        and the next call gets a fresh extractor.
        """
        ex = self.shared
        n = len(judge.clauses)
        for _ in range(8):
            sub = [i for i in range(n) if self.rng.random() < 0.6]
            ok, got = self.call("post_crash_is_unsat", lambda s=sub: ex.is_unsat(s), raw, True)
            self.counts["post_crash_probes"] += 1
            if ok and got is not (not judge.sat(sub)):
                self.counts["post_crash_wrong"] += 1
                self.bad("post_crash_is_unsat", raw,
                         f"after IndexError, is_unsat({sub}) said {got}", "mus-1")
        self.shared = self.fresh(f)

    # -- one formula --------------------------------------------------------

    def check_instance(self, raw, nvars_decl):
        counts = self.counts
        clauses = normalise(raw)
        f = build(raw, nvars_decl, self.rng)
        if [[decode(l) for l in c] for c in f.clauses] != clauses:
            self.bad("cnf_indices", raw, f"parsed {f.clauses}, expected {clauses}")
            return
        before = (list(f.clauses), f.nvars)
        judge = Judge(clauses, counts)
        everything = range(len(clauses))
        unsat = not judge.sat(everything)
        counts["instances"] += 1
        counts["instances_unsat" if unsat else "instances_sat"] += 1
        self.classify(raw, clauses, nvars_decl, unsat)

        results = {}
        for check, fn in (
            ("mus_default", lambda: self.t.mus(f)),
            ("mus_deletion", lambda: self.t.mus(f, "deletion")),
            ("mus_quickxplain", lambda: self.t.mus(f, "quickxplain")),
            ("ex_deletion_core", lambda: self.fresh(f).deletion()),
            ("ex_deletion_nocore", lambda: self.fresh(f).deletion(use_core=False)),
            ("ex_quickxplain_core", lambda: self.fresh(f).quickxplain()),
            ("ex_quickxplain_nocore", lambda: self.fresh(f).quickxplain(use_core=False)),
        ):
            ok, res = self.call(check, fn, raw)
            if ok and self.check_result(check, res, everything, judge, raw):
                results[check] = res

        cores = {}
        for check, fn in (("shrink_core", lambda: self.t.shrink_core(f)),
                          ("ex_core", lambda: self.fresh(f).core())):
            ok, res = self.call(check, fn, raw)
            if ok:
                self.check_core(check, res, everything, judge, raw)
                cores[check] = res

        for name in self.bad_methods():
            try:
                self.t.mus(f, name)
            except ValueError:
                counts["mus_unknown_method_rejected"] += 1
            except Exception as e:  # noqa: BLE001
                self.bad("mus_unknown_method", raw, f"{name!r}: {type(e).__name__}: {e}")
            else:
                self.bad("mus_unknown_method", raw, f"{name!r} was accepted")

        if "mus_default" in results and "mus_deletion" in results \
                and results["mus_default"] != results["mus_deletion"]:
            self.bad("mus_default_is_deletion", raw,
                     f"{results['mus_default']} vs {results['mus_deletion']}")
        # tests/test_mus.py: "a MUS must sit inside the core it came from"
        if "ex_core" in cores:
            for check in ("mus_deletion", "mus_quickxplain"):
                if check in results and not set(results[check]) <= set(cores["ex_core"]):
                    self.bad("mus_inside_core", raw,
                             f"{check}={results[check]} core={cores['ex_core']}")
        if unsat and results:
            self.observe_results(raw, clauses, results, cores)

        muses = None
        if len(clauses) <= ENUM_MAX:
            muses = enumerate_muses(clauses)
            counts["steps"] += 1
            counts["inst_enumerated"] += 1
            if bool(muses) != unsat:
                self.bad("enumeration", raw, f"{muses} but unsat={unsat}")
            known = set(muses)
            for check, res in results.items():
                if tuple(res) not in known and unsat:
                    self.bad(check + ":not_enumerated", raw, f"{res} not in {muses}")
            if len(muses) > 1:
                counts["inst_several_muses"] += 1
                if len({len(m) for m in muses}) > 1:
                    counts["inst_muses_of_different_sizes"] += 1

        self.shared = self.fresh(f)
        self.check_subsets(f, clauses, raw, judge, muses, results)
        self.check_is_unsat(clauses, raw, judge)
        self.check_verify(f, clauses, raw, judge, results)
        self.check_call_docs(f, raw, unsat)
        self.check_cli(raw, clauses, nvars_decl, judge, unsat)
        for ex in self.live:
            self.absorb(ex)
        self.live = []

        if (list(f.clauses), f.nvars) != before:
            self.bad("formula_mutated", raw, "the input CNF changed")
        counts["steps"] += 1

    def fresh(self, f):
        ex = self.t.extractor(f)
        self.live.append(ex)
        return ex

    def bad_methods(self):
        return self.rng.sample(["", "DELETION", "core", "qx", "quickXplain", None], 1)

    def classify(self, raw, clauses, nvars_decl, unsat):
        counts = self.counts
        empties = sum(1 for c in clauses if not c)
        if not raw:
            counts["inst_empty_formula"] += 1
        if empties:
            counts["inst_empty_clause"] += 1
            if len(clauses) == empties == 1:
                counts["inst_only_empty_clause"] += 1
            if empties > 1:
                counts["inst_several_empty_clauses"] += 1
        sets = [frozenset(c) for c in clauses]
        if unsat and len(set(sets)) != len(sets):
            counts["inst_duplicate_clause_unsat"] += 1
        if any(len(set(c)) != len(c) for c in raw):
            counts["inst_duplicate_literal"] += 1
        if len(raw) != len(clauses):
            counts["inst_tautology_dropped"] += 1
        if nvars_decl > max((abs(l) for c in raw for l in c), default=0):
            counts["inst_free_vars"] += 1

    def observe_results(self, raw, clauses, results, cores):
        counts = self.counts
        if len({tuple(r) for r in results.values()}) > 1:
            counts["inst_methods_returned_different_muses"] += 1
        sets = [frozenset(c) for c in clauses]
        multiplicity = collections.Counter(sets)
        for res in results.values():
            if len(res) == 1:
                counts["result_mus_size_1"] += 1
            if len(res) >= 8:
                counts["result_mus_size_ge_8"] += 1
            if any(multiplicity[sets[i]] > 1 for i in res):
                counts["result_one_copy_of_duplicate"] += 1
        core = cores.get("ex_core")
        if core and "ex_deletion_core" in results:
            if len(core) > len(results["ex_deletion_core"]):
                counts["core_not_minimal"] += 1
            if len(core) < len(clauses):
                counts["core_smaller_than_input"] += 1
            if len(core) == len(clauses):
                counts["core_equals_input"] += 1

    def check_core(self, check, res, scope, judge, raw):
        """A core is unsatisfiable and inside the scope; nobody says minimal."""
        self.check_result(check, res, scope, judge, raw, must_be_minimal=False)

    # -- subset= ------------------------------------------------------------

    def check_subsets(self, f, clauses, raw, judge, muses, results):
        counts = self.counts
        rng = self.rng
        n = len(clauses)
        some = next(iter(results.values()), None)
        subsets = [("empty", [])]
        if n:
            subsets.append(("half", [i for i in range(n) if rng.random() < 0.6]))
            subsets.append(("tuple", tuple(i for i in range(n) if rng.random() < 0.8)))
            pick = rng.randrange(n)
            copies = [pick] * rng.randint(2, 4 + n)
            subsets.append(("repeated", copies + [i for i in range(n) if rng.random() < 0.5]))
        if some:
            noise = [i for i in range(n) if rng.random() < 0.3]
            subsets.append(("mus_plus_noise", sorted(set(some) | set(noise))))
            # without one clause of a MUS: a different MUS, or none at all
            gone = rng.choice(some)
            subsets.append(("hitting", [i for i in range(n) if i != gone]))
        for kind, sub in subsets:
            scope = set(sub)
            sat = judge.sat(scope)
            counts["subset_satisfiable" if sat else "subset_unsat"] += 1
            if kind == "empty":
                counts["subset_empty"] += 1
            elif kind == "repeated":
                counts["subset_repeated_index"] += 1
            elif kind == "tuple":
                counts["subset_tuple"] += 1
            repeated = len(sub) != len(scope)
            for check, fn, minimal in (
                ("sub_deletion_core", lambda: self.shared.deletion(sub), True),
                ("sub_deletion_nocore", lambda: self.shared.deletion(sub, use_core=False), True),
                ("sub_quickxplain_core", lambda: self.shared.quickxplain(sub), True),
                ("sub_quickxplain_nocore",
                 lambda: self.shared.quickxplain(sub, use_core=False), True),
                ("sub_core", lambda: self.shared.core(sub), False),
            ):
                ok, res = self.call(check, fn, raw, repeated)
                if ok:
                    counts["subset_calls"] += 1
                    self.check_result(check, res, scope, judge, raw, must_be_minimal=minimal)
                else:
                    self.after_crash(f, judge, raw)
        if muses:
            chosen = rng.sample(muses, min(SUBSET_MUS_CAP, len(muses)))
            for m in chosen:
                want = list(m)
                shuffled = list(m)
                rng.shuffle(shuffled)
                for check, fn in (
                    ("whole_deletion", lambda: self.shared.deletion(shuffled)),
                    ("whole_quickxplain", lambda: self.shared.quickxplain(shuffled)),
                    ("whole_deletion_nocore",
                     lambda: self.shared.deletion(shuffled, use_core=False)),
                    ("whole_quickxplain_nocore",
                     lambda: self.shared.quickxplain(shuffled, use_core=False)),
                    ("whole_core", lambda: self.shared.core(shuffled)),
                ):
                    ok, res = self.call(check, fn, raw)
                    if ok:
                        counts["steps"] += 1
                        counts["subset_mus_returned_whole"] += 1
                        if res != want:
                            self.bad(check, raw, f"subset {shuffled} is a MUS, returned {res}")
                    else:
                        self.after_crash(f, judge, raw)

    # -- is_unsat -----------------------------------------------------------

    def check_is_unsat(self, clauses, raw, judge):
        n = len(clauses)
        for _ in range(4):
            sub = [i for i in range(n) if self.rng.random() < self.rng.choice((0.3, 0.7, 0.95))]
            ok, got = self.call("is_unsat", lambda: self.shared.is_unsat(sub), raw)
            if not ok:
                continue
            want = not judge.sat(sub)
            self.counts["is_unsat_true" if want else "is_unsat_false"] += 1
            if got is not want:
                self.bad("is_unsat", raw, f"subset {sub}: said {got}, oracle says {want}")

    # -- verify -------------------------------------------------------------

    def check_verify(self, f, clauses, raw, judge, results):
        rng = self.rng
        n = len(clauses)
        tests = [[i for i in range(n) if rng.random() < 0.5], list(range(n))]
        if results:
            m = next(iter(results.values()))
            if m:
                tests.append(list(m))                       # a MUS
                tests.append(list(m)[1:])                   # a MUS less one
                tests.append(list(m) + [m[0]])              # a repeated index
                others = [i for i in range(n) if i not in m]
                if others:
                    tests.append(list(m) + [rng.choice(others)])  # a MUS plus one
        for sub in tests:
            ex = self.shared
            before = getattr(ex, "calls", 0)
            scope = set(sub)
            ok, got = self.call("verify", lambda s=sub: ex.verify(s), raw, len(sub) != len(scope))
            if not ok:
                self.after_crash(f, judge, raw)
                continue
            spent = getattr(ex, "calls", 0) - before
            verdict, msg = got
            is_mus = bool(scope) and judge.is_mus(scope)
            if verdict is not is_mus:
                self.bad("verify", raw, f"verify({sub}) said {got}; oracle says {is_mus}")
                continue
            if len(sub) != len(scope):
                self.counts["verify_repeated_index"] += 1
            if is_mus:
                self.counts["verify_true"] += 1
                # a subset is a set, so a repeat costs nothing
                if spent != len(set(sub)) + 1:
                    self.bad("verify_cost", raw,
                             f"verify({sub}) spent {spent} calls, "
                             f"documented {len(set(sub)) + 1}")
            elif judge.sat(scope):
                self.counts["verify_satisfiable"] += 1
                if "satisfiable" not in msg:
                    self.bad("verify_message", raw, f"verify({sub}): {msg}")
            else:
                self.counts["verify_redundant"] += 1
                named = re.search(r"clause (\d+) is redundant", msg)
                if not named:
                    self.bad("verify_message", raw, f"verify({sub}): {msg}")
                elif judge.sat(scope - {int(named.group(1))}):
                    self.bad("verify_message", raw,
                             f"verify({sub}) names a necessary clause: {msg}")

    # -- what the docstrings say a call costs: observed, not a soundness matter

    def check_call_docs(self, f, raw, unsat):
        if not unsat:
            return
        ex = self.fresh(f)
        ok, res = self.call("ex_deletion_core", lambda: ex.deletion(), raw)
        if ok and res:
            self.count_call_doc(ex, res)

    def count_call_doc(self, ex, res):
        """mus-2: "Exactly |M| solver calls after the initial core"."""
        extra = getattr(ex, "calls", 0) - 1 - len(res)
        self.counts["doc_deletion_calls_exactly_M" if extra == 0
                    else "doc_deletion_calls_more_than_M"] += 1

    # -- the command line ---------------------------------------------------

    def cli_run(self, argv):
        buf = io.StringIO()
        with contextlib.redirect_stdout(buf):
            rc = self.t.cli(argv)
        return rc, buf.getvalue()

    def check_cli(self, raw, clauses, nvars_decl, judge, unsat):
        counts = self.counts
        path = os.path.join(self.tmp, "f.cnf")
        with open(path, "w", encoding="ascii") as fh:
            fh.write(dimacs_text(raw, nvars_decl))
        for method in ("deletion", "quickxplain", "core"):
            for flag in ([], ["--verify"]):
                check = f"cli_{method}"
                try:
                    rc, out = self.cli_run(["mus", path, "--method", method, *flag])
                except Exception as e:  # noqa: BLE001
                    self.bad(check + ":raised", raw, f"{type(e).__name__}: {e}")
                    continue
                counts[check] += 1
                counts["steps"] += 1
                if not unsat:
                    counts["cli_satisfiable"] += 1
                    if rc != 10 or "s SATISFIABLE" not in out:
                        self.bad(check + ":sat", raw, f"exit {rc}: {out!r}")
                    continue
                shown = cli_clauses(out)
                if method == "core" and flag and rc == 1:
                    # `--verify` is documented as checking minimality, and a core
                    # is documented as not minimal: only right when it is not.
                    counts["cli_core_verify_not_minimal"] += 1
                    if "redundant" not in out:
                        self.bad(check + ":verify", raw, f"exit 1 without a reason: {out!r}")
                    continue
                if rc != 20 or "s UNSATISFIABLE" not in out:
                    self.bad(check + ":exit", raw, f"exit {rc}: {out!r}")
                    continue
                res = [i for i, _ in shown]
                for i, lits in shown:
                    if not 0 <= i < len(clauses) or set(lits) != set(clauses[i]):
                        self.bad(check + ":body", raw,
                                 f"printed clause {i} as {lits}, it is "
                                 f"{clauses[i] if 0 <= i < len(clauses) else None}")
                self.check_result(check + "_set", res, range(len(clauses)), judge, raw,
                                  must_be_minimal=method != "core")
                if flag:
                    counts["cli_verify_ok"] += 1
                    if "c verified" not in out:
                        self.bad(check + ":verify", raw, f"no verdict printed: {out!r}")


def cli_clauses(out):
    shown = []
    for line in out.splitlines():
        m = re.match(r"c   clause (\d+):(.*)$", line)
        if m:
            toks = [int(t) for t in m.group(2).split()]
            shown.append((int(m.group(1)), toks[:-1]))
    return shown


def dimacs_text(raw, nvars_decl):
    lines = [f"p cnf {nvars_decl} {len(raw)}"]
    lines.extend(" ".join(map(str, [*c, 0])) for c in raw)
    return "\n".join(lines) + "\n"


def build(raw, nvars_decl, rng):
    """Half through CNF.add_dimacs, half through the parser."""
    if rng.random() < 0.5:
        f = CNF(nvars_decl)
        for c in raw:
            f.add_dimacs(c)
        return f
    return parse_dimacs(dimacs_text(raw, nvars_decl))


# -- formulas: DIMACS literals, tiny ---------------------------------------------

def signs(rng, vs):
    return [v if rng.random() < 0.5 else -v for v in vs]


def g_random(rng):
    n = rng.randint(2, 9)
    m = int(n * rng.uniform(2.5, 7))
    return [signs(rng, rng.sample(range(1, n + 1), min(n, rng.choice((1, 2, 2, 3, 3, 3)))))
            for _ in range(m)]


def g_small(rng):
    """Few variables and few clauses: rich in MUSes, and all of them enumerable."""
    n = rng.randint(1, 4)
    m = rng.randint(3, ENUM_MAX)
    return [signs(rng, rng.sample(range(1, n + 1), min(n, rng.choice((1, 1, 2, 2, 3)))))
            for _ in range(m)]


def g_random3(rng):
    """Dense 3-SAT: big enough that the solver's core is not already minimal."""
    n = rng.randint(7, 12)
    return [signs(rng, rng.sample(range(1, n + 1), 3)) for _ in range(int(n * rng.uniform(5, 8)))]


def g_planted_sat(rng):
    n = rng.randint(1, 12)
    a = {v: rng.random() < 0.5 for v in range(1, n + 1)}
    out = []
    for _ in range(rng.randint(0, 3 * n + 2)):
        vs = rng.sample(range(1, n + 1), min(n, rng.randint(1, 3)))
        c = signs(rng, vs)
        if not any((l > 0) == a[abs(l)] for l in c):
            c[0] = -c[0]
        out.append(c)
    return out


def chain(start, k):
    """x1, x1 -> x2, ..., ~xk: a MUS of size k + 1."""
    vs = list(range(start, start + k))
    out = [[vs[0]]]
    out.extend([-a, b] for a, b in zip(vs, vs[1:]))
    out.append([-vs[-1]])
    return out


def all_signs(start, k):
    """Every sign pattern over k variables: a MUS of size 2**k."""
    out = []
    for m in range(1 << k):
        out.append([(start + i) if m >> i & 1 else -(start + i) for i in range(k)])
    return out


def parity_cycle(start, k):
    """x1+x2, x2+x3, ..., xk+x1 with an odd sum of constants: Tseitin on a cycle."""
    out = []
    for i in range(k):
        a, b = start + i, start + (i + 1) % k
        if i == 0:   # a = b
            out += [[-a, b], [a, -b]]
        else:        # a != b or a = b; the odd total comes from k's parity below
            if (k % 2 == 0) == (i == 1):
                out += [[a, b], [-a, -b]]
            else:
                out += [[-a, b], [a, -b]]
    return out


def php(holes):
    """holes + 1 pigeons in ``holes`` holes: minimally unsatisfiable."""
    var = lambda p, h: p * holes + h + 1
    out = [[var(p, h) for h in range(holes)] for p in range(holes + 1)]
    for h in range(holes):
        for p in range(holes + 1):
            for q in range(p + 1, holes + 1):
                out.append([-var(p, h), -var(q, h)])
    return out


def g_chain(rng):
    return chain(1, rng.randint(1, 9))


def g_disjoint(rng):
    """Independent contradictions: as many MUSes as parts, of chosen sizes."""
    start, out = 1, []
    for _ in range(rng.randint(2, 3)):
        k = rng.randint(1, 4)
        out += chain(start, k)
        start += k
    return out


def g_overlap(rng):
    """Two routes through a chain: MUSes sharing clauses, of different sizes."""
    k = rng.randint(3, 6)
    out = chain(1, k)
    for _ in range(rng.randint(1, 2)):
        a = rng.randint(1, k - 1)
        b = rng.randint(a + 1, k)
        out.append([-a, b])
    return out


def g_all_signs(rng):
    return all_signs(1, rng.randint(1, 4))


def g_parity(rng):
    return parity_cycle(1, rng.randint(3, 8))


def g_php(rng):
    return php(rng.randint(2, 3))


def g_sat_padding(rng, base):
    top = max((abs(l) for c in base for l in c), default=0)
    room = oracle.MAX_VARS - top
    if room <= 0:
        return base
    fresh = list(range(top + 1, top + 1 + min(room, 3)))
    return base + [signs(rng, rng.sample(fresh, min(len(fresh), rng.randint(1, 2))))
                   for _ in range(rng.randint(1, 4))]


def unsat_base(rng):
    return rng.choice((g_chain, g_overlap, g_disjoint, g_all_signs, g_parity))(rng)


def g_duplicates(rng):
    """Copies of clauses, reordered and with repeated literals."""
    base = unsat_base(rng)
    out = []
    for c in base:
        out.append(list(c))
        for _ in range(rng.choice((0, 0, 1, 2))):
            copy = list(c)
            rng.shuffle(copy)
            if copy and rng.random() < 0.3:
                copy.append(rng.choice(copy))
            out.append(copy)
    return out


def g_empty(rng):
    """The empty clause, alone or beside other MUSes and satisfiable clauses."""
    base = rng.choice((g_chain, g_small, g_planted_sat))(rng)
    return base + [[] for _ in range(rng.randint(1, 3))]


def g_trivial(rng):
    return rng.choice((
        [], [[]], [[], []], [[1]], [[1], [-1]], [[1, -1]], [[1, -1], [2, -2]],
        [[1, -1], []], [[1, 1]], [[1], [1], [-1]], [[1], [1], [-1], [-1]],
        [[], [1], [-1]], [[1, 2], [1, 2], [2, 1], [-1], [-2]],
    ))


def g_tautologies(rng):
    """CNF.add drops tautologies, so the indices shift: the harness must follow."""
    base = rng.choice((g_chain, g_small, g_planted_sat))(rng)
    top = max((abs(l) for c in base for l in c), default=1)
    out = list(base)
    for _ in range(rng.randint(1, 3)):
        v = rng.randint(1, top)
        out.insert(rng.randint(0, len(out)), [v, -v] if rng.random() < 0.5 else [-v, 1, v])
    return out


SHAPES = (
    g_random, g_random3, g_small, g_small, g_planted_sat, g_chain, g_disjoint, g_overlap,
    g_all_signs, g_parity, g_php, g_duplicates, g_empty, g_trivial, g_tautologies,
)


def make_instance(rng):
    raw = rng.choice(SHAPES)(rng)
    raw = [list(c) for c in raw]
    if rng.random() < 0.3:
        raw = g_sat_padding(rng, raw)
    top = max((abs(l) for c in raw for l in c), default=0)
    if rng.random() < 0.5 and top:              # rename the variables
        perm = list(range(1, top + 1))
        rng.shuffle(perm)
        raw = [[perm[abs(l) - 1] * (1 if l > 0 else -1) for l in c] for c in raw]
    if rng.random() < 0.8:
        rng.shuffle(raw)
    for c in raw:
        if rng.random() < 0.3:
            rng.shuffle(c)
    extra = rng.randint(1, 3) if rng.random() < 0.15 and top + 3 <= oracle.MAX_VARS else 0
    return raw, top + extra


# -- past the oracle: enough search to reach restarts, reductions and walks ------

def hard_instances(rng, count):
    """Judged by campaign.dpll, so the variable limit does not apply.

    PHP(7,6) is the one that spends enough conflicts in a single solver for
    clause reductions and probSAT walks to fire; see REQUIRED.
    """
    out = [php(7)] if count else []
    for i in range(count - 1):
        if i % 2:
            out.append(php(5))
        else:
            n = 60
            out.append([signs(rng, rng.sample(range(1, n + 1), 3)) for _ in range(n * 5)])
    return out


def check_hard(run, raw):
    """Every method on one shared extractor, so its solver keeps its state."""
    clauses = normalise(raw)
    f = CNF(0)
    for c in raw:
        f.add_dimacs(c)
    judge = Judge(clauses, run.counts)
    everything = range(len(clauses))
    run.counts["instances_hard"] += 1
    ex = run.t.extractor(f)
    ok, core = run.call("hard_core", lambda: ex.core(), raw)
    if ok:
        run.check_result("hard_core", core, everything, judge, raw, must_be_minimal=False)
    first = None
    methods = [
        ("hard_deletion", lambda: ex.deletion()),
        ("hard_quickxplain", lambda: ex.quickxplain()),
    ]
    if len(clauses) < 150:      # PHP(7,6) has spent its budget by now
        methods += [
            ("hard_deletion_nocore", lambda: ex.deletion(use_core=False)),
            ("hard_quickxplain_nocore", lambda: ex.quickxplain(use_core=False)),
        ]
    for check, fn in methods:
        ok, res = run.call(check, fn, raw)
        if ok:
            run.check_result(check, res, everything, judge, raw)
            first = res if first is None else first
    if ok and core and first and len(core) > len(first):
        run.counts["core_not_minimal"] += 1
    run.absorb(ex)


# -- a run ------------------------------------------------------------------------

def run_all(target, seed, instances, hard):
    rng = random.Random(seed)
    run = Run(target, rng)
    with tempfile.TemporaryDirectory() as tmp:
        run.tmp = tmp
        for _ in range(instances):
            raw, nvars = make_instance(rng)
            run.check_instance(raw, nvars)
    for raw in hard_instances(rng, hard):
        check_hard(run, raw)
    return run


def zero_categories(counts):
    return [c for c in REQUIRED if not counts[c]]


# -- self-test: the harness must catch wrong code ----------------------------------

def ex_stub(**overrides):
    return type("Stub", (MUSExtractor,), overrides)


def stub_mus_of(extractor):
    def mus(f, method="deletion"):
        ex = extractor(f)
        if method == "deletion":
            return ex.deletion()
        if method == "quickxplain":
            return ex.quickxplain()
        raise ValueError(method)
    return mus


def _everything(self, subset=None, use_core=True):
    cands = list(range(len(self.selectors))) if subset is None else sorted(set(subset))
    return cands if self.is_unsat(cands) else []


def _less_one(self, subset=None, use_core=True):
    return MUSExtractor.deletion(self, subset, use_core)[1:]


def _plus_one(self, subset=None, use_core=True):
    res = MUSExtractor.deletion(self, subset, use_core)
    others = [i for i in range(len(self.selectors)) if i not in res]
    return sorted(res + others[:1]) if res else res


def _ignores_subset(self, subset=None, use_core=True):
    return MUSExtractor.deletion(self, None, use_core)


def _flaky_is_unsat(self, subset):
    got = MUSExtractor.is_unsat(self, subset)
    return not got if len(subset) % 7 == 3 else got


def _qx_nocore_only(self, subset=None, use_core=True):
    if use_core:
        return MUSExtractor.quickxplain(self, subset, use_core)
    return _everything(self, subset)


def _cli_wrong_exit(argv):
    cdclkit_cli.main(argv)
    return 0


def _cli_core_as_minimal(argv):
    """Answers every method with the unminimised core."""
    argv = list(argv)
    argv[argv.index("--method") + 1] = "core"
    if "--verify" in argv:
        argv.remove("--verify")
    return cdclkit_cli.main(argv)


def _accepts_any_method(f, method="deletion"):
    return real_mus(f, method if method == "quickxplain" else "deletion")


def matches(check, needle):
    """A hit on the check itself. mus-1 raises on real code, and must not count."""
    if check.endswith(":raised"):
        return False
    return check == needle or check.endswith(needle) or check.startswith(needle + ":")


def self_test(seed):
    def with_extractor(**overrides):
        cls = ex_stub(**overrides)
        return Target(extractor=cls, mus=stub_mus_of(cls))

    def real_ex_only(**overrides):
        return Target(extractor=ex_stub(**overrides))

    empties = lambda *a, **k: []
    stubs = {
        "everything": (with_extractor(deletion=_everything, quickxplain=_everything),
                       ":not_minimal"),
        "nothing": (with_extractor(deletion=empties, quickxplain=empties), ":empty_on_unsat"),
        "less_one": (with_extractor(deletion=_less_one), ":result_satisfiable"),
        "plus_one": (with_extractor(deletion=_plus_one), ":not_minimal"),
        "nonempty_on_sat": (Target(mus=lambda f, method="deletion": [0] if f.clauses else []),
                            ":nonempty_on_sat"),
        "ignores_subset": (with_extractor(deletion=_ignores_subset), ":outside_scope"),
        "qx_nocore_only": (real_ex_only(quickxplain=_qx_nocore_only),
                           "ex_quickxplain_nocore:not_minimal"),
        "verify_always_yes": (real_ex_only(verify=lambda self, s: (True, "ok")), "verify"),
        "verify_always_no": (real_ex_only(verify=lambda self, s: (False, "no")), "verify"),
        "flaky_is_unsat": (real_ex_only(is_unsat=_flaky_is_unsat), "is_unsat"),
        "core_drops_a_clause": (real_ex_only(core=lambda self, subset=None:
                                             MUSExtractor.core(self, subset)[1:]), "ex_core"),
        "shrink_core_only": (Target(shrink_core=lambda f: []), "shrink_core"),
        "mus_accepts_any_method": (Target(mus=_accepts_any_method), "mus_unknown_method"),
        "cli_wrong_exit": (Target(cli=_cli_wrong_exit), "cli_deletion"),
        "cli_core_as_minimal": (Target(cli=_cli_core_as_minimal), "cli_deletion_set:not_minimal"),
    }
    failed = 0
    for name, (target, needle) in stubs.items():
        run = run_all(target, seed, 60, 0)
        hits = sum(v for k, v in run.by_check.items() if matches(k, needle))
        verdict = "flagged" if hits else "NOT FLAGGED"
        failed += not hits
        print(f"  stub {name:24s} {verdict}: {hits} on checks containing {needle!r} "
              f"({run.total_mismatches} in all)")
    # a run too short to reach the corner must not read as evidence
    run = run_all(Target(), seed, 1, 0)
    zeros = zero_categories(run.counts)
    print(f"  one instance, no hard tier: {len(zeros)} categories at zero "
          f"({'fails the run' if zeros else 'NOT FLAGGED'})")
    failed += not zeros
    print("self-test: " + ("FAILED" if failed else "every stub was flagged"))
    return 1 if failed else 0


# -- entry --------------------------------------------------------------------------

FINDINGS = [
    {"id": "mus-1", "severity": "Bug",
     "summary": "A repeated index in subset= (or a repeated assumption in Solver.solve) "
                "raises IndexError, and the same extractor then returns a satisfiable "
                "set that verify() endorses"},
    {"id": "mus-2", "severity": "Note",
     "summary": "mus.py says deletion makes exactly |M| calls after the core; it makes "
                "|core|, which differs when the core is not minimal"},
    {"id": "mus-3", "severity": "Note",
     "summary": "cdclkit mus --method core --verify exits 1 and prints no clauses on a "
                "correct but non-minimal core; consistent with its help text"},
]

OBSERVATIONS = [
    "Indices count CNF.clauses, so a tautology in the input, which CNF.add documents "
    "dropping, shifts them against the file's own clause numbering. The CLI prints each "
    "clause's body, and the harness checks the body against the index.",
]

NOT_CHECKED = [
    "negative and out-of-range indices in subset= and verify(): undocumented",
    "MUSExtractor constructed on a CNF whose nvars was lowered by hand or whose "
    ".clauses was assigned directly: selector variables would collide; outside "
    "CNF's normalising interface",
    "a CNF mutated after the extractor was built",
    "the native engine: mus uses the Python Solver only, there is no native MUS path",
    "formulas past the hard tier's 60 variables, and any claim about call counts "
    "(QuickXplain's O(|M| log(|F|/|M|))) beyond verify's cost and deletion's",
    "minimum (smallest) MUS: documented as not attempted",
    "Solver Config variations: MUSExtractor exposes no config parameter",
]


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--seed", type=int, default=20261108)
    ap.add_argument("--instances", type=int, default=1000)
    ap.add_argument("--hard", type=int, default=3, help="instances past 16 variables")
    ap.add_argument("--self-test", action="store_true")
    ap.add_argument("--write", action="store_true", help="write campaign/results/mus.json")
    args = ap.parse_args(argv)
    if args.self_test:
        return self_test(args.seed)

    t0 = time.perf_counter()
    cpu0 = time.process_time()
    run = run_all(Target(), args.seed, args.instances, args.hard)
    dt = time.perf_counter() - t0
    cpu = time.process_time() - cpu0

    print(f"instances {run.counts['instances']} + hard {run.counts['instances_hard']}, "
          f"seed {args.seed}, {dt:.1f}s wall, {cpu:.1f}s cpu, checks judged {run.counts['steps']}")
    for k in sorted(run.counts):
        print(f"  {k:44s} {run.counts[k]}")
    zeros = zero_categories(run.counts)
    print(f"mismatches: {run.total_mismatches}  by finding: {dict(run.by_label)}")
    labels = {k: v for k, v in run.by_label.items() if k != "UNEXPLAINED"}
    regressions, still_open = status.split(labels)
    for label in sorted(regressions):
        print(f"REGRESSION {label}: {regressions[label]} mismatches")
    for k, v in run.by_check.most_common():
        print(f"  {k}: {v}")
    for m in run.mismatches[:8]:
        print("  e.g.", json.dumps(m))
    if zeros:
        print("CATEGORIES AT ZERO:", ", ".join(zeros))

    if args.write:
        os.makedirs("campaign/results", exist_ok=True)
        with open("campaign/results/mus.json", "w", encoding="ascii") as fh:
            json.dump({
                "corner": "mus",
                "seeds": [args.seed],
                "instances": run.counts["instances"] + run.counts["instances_hard"],
                "steps": run.counts["steps"],
                "per_category_counts": dict(sorted(run.counts.items())),
                "runtime_seconds": round(dt, 1),
                "cpu_seconds": round(cpu, 1),
                "mismatches": run.total_mismatches,
                "mismatches_by_finding": dict(run.by_label),
                "regressions": regressions,
                "findings": [{**f, "status": status.state(f["id"])} for f in FINDINGS],
                "observations": OBSERVATIONS,
                "not_checked": NOT_CHECKED,
            }, fh, indent=2)
            fh.write("\n")
    return 1 if regressions or run.by_label["UNEXPLAINED"] or zeros else 0


if __name__ == "__main__":
    sys.exit(main())
