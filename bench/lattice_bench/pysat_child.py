"""Runs one PySAT solver on one CNF with a time limit; prints one JSON line.

    python -m lattice_bench.pysat_child minisat22 file.cnf 300

Only the search is timed: reading the file and loading the clauses into the solver are not
(Lattice's own time likewise starts after parsing).
"""
from __future__ import annotations

import json
import sys
import threading
import time
from pathlib import Path

from pysat.solvers import Solver

from lattice_bench.run import read_clauses


def main():
    name, path, limit = sys.argv[1], sys.argv[2], float(sys.argv[3])
    clauses = read_clauses(Path(path))
    if name == "minisat22":
        # PySAT's MiniSat 2.2 build segfaults inside solve() on formulas whose variable numbers have
        # large gaps (e.g. 1,157 used out of 58,317 declared). Renumbering the variables 1..n keeps
        # the formula equisatisfiable and avoids the crash; the model is checked on these clauses.
        ids: dict[int, int] = {}
        clauses = [[ids.setdefault(abs(lit), len(ids) + 1) * (1 if lit > 0 else -1) for lit in c] for c in clauses]
    with Solver(name=name, bootstrap_with=clauses, use_timer=False) as s:
        timer = threading.Timer(limit, s.interrupt)
        timer.start()
        t0 = time.perf_counter()
        res = s.solve_limited(expect_interrupt=True)
        secs = time.perf_counter() - t0
        timer.cancel()
        status = {True: "sat", False: "unsat", None: "unknown"}[res]
        out = {"status": status, "seconds": secs}
        if res:
            model = set(l for l in s.get_model())
            out["model_ok"] = all(any(l in model for l in c) for c in clauses)
        print(json.dumps(out))


if __name__ == "__main__":
    main()
