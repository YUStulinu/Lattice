"""Small puzzles as CNF, and solver traces of them for the web visualisation.

    python -m lattice_bench.puzzles

* Sudoku: variable x(r, c, d) "cell (r, c) holds digit d". Puzzles are made here with the
  solver itself: a random full grid, then clues removed while the solution stays unique
  (checked by asking the solver for a second solution).
* N queens: x(r, c) "a queen on (r, c)"; one per row, at most one per column and diagonal.
* Pigeonhole 6 into 5: unsatisfiable, so the trace ends in a refutation.

Writes web/public/traces/<name>.json: the puzzle, the variable labels and the solver's events.
"""
from __future__ import annotations

import json
import random
import re
import subprocess
import tempfile
from itertools import combinations
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
OUT = ROOT / "web" / "public" / "traces"


def lattice() -> str:
    for c in ["build-viz/Release/lattice.exe", "build/Release/lattice.exe", "build/lattice"]:
        if (ROOT / c).exists():
            return str(ROOT / c)
    raise FileNotFoundError("build the solver first")


def solve(clauses: list[list[int]], nvars: int, trace: Path | None = None) -> list[int] | None:
    with tempfile.TemporaryDirectory() as d:
        f = Path(d) / "f.cnf"
        f.write_text(f"p cnf {nvars} {len(clauses)}\n" + "".join(" ".join(map(str, c)) + " 0\n" for c in clauses))
        args = [lattice(), "--no-elim", str(f)]  # no elimination: every variable stays visible
        if trace:
            args[2:2] = ["--trace", str(trace)]
        out = subprocess.run(args, capture_output=True, text=True).stdout
    if "s SATISFIABLE" not in out:
        return None
    return [int(x) for line in out.splitlines() if line.startswith("v ") for x in line[2:].split() if x != "0"]


# ---------------------------------------------------------------- Sudoku


def sx(r: int, c: int, d: int) -> int:
    return 81 * r + 9 * c + d + 1


def sudoku_cnf(givens: list[int]) -> list[list[int]]:
    cl = []
    for r in range(9):
        for c in range(9):
            cl.append([sx(r, c, d) for d in range(9)])
            cl += [[-sx(r, c, a), -sx(r, c, b)] for a, b in combinations(range(9), 2)]
    groups = [[(r, c) for c in range(9)] for r in range(9)] + [[(r, c) for r in range(9)] for c in range(9)]
    groups += [[(3 * br + i, 3 * bc + j) for i in range(3) for j in range(3)] for br in range(3) for bc in range(3)]
    for g in groups:
        for d in range(9):
            cl.append([sx(r, c, d) for r, c in g])
            cl += [[-sx(*a, d), -sx(*b, d)] for a, b in combinations(g, 2)]
    for i, v in enumerate(givens):
        if v:
            cl.append([sx(i // 9, i % 9, v - 1)])
    return cl


def grid_of(model: list[int]) -> list[int]:
    g = [0] * 81
    for lit in model:
        if 0 < lit <= 729:
            k = lit - 1
            g[k // 9] = k % 9 + 1
    return g


def unique(givens: list[int]) -> bool:
    m = solve(sudoku_cnf(givens), 729)
    if m is None:
        return False
    sol = grid_of(m)
    block = [-sx(i // 9, i % 9, sol[i] - 1) for i in range(81)]
    return solve(sudoku_cnf(givens) + [block], 729) is None


def make_sudoku(seed: int, target: int) -> tuple[list[int], list[int]]:
    rng = random.Random(seed)
    # A random full grid: random first row, the rest by the solver.
    first = list(range(1, 10))
    rng.shuffle(first)
    full = grid_of(solve(sudoku_cnf(first + [0] * 72), 729))
    givens = full[:]
    cells = list(range(81))
    rng.shuffle(cells)
    for i in cells:
        if sum(1 for v in givens if v) <= target:
            break
        keep = givens[i]
        givens[i] = 0
        if not unique(givens):
            givens[i] = keep
    return givens, full


# ---------------------------------------------------------------- queens, pigeons


def queens_cnf(n: int) -> list[list[int]]:
    q = lambda r, c: n * r + c + 1  # noqa: E731
    cl = [[q(r, c) for c in range(n)] for r in range(n)]
    cells = [(r, c) for r in range(n) for c in range(n)]
    for (r1, c1), (r2, c2) in combinations(cells, 2):
        if c1 == c2 or r1 == r2 or abs(r1 - r2) == abs(c1 - c2):
            cl.append([-q(r1, c1), -q(r2, c2)])
    return cl


def pigeon_cnf(holes: int) -> list[list[int]]:
    p = lambda i, j: holes * i + j + 1  # noqa: E731
    cl = [[p(i, j) for j in range(holes)] for i in range(holes + 1)]
    for j in range(holes):
        cl += [[-p(a, j), -p(b, j)] for a, b in combinations(range(holes + 1), 2)]
    return cl


def write_trace(name: str, title: str, kind: str, clauses: list[list[int]], nvars: int, labels: dict[int, str], extra: dict):
    OUT.mkdir(parents=True, exist_ok=True)
    with tempfile.TemporaryDirectory() as d:
        t = Path(d) / "trace.jsonl"
        model = solve(clauses, nvars, trace=t)
        events = [json.loads(line) for line in t.read_text().splitlines()]
    doc = {"name": name, "title": title, "kind": kind, "vars": nvars, "clauses": len(clauses), "labels": labels,
           "result": "sat" if model else "unsat", "events": events} | extra
    (OUT / f"{name}.json").write_text(json.dumps(doc, separators=(",", ":")))
    print(f"{name}: {len(clauses)} clauses, {len(events)} events, {doc['result']}")


def main():
    for name, title, seed, target in [("sudoku-easy", "Sudoku, 36 clues", 1, 36), ("sudoku-hard", "Sudoku, as few clues as unique allows", 7, 17)]:
        givens, full = make_sudoku(seed, target)
        labels = {sx(r, c, d): f"r{r + 1}c{c + 1}={d + 1}" for r in range(9) for c in range(9) for d in range(9)}
        write_trace(name, f"{title} ({sum(1 for v in givens if v)} given)", "sudoku", sudoku_cnf(givens), 729, labels, {"givens": givens, "solution": full})
    for n in [8, 16]:
        labels = {n * r + c + 1: f"Q({r + 1},{c + 1})" for r in range(n) for c in range(n)}
        write_trace(f"queens-{n}", f"{n} queens", "queens", queens_cnf(n), n * n, labels, {"n": n})
    holes = 5
    labels = {holes * i + j + 1: f"P{i + 1}→H{j + 1}" for i in range(holes + 1) for j in range(holes)}
    write_trace("pigeons-6-5", "6 pigeons, 5 holes (unsatisfiable)", "pigeons", pigeon_cnf(holes), (holes + 1) * holes, labels, {"pigeons": holes + 1, "holes": holes})


if __name__ == "__main__":
    main()
