"""Tests of the benchmark tooling: encoders, model checking, summaries (no downloads needed)."""
from __future__ import annotations

import itertools
import shutil
from pathlib import Path

import pytest

from lattice_bench import puzzles, report, run


def brute(clauses: list[list[int]], n: int):
    for bits in itertools.product([False, True], repeat=n):
        if all(any(bits[abs(l) - 1] == (l > 0) for l in c) for c in clauses):
            return bits
    return None


def test_queens_and_pigeons_encodings():
    # 4 queens has solutions; 3 queens has none; 3 pigeons in 2 holes cannot fit.
    assert brute(puzzles.queens_cnf(4), 16) is not None
    assert brute(puzzles.queens_cnf(3), 9) is None
    assert brute(puzzles.pigeon_cnf(2), 6) is None
    sol = brute(puzzles.queens_cnf(5), 25)
    queens = [(i // 5, i % 5) for i, b in enumerate(sol) if b]
    assert len(queens) == 5
    for (r1, c1), (r2, c2) in itertools.combinations(queens, 2):
        assert r1 != r2 and c1 != c2 and abs(r1 - r2) != abs(c1 - c2)


def test_sudoku_encoding_size():
    cl = puzzles.sudoku_cnf([0] * 81)
    # 81 cells x (1 + 36) + 27 groups x 9 digits x (1 + 36)
    assert len(cl) == 81 * 37 + 27 * 9 * 37
    assert puzzles.sx(8, 8, 8) == 729


def test_model_check(tmp_path: Path):
    f = tmp_path / "f.cnf"
    f.write_text("c comment\np cnf 3 2\n1 -2 0\n2 3\n0\n")
    assert run.read_clauses(f) == [[1, -2], [2, 3]]
    assert run.model_ok(f, {1, 2, -3})
    assert not run.model_ok(f, {-1, 2, -3})


def test_summary_counts_and_par2():
    rows = [
        {"hash": "a", "family": "x", "solver": "lattice", "timeout": 10, "status": "sat", "seconds": 1, "model_ok": True},
        {"hash": "b", "family": "x", "solver": "lattice", "timeout": 10, "status": "unknown", "seconds": 10},
        {"hash": "c", "family": "y", "solver": "lattice", "timeout": 10, "status": "unsat", "seconds": 3, "proof": "verified", "check_seconds": 6, "proof_mb": 1.0},
    ]
    s = report.summarise(rows)["lattice"]
    assert (s["solved"], s["sat"], s["unsat"]) == (2, 1, 1)
    assert s["par2"] == pytest.approx((1 + 20 + 3) / 3, abs=0.1)
    assert s["proofs"]["verified"] == 1 and s["proofs"]["check_over_solve_median"] == 2.0
    assert report.per_family(rows, ["lattice"]) == {"x": {"instances": 2, "lattice": 1}, "y": {"instances": 1, "lattice": 1}}


@pytest.mark.skipif(not any((Path(__file__).resolve().parents[2] / p).exists() for p in ["build/Release/lattice.exe", "build/lattice"]),
                    reason="solver not built")
def test_solver_end_to_end_on_queens():
    m = puzzles.solve(puzzles.queens_cnf(8), 64)
    assert m is not None and sum(1 for x in m if x > 0) == 8
    assert puzzles.solve(puzzles.pigeon_cnf(4), 20) is None


def test_satlib_end_marker(tmp_path):
    from lattice_bench.run import read_clauses

    p = tmp_path / "uf.cnf"
    p.write_text("c x\np cnf 2 2\n 1 -2 0\n 2 0\n%\n0\n\n")
    assert read_clauses(p) == [[1, -2], [2]]
