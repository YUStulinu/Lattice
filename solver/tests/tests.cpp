// Solver tests: random formulas against brute force, structured UNSAT families, model checks,
// with and without preprocessing and with each restart policy.
#include <cstdio>
#include <random>
#include <vector>

#include "solver.hpp"

using namespace lattice;

static int failures = 0;
#define CHECK(cond, ...)                                     \
    do {                                                     \
        if (!(cond)) {                                       \
            std::printf("FAIL %s:%d: ", __FILE__, __LINE__); \
            std::printf(__VA_ARGS__);                        \
            std::printf("\n");                               \
            failures++;                                      \
        }                                                    \
    } while (0)

using Cnf = std::vector<std::vector<int>>;

static bool brute_force(const Cnf& f, int n) {
    for (uint64_t m = 0; m < (uint64_t{1} << n); m++) {
        bool all = true;
        for (const auto& c : f) {
            bool sat = false;
            for (int x : c)
                if (((m >> (std::abs(x) - 1)) & 1) == (x > 0 ? 1u : 0u)) sat = true;
            if (!sat) {
                all = false;
                break;
            }
        }
        if (all) return true;
    }
    return false;
}

static Result run(const Cnf& f, Options o, Solver** keep = nullptr) {
    auto* s = new Solver(o);
    for (const auto& c : f) {
        std::vector<Lit> ls;
        for (int x : c) ls.push_back(from_dimacs(x));
        s->add_clause(ls);
    }
    const Result r = s->solve();
    if (r == Result::Sat) {
        for (const auto& c : f) {
            bool sat = false;
            for (int x : c)
                if (s->model_value(static_cast<Var>(std::abs(x) - 1)) == (x > 0)) sat = true;
            if (!sat) {
                CHECK(false, "model violates a clause");
                break;
            }
        }
    }
    if (keep) {
        *keep = s;
    } else {
        delete s;
    }
    return r;
}

static Cnf random_ksat(std::mt19937& rng, int n, int m, int k) {
    Cnf f;
    std::uniform_int_distribution<int> v(1, n);
    for (int i = 0; i < m; i++) {
        std::vector<int> c;
        while (static_cast<int>(c.size()) < k) {
            int x = v(rng);
            bool dup = false;
            for (int y : c)
                if (std::abs(y) == x) dup = true;
            if (!dup) c.push_back(rng() & 1 ? x : -x);
        }
        f.push_back(c);
    }
    return f;
}

// n+1 pigeons in n holes: unsatisfiable, and hard for resolution.
static Cnf pigeonhole(int n) {
    Cnf f;
    auto p = [&](int i, int j) { return i * n + j + 1; };
    for (int i = 0; i <= n; i++) {
        std::vector<int> c;
        for (int j = 0; j < n; j++) c.push_back(p(i, j));
        f.push_back(c);
    }
    for (int j = 0; j < n; j++)
        for (int a = 0; a <= n; a++)
            for (int b = a + 1; b <= n; b++) f.push_back({-p(a, j), -p(b, j)});
    return f;
}

int main() {
    std::mt19937 rng(42);
    // Random 3-SAT near the threshold (ratio 4.26); small formulas lean towards SAT.
    int sat = 0, unsat = 0;
    for (int t = 0; t < 400; t++) {
        const int n = 8 + static_cast<int>(rng() % 13);
        const Cnf f = random_ksat(rng, n, static_cast<int>(n * 4.26 + 0.5), 3);
        const bool truth = brute_force(f, n);
        for (int variant = 0; variant < 4; variant++) {
            Options o;
            o.elim = variant % 2 == 0;
            o.restarts = variant < 2 ? Restarts::Auto : (variant == 2 ? Restarts::Luby : Restarts::Glucose);
            const Result r = run(f, o);
            CHECK((r == Result::Sat) == truth && r != Result::Unknown, "random 3-SAT #%d (n=%d, variant %d): got %d, truth %d", t, n, variant,
                  static_cast<int>(r), truth);
        }
        truth ? sat++ : unsat++;
    }
    CHECK(sat > 50 && unsat > 50, "the random set should mix SAT (%d) and UNSAT (%d)", sat, unsat);
    // Bigger random formulas: SAT side (ratio 4.0) checked through the model, UNSAT side (ratio
    // 5.5) by agreement of all variants.
    for (int t = 0; t < 20; t++) {
        const Cnf f = random_ksat(rng, 150, 600, 3);
        CHECK(run(f, Options{}) != Result::Unknown, "random 150 vars");
        const Cnf g = random_ksat(rng, 60, 330, 3);
        Options no;
        no.elim = false;
        CHECK(run(g, Options{}) == run(g, no), "elim changes the answer on an unsat-side formula");
    }
    for (int n = 4; n <= 8; n++) {
        CHECK(run(pigeonhole(n), Options{}) == Result::Unsat, "pigeonhole %d", n);
        Options no;
        no.elim = false;
        CHECK(run(pigeonhole(n), no) == Result::Unsat, "pigeonhole %d without elimination", n);
    }
    // Edge cases: empty formula, empty clause, units, a variable that never occurs.
    CHECK(run({}, Options{}) == Result::Sat, "empty formula");
    CHECK(run({{1}, {-1}}, Options{}) == Result::Unsat, "x and not x");
    CHECK(run({{1, 2}, {-1}, {-2, 3}, {5}}, Options{}) == Result::Sat, "units and a gap in numbering");
    CHECK(run({{1, -1}}, Options{}) == Result::Sat, "tautology only");
    // Long chains of implications (lots of propagation, few decisions).
    Cnf chain;
    for (int i = 1; i < 3000; i++) chain.push_back({-i, i + 1});
    chain.push_back({1});
    chain.push_back({-3000});
    CHECK(run(chain, Options{}) == Result::Unsat, "implication chain");
    if (failures) {
        std::printf("%d failures\n", failures);
        return 1;
    }
    std::printf("all tests passed (%d SAT, %d UNSAT random formulas, each in 4 configurations)\n", sat, unsat);
    return 0;
}
