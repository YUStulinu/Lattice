// Lattice: a CDCL SAT solver.
//
// Literals are unsigned integers 2v + s (s = 1 for the negation); variables count from 0 inside
// and from 1 in DIMACS. Clauses live in one arena of 32-bit words; a clause reference is an
// offset into it.
#pragma once

#include <cstdint>
#include <cstdio>
#include <string>
#include <vector>

namespace lattice {

using Lit = uint32_t;
using Var = uint32_t;
using CRef = uint32_t;
constexpr CRef kNoReason = 0xFFFFFFFFu;
constexpr Lit kNoLit = 0xFFFFFFFFu;

inline Lit mk_lit(Var v, bool neg) { return 2 * v + (neg ? 1 : 0); }
inline Var var(Lit l) { return l >> 1; }
inline bool sign(Lit l) { return l & 1; }
inline Lit neg(Lit l) { return l ^ 1; }
inline int to_dimacs(Lit l) { return sign(l) ? -static_cast<int>(var(l) + 1) : static_cast<int>(var(l) + 1); }
inline Lit from_dimacs(int x) { return x > 0 ? mk_lit(static_cast<Var>(x - 1), false) : mk_lit(static_cast<Var>(-x - 1), true); }

// A DRAT proof, in the binary or the text format.
class Proof {
  public:
    bool open(const std::string& path, bool binary);
    bool enabled() const { return f_ != nullptr; }
    void add(const Lit* lits, size_t n) { if (f_) write('a', lits, n); }
    void del(const Lit* lits, size_t n) { if (f_) write('d', lits, n); }
    void add(const std::vector<Lit>& c) { add(c.data(), c.size()); }
    void del(const std::vector<Lit>& c) { del(c.data(), c.size()); }
    void close();
    ~Proof() { close(); }
    uint64_t lines = 0;

  private:
    void write(char kind, const Lit* lits, size_t n);
    FILE* f_ = nullptr;
    bool binary_ = true;
    std::vector<char> buf_;
};

// Search trace for the visualisation (small problems only): one JSON object per line.
class Trace {
  public:
    bool open(const std::string& path);
    bool enabled() const { return f_ != nullptr && events < limit; }
    void event(const char* json);
    void close();
    ~Trace() { close(); }
    uint64_t events = 0, limit = 200000;

  private:
    FILE* f_ = nullptr;
};

enum class Restarts { Glucose, Luby, Auto };

struct Options {
    bool elim = true;  // bounded variable elimination and subsumption before search
    Restarts restarts = Restarts::Auto;
    double timeout = 0;  // seconds, 0 = none
    bool verbose = false;
    uint64_t seed = 0;
};

struct Stats {
    uint64_t decisions = 0, propagations = 0, conflicts = 0, restarts = 0, learnt_literals = 0, minimised_literals = 0;
    uint64_t reductions = 0, deleted = 0, elim_vars = 0, elim_resolvents = 0, subsumed = 0, strengthened = 0;
    double elim_seconds = 0, solve_seconds = 0;
};

enum class Result { Sat, Unsat, Unknown };

class Solver {
  public:
    explicit Solver(Options o = {}) : opt(o) {}
    // Formula input. Returns false if the formula became trivially unsatisfiable.
    void reserve_vars(Var n);
    bool add_clause(std::vector<Lit> lits);
    Result solve();
    // After Sat: value of a variable in the model (true/false).
    bool model_value(Var v) const { return model[v]; }
    Var num_vars() const { return static_cast<Var>(assigns.size()); }
    size_t num_original() const { return original.size(); }

    Options opt;
    Stats stats;
    Proof proof;
    Trace trace;
    std::vector<bool> model;
    std::vector<std::vector<Lit>> original;  // the input formula, kept to check the model

  private:
    // --- clause arena: [size][flags][activity][lits...]
    std::vector<uint32_t> arena;
    std::vector<CRef> clauses, learnts;
    uint64_t wasted = 0;
    uint32_t& csize(CRef c) { return arena[c]; }
    uint32_t& cflags(CRef c) { return arena[c + 1]; }
    float& cact(CRef c) { return reinterpret_cast<float&>(arena[c + 2]); }
    Lit* lits(CRef c) { return &arena[c + 3]; }
    bool learnt(CRef c) { return cflags(c) & 1; }
    bool deleted(CRef c) { return cflags(c) & 2; }
    bool used(CRef c) { return cflags(c) & 4; }
    uint32_t lbd(CRef c) { return cflags(c) >> 3; }
    void set_lbd(CRef c, uint32_t l) { cflags(c) = (cflags(c) & 7) | (l << 3); }
    CRef alloc(const std::vector<Lit>& ls, bool is_learnt);
    void remove_clause(CRef c);  // mark deleted, log to the proof
    bool locked(CRef c);
    bool satisfied(CRef c);

    // --- watches
    struct Watch {
        CRef cref;
        Lit blocker;
        bool binary;
    };
    std::vector<std::vector<Watch>> watches;  // watches[l]: clauses to visit when l becomes false
    void attach(CRef c);
    void rebuild_watches();
    void collect_garbage();

    // --- assignment
    std::vector<int8_t> vals;      // per literal: 1 true, -1 false, 0 unassigned
    std::vector<int8_t> assigns;   // per variable (unused but sizes the problem)
    std::vector<uint32_t> level;
    std::vector<CRef> reason;
    std::vector<Lit> trail;
    std::vector<uint32_t> trail_lim;
    size_t qhead = 0;
    uint32_t decision_level() const { return static_cast<uint32_t>(trail_lim.size()); }
    int8_t value(Lit l) const { return vals[l]; }
    void enqueue(Lit l, CRef from);
    CRef propagate();
    void backtrack(uint32_t lvl);

    // --- heuristics
    std::vector<double> activity;
    double var_inc = 1, var_decay = 0.8;
    std::vector<uint8_t> phase, eliminated;
    std::vector<int> heap, heap_pos;
    void heap_up(int i);
    void heap_down(int i);
    void heap_insert(Var v);
    Var heap_pop();
    bool heap_less(Var a, Var b) const { return activity[a] > activity[b]; }
    void bump(Var v);
    void bump_clause(CRef c);
    float cla_inc = 1;
    Lit pick_branch();

    // --- conflict analysis
    std::vector<uint8_t> seen;
    std::vector<Lit> learnt_clause, to_clear, stack;
    std::vector<uint64_t> level_stamp;
    uint64_t stamp = 0;
    void analyze(CRef confl, std::vector<Lit>& out, uint32_t& bt_level, uint32_t& out_lbd);
    bool redundant(Lit p, uint32_t abstract_levels);
    uint32_t compute_lbd(const Lit* ls, size_t n);

    // --- restarts and reduction
    double lbd_fast = 0, lbd_slow = 0, trail_avg = 0;
    uint64_t conflicts_at_restart = 0, next_reduce = 2000, reduce_inc = 300;
    uint64_t luby_index = 0, luby_limit = 0, mode_switch = 1000, phase_length = 1000;
    bool stable = false;  // Auto: alternate focused (glucose) and stable (Luby) phases
    bool restart_due();
    void reduce_db();
    size_t simplified_trail = 0;
    void simplify_satisfied();

    // --- preprocessing (elim.cpp)
    bool unsat = false;
    std::vector<std::vector<Lit>> pending;  // clauses before preprocessing
    std::vector<std::vector<Lit>> elim_stack;  // for extending the model to eliminated variables
    bool preprocess();
    void extend_model();

    double start_time = 0;
    bool out_of_time();
    Result search_loop();
};

double now_seconds();
uint64_t luby(uint64_t i);

}  // namespace lattice
