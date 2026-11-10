#include "solver.hpp"

#include <algorithm>
#include <chrono>
#include <cmath>
#include <cstring>

namespace lattice {

double now_seconds() {
    return std::chrono::duration<double>(std::chrono::steady_clock::now().time_since_epoch()).count();
}

// The Luby sequence 1 1 2 1 1 2 4 1 1 2 1 1 2 4 8 ... (i from 0).
uint64_t luby(uint64_t i) {
    uint64_t size = 1, seq = 0;
    while (size < i + 1) size = 2 * size + 1, seq++;
    while (size - 1 != i) {
        size = (size - 1) >> 1;
        seq--;
        i = i % size;
    }
    return uint64_t{1} << seq;
}

// ---------------------------------------------------------------- proof and trace

bool Proof::open(const std::string& path, bool binary) {
    f_ = std::fopen(path.c_str(), "wb");
    binary_ = binary;
    return f_ != nullptr;
}

void Proof::write(char kind, const Lit* ls, size_t n) {
    lines++;
    if (binary_) {
        buf_.push_back(kind);
        for (size_t i = 0; i < n; i++) {
            // DIMACS literal x as the unsigned 2|x| + (x < 0), 7 bits per byte (LEB128).
            uint32_t u = 2 * (var(ls[i]) + 1) + (sign(ls[i]) ? 1 : 0);
            while (u > 127) {
                buf_.push_back(static_cast<char>((u & 127) | 128));
                u >>= 7;
            }
            buf_.push_back(static_cast<char>(u));
        }
        buf_.push_back(0);
    } else {
        if (kind == 'd') buf_.insert(buf_.end(), {'d', ' '});
        char tmp[16];
        for (size_t i = 0; i < n; i++) {
            const int len = std::snprintf(tmp, sizeof tmp, "%d ", to_dimacs(ls[i]));
            buf_.insert(buf_.end(), tmp, tmp + len);
        }
        buf_.insert(buf_.end(), {'0', '\n'});
    }
    if (buf_.size() > (1 << 20)) {
        std::fwrite(buf_.data(), 1, buf_.size(), f_);
        buf_.clear();
    }
}

void Proof::close() {
    if (!f_) return;
    std::fwrite(buf_.data(), 1, buf_.size(), f_);
    buf_.clear();
    std::fclose(f_);
    f_ = nullptr;
}

bool Trace::open(const std::string& path) {
    f_ = std::fopen(path.c_str(), "wb");
    return f_ != nullptr;
}

void Trace::event(const char* json) {
    if (!enabled()) return;
    std::fputs(json, f_);
    std::fputc('\n', f_);
    events++;
}

void Trace::close() {
    if (f_) std::fclose(f_);
    f_ = nullptr;
}

static std::string lits_json(const Lit* ls, size_t n) {
    std::string s = "[";
    for (size_t i = 0; i < n; i++) s += (i ? "," : "") + std::to_string(to_dimacs(ls[i]));
    return s + "]";
}

// ---------------------------------------------------------------- input

void Solver::reserve_vars(Var n) {
    if (n <= num_vars()) return;
    assigns.resize(n, 0);
    vals.resize(2 * static_cast<size_t>(n), 0);
    level.resize(n, 0);
    reason.resize(n, kNoReason);
    activity.resize(n, 0);
    phase.resize(n, 1);  // negative first, as MiniSat
    eliminated.resize(n, 0);
    seen.resize(n, 0);
    heap_pos.resize(n, -1);
    watches.resize(2 * static_cast<size_t>(n));
}

bool Solver::add_clause(std::vector<Lit> c) {
    Var maxv = 0;
    for (Lit l : c) maxv = std::max(maxv, var(l) + 1);
    reserve_vars(maxv);
    original.push_back(c);
    if (unsat) return false;
    // Remove duplicates; drop tautologies.
    std::sort(c.begin(), c.end());
    c.erase(std::unique(c.begin(), c.end()), c.end());
    for (size_t i = 1; i < c.size(); i++)
        if (c[i] == neg(c[i - 1])) return true;
    if (c.empty()) {
        unsat = true;
        return false;
    }
    pending.push_back(std::move(c));
    return true;
}

// ---------------------------------------------------------------- clause store

CRef Solver::alloc(const std::vector<Lit>& ls, bool is_learnt) {
    const CRef c = static_cast<CRef>(arena.size());
    arena.push_back(static_cast<uint32_t>(ls.size()));
    arena.push_back(is_learnt ? 1u : 0u);
    arena.push_back(0);
    arena.insert(arena.end(), ls.begin(), ls.end());
    cact(c) = 0;
    (is_learnt ? learnts : clauses).push_back(c);
    return c;
}

void Solver::remove_clause(CRef c) {
    proof.del(lits(c), csize(c));
    cflags(c) |= 2;
    wasted += 3 + csize(c);
    stats.deleted++;
}

bool Solver::locked(CRef c) {
    const Lit* l = lits(c);
    for (int i = 0; i < (csize(c) == 2 ? 2 : 1); i++) {
        const Var v = var(l[i]);
        if (value(l[i]) == 1 && reason[v] == c) return true;
    }
    return false;
}

bool Solver::satisfied(CRef c) {
    const Lit* l = lits(c);
    for (uint32_t i = 0; i < csize(c); i++)
        if (value(l[i]) == 1) return true;
    return false;
}

void Solver::attach(CRef c) {
    Lit* l = lits(c);
    const bool bin = csize(c) == 2;
    watches[l[0]].push_back({c, l[1], bin});
    watches[l[1]].push_back({c, l[0], bin});
}

void Solver::rebuild_watches() {
    for (auto& w : watches) w.clear();
    for (CRef c : clauses)
        if (!deleted(c)) attach(c);
    for (CRef c : learnts)
        if (!deleted(c)) attach(c);
}

// Compacts the arena; reasons and clause lists are remapped, watches rebuilt.
void Solver::collect_garbage() {
    std::vector<uint32_t> fresh;
    fresh.reserve(arena.size() - wasted);
    auto move = [&](std::vector<CRef>& list) {
        size_t j = 0;
        for (CRef c : list) {
            if (deleted(c)) continue;
            const CRef n = static_cast<CRef>(fresh.size());
            fresh.insert(fresh.end(), arena.begin() + c, arena.begin() + c + 3 + csize(c));
            arena[c + 2] = n;  // forwarding address (activity no longer needed in the old copy)
            cflags(c) |= 8u << 28;  // moved marker in a bit lbd never reaches
            list[j++] = n;
        }
        list.resize(j);
    };
    move(clauses);
    move(learnts);
    for (Lit l : trail) {
        CRef& r = reason[var(l)];
        if (r != kNoReason) r = (cflags(r) & (8u << 28)) ? arena[r + 2] : kNoReason;
    }
    arena.swap(fresh);
    for (CRef c : clauses) cflags(c) &= ~(8u << 28);
    for (CRef c : learnts) cflags(c) &= ~(8u << 28);
    wasted = 0;
    rebuild_watches();
}

// ---------------------------------------------------------------- assignment

void Solver::enqueue(Lit l, CRef from) {
    vals[l] = 1;
    vals[neg(l)] = -1;
    const Var v = var(l);
    level[v] = decision_level();
    reason[v] = from;
    trail.push_back(l);
    if (trace.enabled()) {
        // "a": an assignment, with its level; "why" is the clause that implied it (absent for
        // decisions and top-level units).
        std::string e = "{\"e\":\"a\",\"l\":" + std::to_string(to_dimacs(l)) + ",\"d\":" + std::to_string(decision_level());
        if (from != kNoReason) e += ",\"why\":" + lits_json(lits(from), csize(from));
        trace.event((e + "}").c_str());
    }
}

CRef Solver::propagate() {
    CRef confl = kNoReason;
    while (qhead < trail.size()) {
        const Lit p = trail[qhead++];
        const Lit false_lit = neg(p);
        std::vector<Watch>& ws = watches[false_lit];
        stats.propagations++;
        size_t i = 0, j = 0;
        const size_t n = ws.size();
        while (i < n) {
            const Watch w = ws[i++];
            if (value(w.blocker) == 1) {
                ws[j++] = w;
                continue;
            }
            if (w.binary) {
                ws[j++] = w;
                if (value(w.blocker) == -1) {
                    confl = w.cref;
                    while (i < n) ws[j++] = ws[i++];
                } else {
                    enqueue(w.blocker, w.cref);
                }
                continue;
            }
            Lit* c = lits(w.cref);
            if (c[0] == false_lit) std::swap(c[0], c[1]);
            const Lit first = c[0];
            const Watch nw{w.cref, first, false};
            if (first != w.blocker && value(first) == 1) {
                ws[j++] = nw;
                continue;
            }
            const uint32_t sz = csize(w.cref);
            bool moved = false;
            for (uint32_t k = 2; k < sz; k++) {
                if (value(c[k]) != -1) {
                    c[1] = c[k];
                    c[k] = false_lit;
                    watches[c[1]].push_back(nw);
                    moved = true;
                    break;
                }
            }
            if (moved) continue;
            ws[j++] = nw;
            if (value(first) == -1) {
                confl = w.cref;
                while (i < n) ws[j++] = ws[i++];
            } else {
                enqueue(first, w.cref);
            }
        }
        ws.resize(j);
        if (confl != kNoReason) break;
    }
    return confl;
}

void Solver::backtrack(uint32_t lvl) {
    if (decision_level() <= lvl) return;
    if (trace.enabled()) trace.event(("{\"e\":\"back\",\"to\":" + std::to_string(lvl) + "}").c_str());
    for (size_t i = trail.size(); i-- > trail_lim[lvl];) {
        const Lit l = trail[i];
        const Var v = var(l);
        vals[l] = vals[neg(l)] = 0;
        reason[v] = kNoReason;
        phase[v] = sign(l);
        if (heap_pos[v] < 0) heap_insert(v);
    }
    trail.resize(trail_lim[lvl]);
    trail_lim.resize(lvl);
    qhead = trail.size();
}

// ---------------------------------------------------------------- VSIDS

void Solver::heap_up(int i) {
    const int v = heap[static_cast<size_t>(i)];
    while (i > 0) {
        const int p = (i - 1) / 2;
        if (!heap_less(static_cast<Var>(v), static_cast<Var>(heap[static_cast<size_t>(p)]))) break;
        heap[static_cast<size_t>(i)] = heap[static_cast<size_t>(p)];
        heap_pos[static_cast<size_t>(heap[static_cast<size_t>(i)])] = i;
        i = p;
    }
    heap[static_cast<size_t>(i)] = v;
    heap_pos[static_cast<size_t>(v)] = i;
}

void Solver::heap_down(int i) {
    const int v = heap[static_cast<size_t>(i)];
    const int n = static_cast<int>(heap.size());
    for (;;) {
        int c = 2 * i + 1;
        if (c >= n) break;
        if (c + 1 < n && heap_less(static_cast<Var>(heap[static_cast<size_t>(c + 1)]), static_cast<Var>(heap[static_cast<size_t>(c)]))) c++;
        if (!heap_less(static_cast<Var>(heap[static_cast<size_t>(c)]), static_cast<Var>(v))) break;
        heap[static_cast<size_t>(i)] = heap[static_cast<size_t>(c)];
        heap_pos[static_cast<size_t>(heap[static_cast<size_t>(i)])] = i;
        i = c;
    }
    heap[static_cast<size_t>(i)] = v;
    heap_pos[static_cast<size_t>(v)] = i;
}

void Solver::heap_insert(Var v) {
    if (eliminated[v]) return;
    heap.push_back(static_cast<int>(v));
    heap_pos[v] = static_cast<int>(heap.size()) - 1;
    heap_up(heap_pos[v]);
}

Var Solver::heap_pop() {
    const Var top = static_cast<Var>(heap[0]);
    heap[0] = heap.back();
    heap.pop_back();
    heap_pos[top] = -1;
    if (!heap.empty()) {
        heap_pos[static_cast<size_t>(heap[0])] = 0;
        heap_down(0);
    }
    return top;
}

void Solver::bump(Var v) {
    if ((activity[v] += var_inc) > 1e100) {
        for (double& a : activity) a *= 1e-100;
        var_inc *= 1e-100;
    }
    if (heap_pos[v] >= 0) heap_up(heap_pos[v]);
}

void Solver::bump_clause(CRef c) {
    if ((cact(c) += cla_inc) > 1e20f) {
        for (CRef l : learnts) cact(l) *= 1e-20f;
        cla_inc *= 1e-20f;
    }
}

Lit Solver::pick_branch() {
    while (!heap.empty()) {
        const Var v = heap_pop();
        if (vals[mk_lit(v, false)] == 0 && !eliminated[v]) return mk_lit(v, phase[v] != 0);
    }
    return kNoLit;
}

// ---------------------------------------------------------------- conflict analysis

uint32_t Solver::compute_lbd(const Lit* ls, size_t n) {
    stamp++;
    uint32_t count = 0;
    for (size_t i = 0; i < n; i++) {
        const uint32_t l = level[var(ls[i])];
        if (level_stamp[l] != stamp) {
            level_stamp[l] = stamp;
            count++;
        }
    }
    return count;
}

// Is p implied by literals already in the learnt clause? (MiniSat's recursive minimisation,
// with the abstraction of decision levels as a quick filter.)
bool Solver::redundant(Lit p, uint32_t abstract_levels) {
    stack.clear();
    stack.push_back(p);
    const size_t top = to_clear.size();
    while (!stack.empty()) {
        const Lit q = stack.back();
        stack.pop_back();
        const CRef r = reason[var(q)];
        const Lit* c = lits(r);
        for (uint32_t i = 0; i < csize(r); i++) {
            const Lit l = c[i];
            const Var v = var(l);
            if (v == var(q) || seen[v] || level[v] == 0) continue;
            if (reason[v] != kNoReason && ((1u << (level[v] & 31)) & abstract_levels)) {
                seen[v] = 1;
                stack.push_back(l);
                to_clear.push_back(l);
            } else {
                for (size_t k = top; k < to_clear.size(); k++) seen[var(to_clear[k])] = 0;
                to_clear.resize(top);
                return false;
            }
        }
    }
    return true;
}

void Solver::analyze(CRef confl, std::vector<Lit>& out, uint32_t& bt_level, uint32_t& out_lbd) {
    out.clear();
    out.push_back(kNoLit);  // the asserting literal goes here
    int path = 0;
    Lit p = kNoLit;
    size_t index = trail.size();
    do {
        if (learnt(confl)) {
            bump_clause(confl);
            cflags(confl) |= 4;  // used since the last reduction
            const uint32_t l = compute_lbd(lits(confl), csize(confl));
            if (l + 1 < lbd(confl)) set_lbd(confl, l);
        }
        const Lit* c = lits(confl);
        for (uint32_t i = 0; i < csize(confl); i++) {
            const Lit q = c[i];
            const Var v = var(q);
            if (q == p || seen[v] || level[v] == 0) continue;
            seen[v] = 1;
            bump(v);
            if (level[v] >= decision_level()) {
                path++;
            } else {
                out.push_back(q);
            }
        }
        while (!seen[var(trail[--index])]) {
        }
        p = trail[index];
        confl = reason[var(p)];
        seen[var(p)] = 0;
        path--;
    } while (path > 0);
    out[0] = neg(p);

    // Minimise.
    to_clear.assign(out.begin(), out.end());
    uint32_t abstract_levels = 0;
    for (size_t i = 1; i < out.size(); i++) abstract_levels |= 1u << (level[var(out[i])] & 31);
    size_t j = 1;
    const size_t before = out.size();
    for (size_t i = 1; i < out.size(); i++)
        if (reason[var(out[i])] == kNoReason || !redundant(out[i], abstract_levels)) out[j++] = out[i];
    out.resize(j);
    stats.minimised_literals += before - out.size();
    stats.learnt_literals += out.size();
    for (Lit l : to_clear) seen[var(l)] = 0;
    to_clear.clear();

    // Backjump to the second-highest level; that literal goes second (it will be watched).
    bt_level = 0;
    if (out.size() > 1) {
        size_t m = 1;
        for (size_t i = 2; i < out.size(); i++)
            if (level[var(out[i])] > level[var(out[m])]) m = i;
        std::swap(out[1], out[m]);
        bt_level = level[var(out[1])];
    }
    out_lbd = compute_lbd(out.data(), out.size());
}

// ---------------------------------------------------------------- restarts, reduction

bool Solver::restart_due() {
    const uint64_t since = stats.conflicts - conflicts_at_restart;
    if (stable || opt.restarts == Restarts::Luby) return since >= luby_limit;
    // Glucose: restart when recent learnt clauses are worse (higher LBD) than the long-run
    // average; exponential moving averages instead of Glucose's queues.
    return since >= 50 && lbd_fast > 1.25 * lbd_slow;
}

void Solver::reduce_db() {
    stats.reductions++;
    // Tiers: LBD <= 2 kept for good; LBD <= 6 kept while used; the rest ranked by activity, and
    // the less active half removed. Clauses that are reasons are never removed.
    std::vector<CRef> candidates;
    for (CRef c : learnts) {
        if (deleted(c)) continue;
        const uint32_t l = lbd(c);
        if (l <= 2) continue;
        if (l <= 6 && used(c)) {
            cflags(c) &= ~4u;
            continue;
        }
        cflags(c) &= ~4u;
        if (!locked(c)) candidates.push_back(c);
    }
    std::sort(candidates.begin(), candidates.end(), [&](CRef a, CRef b) {
        return lbd(a) != lbd(b) ? lbd(a) > lbd(b) : cact(a) < cact(b);
    });
    for (size_t i = 0; i < candidates.size() / 2; i++) remove_clause(candidates[i]);
    learnts.erase(std::remove_if(learnts.begin(), learnts.end(), [&](CRef c) { return deleted(c); }), learnts.end());
    if (wasted * 4 > arena.size()) {
        collect_garbage();
    } else {
        rebuild_watches();
    }
}

// At level 0: remove clauses satisfied by the top-level assignment.
void Solver::simplify_satisfied() {
    if (trail.size() == simplified_trail) return;
    simplified_trail = trail.size();
    for (auto* list : {&clauses, &learnts}) {
        for (CRef c : *list)
            if (!deleted(c) && satisfied(c) && !locked(c)) remove_clause(c);
        list->erase(std::remove_if(list->begin(), list->end(), [&](CRef c) { return deleted(c); }), list->end());
    }
    if (wasted * 4 > arena.size()) {
        collect_garbage();
    } else {
        rebuild_watches();
    }
}

bool Solver::out_of_time() { return opt.timeout > 0 && now_seconds() - start_time > opt.timeout; }

// ---------------------------------------------------------------- main loop

Result Solver::solve() {
    start_time = now_seconds();
    if (unsat || !preprocess()) {
        proof.add(nullptr, 0);
        stats.solve_seconds = now_seconds() - start_time;
        return Result::Unsat;
    }
    level_stamp.assign(num_vars() + 2, 0);
    for (Var v = 0; v < num_vars(); v++)
        if (heap_pos[v] < 0 && !eliminated[v]) heap_insert(v);
    Result r = search_loop();
    if (r == Result::Sat) {
        model.assign(num_vars(), false);
        for (Var v = 0; v < num_vars(); v++) model[v] = vals[mk_lit(v, false)] == 1;
        extend_model();
    } else if (r == Result::Unsat) {
        proof.add(nullptr, 0);
    }
    stats.solve_seconds = now_seconds() - start_time;
    return r;
}

Result Solver::search_loop() {
    // Clauses that survived preprocessing: units go on the trail, others into the arena.
    for (auto& c : pending) {
        if (c.size() == 1) {
            if (value(c[0]) == -1) return Result::Unsat;
            if (value(c[0]) == 0) enqueue(c[0], kNoReason);
        } else {
            attach(alloc(c, false));
        }
    }
    pending.clear();
    pending.shrink_to_fit();
    if (propagate() != kNoReason) return Result::Unsat;
    luby_limit = 100 * luby(luby_index);
    std::vector<Lit> learnt_lits;
    char buf[256];
    for (;;) {
        const CRef confl = propagate();
        if (confl != kNoReason) {
            stats.conflicts++;
            if (decision_level() == 0) return Result::Unsat;
            uint32_t bt = 0, l = 0;
            if (trace.enabled()) trace.event(("{\"e\":\"conflict\",\"c\":" + lits_json(lits(confl), csize(confl)) + "}").c_str());
            analyze(confl, learnt_lits, bt, l);
            backtrack(bt);
            proof.add(learnt_lits);
            if (trace.enabled()) {
                std::snprintf(buf, sizeof buf, ",\"lbd\":%u,\"back\":%u}", l, bt);
                trace.event(("{\"e\":\"learn\",\"c\":" + lits_json(learnt_lits.data(), learnt_lits.size()) + buf).c_str());
            }
            if (learnt_lits.size() == 1) {
                enqueue(learnt_lits[0], kNoReason);
            } else {
                const CRef c = alloc(learnt_lits, true);
                set_lbd(c, l);
                attach(c);
                bump_clause(c);
                enqueue(learnt_lits[0], c);
            }
            var_inc /= var_decay;
            cla_inc /= 0.999f;
            if (var_decay < 0.95 && stats.conflicts % 5000 == 0) var_decay += 0.01;
            lbd_fast += (l - lbd_fast) / 32.0;
            lbd_slow += (l - lbd_slow) / (stats.conflicts < 10000 ? static_cast<double>(stats.conflicts) : 10000.0);
            trail_avg += (trail.size() - trail_avg) / 5000.0;
            // Glucose's restart blocking: a much longer trail than usual means the search may be
            // close to a model; do not throw it away.
            if (!stable && stats.conflicts > 10000 && trail.size() > 1.4 * trail_avg) conflicts_at_restart = stats.conflicts;
            if (stats.conflicts % 1024 == 0 && out_of_time()) return Result::Unknown;
            if (opt.verbose && stats.conflicts % 100000 == 0)
                std::fprintf(stderr, "c %8llu conflicts  %8zu learnts  %s  %.1f s\n", static_cast<unsigned long long>(stats.conflicts), learnts.size(),
                             stable ? "stable" : "focused", now_seconds() - start_time);
        } else {
            if (restart_due()) {
                stats.restarts++;
                conflicts_at_restart = stats.conflicts;
                if (stable || opt.restarts == Restarts::Luby) luby_limit = 100 * luby(++luby_index);
                backtrack(0);
                if (trace.enabled()) trace.event("{\"e\":\"restart\"}");
                if (opt.restarts == Restarts::Auto && stats.conflicts >= mode_switch) {
                    // Alternate the two regimes, each phase twice as long as the last.
                    stable = !stable;
                    if (!stable) phase_length *= 2;
                    mode_switch = stats.conflicts + phase_length;
                    luby_index = 0;
                    luby_limit = 100 * luby(0);
                }
            }
            if (decision_level() == 0) simplify_satisfied();
            if (stats.conflicts >= next_reduce) {
                next_reduce = stats.conflicts + 2000 + reduce_inc * stats.reductions;
                reduce_db();
            }
            const Lit d = pick_branch();
            if (d == kNoLit) return Result::Sat;
            stats.decisions++;
            trail_lim.push_back(static_cast<uint32_t>(trail.size()));
            if (trace.enabled()) {
                std::snprintf(buf, sizeof buf, "{\"e\":\"decide\",\"l\":%d,\"level\":%u}", to_dimacs(d), decision_level());
                trace.event(buf);
            }
            enqueue(d, kNoReason);
        }
    }
}

}  // namespace lattice
