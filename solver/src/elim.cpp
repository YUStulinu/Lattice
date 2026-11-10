// Preprocessing: unit propagation, subsumption, self-subsuming resolution and bounded variable
// elimination (Eén and Biere, "Effective preprocessing in SAT through variable and clause
// elimination", SAT 2005). Every step is logged to the DRAT proof: new clauses (strengthened
// clauses and resolvents) are implied by resolution and therefore RUP; removals are deletions.
#include <algorithm>
#include <cstdint>
#include <queue>

#include "solver.hpp"

namespace lattice {

namespace {

struct PClause {
    std::vector<Lit> lits;  // sorted
    uint64_t sig = 0;
    bool dead = false;
};

uint64_t signature(const std::vector<Lit>& c) {
    uint64_t s = 0;
    for (Lit l : c) s |= uint64_t{1} << (l % 64);
    return s;
}

struct Pre {
    Solver& s;
    Proof& proof;
    std::vector<PClause> cs;
    std::vector<std::vector<uint32_t>> occ;  // literal -> clause indices (may hold dead ones)
    std::vector<int8_t> val;                 // per literal, top-level assignment
    std::vector<uint8_t>& eliminated;
    std::vector<std::vector<Lit>>& elim_stack;
    std::vector<Lit> units;
    uint64_t steps = 0, budget;
    bool unsat = false;
    double deadline;

    Pre(Solver& solver, Proof& p, std::vector<uint8_t>& el, std::vector<std::vector<Lit>>& st, Var n, uint64_t b, double dl)
        : s(solver), proof(p), occ(2 * static_cast<size_t>(n)), val(2 * static_cast<size_t>(n), 0), eliminated(el), elim_stack(st), budget(b), deadline(dl) {}

    uint32_t add(std::vector<Lit> c) {
        std::sort(c.begin(), c.end());
        const auto id = static_cast<uint32_t>(cs.size());
        for (Lit l : c) occ[l].push_back(id);
        cs.push_back({std::move(c), 0, false});
        cs.back().sig = signature(cs.back().lits);
        if (cs.back().lits.size() == 1) units.push_back(cs.back().lits[0]);
        return id;
    }

    void kill(uint32_t id) {
        if (cs[id].dead) return;
        cs[id].dead = true;
        proof.del(cs[id].lits);
    }

    // Replaces clause id by itself without `l` (logged as add, then delete).
    void strengthen(uint32_t id, Lit l) {
        PClause& c = cs[id];
        std::vector<Lit> old = c.lits;
        c.lits.erase(std::find(c.lits.begin(), c.lits.end(), l));
        proof.add(c.lits);
        proof.del(old);
        c.sig = signature(c.lits);
        auto& o = occ[l];
        o.erase(std::remove(o.begin(), o.end(), id), o.end());
        if (c.lits.empty()) unsat = true;
        if (c.lits.size() == 1) units.push_back(c.lits[0]);
    }

    bool propagate_units() {
        while (!units.empty() && !unsat) {
            const Lit u = units.back();
            units.pop_back();
            if (val[u] == 1) continue;
            if (val[u] == -1) {
                unsat = true;
                return false;
            }
            val[u] = 1;
            val[neg(u)] = -1;
            for (uint32_t id : occ[u])
                if (!cs[id].dead && cs[id].lits.size() > 1) kill(id);  // satisfied (keep the unit itself)
            const std::vector<uint32_t> negs = occ[neg(u)];
            for (uint32_t id : negs)
                if (!cs[id].dead) strengthen(id, neg(u));
        }
        return !unsat;
    }

    // Is a a subset of b, allowing at most one literal of a to appear negated in b? On success
    // `flipped` is that negated literal of b (kNoLit if a plainly subsumes b). Both sorted.
    static bool subset(const std::vector<Lit>& a, const std::vector<Lit>& b, Lit& flipped) {
        flipped = kNoLit;
        for (Lit l : a) {
            if (std::binary_search(b.begin(), b.end(), l)) continue;
            if (flipped == kNoLit && std::binary_search(b.begin(), b.end(), neg(l))) {
                flipped = neg(l);
                continue;
            }
            return false;
        }
        return true;
    }

    // Removes clauses subsumed by c and strengthens those c self-subsumes.
    void backward(uint32_t ci) {
        if (cs[ci].dead) return;
        const std::vector<Lit> c = cs[ci].lits;
        // The literal of c (or its negation) with the fewest occurrences.
        Lit best = c[0];
        size_t bestn = SIZE_MAX;
        for (Lit l : c) {
            const size_t n = occ[l].size() + occ[neg(l)].size();
            if (n < bestn) bestn = n, best = l;
        }
        for (Lit side : {best, neg(best)}) {
            const std::vector<uint32_t> list = occ[side];
            for (uint32_t di : list) {
                if (di == ci || cs[di].dead || cs[di].lits.size() < c.size()) continue;
                steps += c.size();
                if ((cs[ci].sig & ~cs[di].sig) != 0) {
                    // Signatures are of exact literals; a negated literal may still match.
                    // Cheap test on variables instead.
                    uint64_t va = 0, vb = 0;
                    for (Lit l : c) va |= uint64_t{1} << (var(l) % 64);
                    for (Lit l : cs[di].lits) vb |= uint64_t{1} << (var(l) % 64);
                    if (va & ~vb) continue;
                }
                Lit flipped;
                if (!subset(c, cs[di].lits, flipped)) continue;
                if (flipped == kNoLit) {
                    s.stats.subsumed++;
                    kill(di);
                } else {
                    s.stats.strengthened++;
                    strengthen(di, flipped);
                }
            }
        }
    }

    bool frozen_or_done(Var v) const { return eliminated[v] || val[mk_lit(v, false)] != 0; }

    std::vector<uint32_t> live(Lit l) {
        std::vector<uint32_t> out;
        for (uint32_t id : occ[l])
            if (!cs[id].dead) out.push_back(id);
        occ[l] = out;
        return out;
    }

    // Resolvent of p (contains v) and n (contains ~v); false if tautological.
    static bool resolve(const std::vector<Lit>& p, const std::vector<Lit>& n, Var v, std::vector<Lit>& out) {
        out.clear();
        size_t i = 0, j = 0;
        while (i < p.size() || j < n.size()) {
            Lit l;
            if (j == n.size() || (i < p.size() && p[i] <= n[j])) {
                l = p[i++];
                if (j < n.size() && n[j] == l) j++;
            } else {
                l = n[j++];
            }
            if (var(l) == v) continue;
            if (!out.empty() && out.back() == neg(l)) return false;
            out.push_back(l);
        }
        return true;
    }

    bool eliminate(Var v) {
        const Lit pl = mk_lit(v, false), nl = mk_lit(v, true);
        const auto pos = live(pl), negs = live(nl);
        if (pos.size() + negs.size() > 24) return false;
        std::vector<std::vector<Lit>> resolvents;
        std::vector<Lit> r;
        for (uint32_t a : pos)
            for (uint32_t b : negs) {
                steps += cs[a].lits.size() + cs[b].lits.size();
                if (!resolve(cs[a].lits, cs[b].lits, v, r)) continue;
                if (r.size() > 20 || resolvents.size() >= pos.size() + negs.size()) return false;
                resolvents.push_back(r);
            }
        // Keep the eliminated clauses for the model (the literal of v first), add resolvents,
        // then delete the originals.
        for (uint32_t id : pos) {
            std::vector<Lit> c = cs[id].lits;
            std::iter_swap(c.begin(), std::find(c.begin(), c.end(), pl));
            elim_stack.push_back(std::move(c));
        }
        for (uint32_t id : negs) {
            std::vector<Lit> c = cs[id].lits;
            std::iter_swap(c.begin(), std::find(c.begin(), c.end(), nl));
            elim_stack.push_back(std::move(c));
        }
        for (auto& res : resolvents) {
            proof.add(res);
            if (res.empty()) unsat = true;
            add(res);
        }
        for (uint32_t id : pos) kill(id);
        for (uint32_t id : negs) kill(id);
        eliminated[v] = 1;
        s.stats.elim_vars++;
        s.stats.elim_resolvents += resolvents.size();
        // New clauses may subsume others.
        for (size_t k = cs.size() - resolvents.size(); k < cs.size(); k++) backward(static_cast<uint32_t>(k));
        return propagate_units();
    }

    bool run() {
        if (!propagate_units()) return false;
        // Subsumption, shortest clauses first.
        std::vector<uint32_t> order(cs.size());
        for (uint32_t i = 0; i < order.size(); i++) order[i] = i;
        std::sort(order.begin(), order.end(), [&](uint32_t a, uint32_t b) { return cs[a].lits.size() < cs[b].lits.size(); });
        for (uint32_t id : order) {
            if (steps > budget / 2 || now_seconds() > deadline) break;
            backward(id);
            if (!propagate_units()) return false;
        }
        // Variable elimination, cheapest variables first (fewest occurrence pairs).
        using Item = std::pair<uint64_t, Var>;
        std::priority_queue<Item, std::vector<Item>, std::greater<Item>> q;
        for (Var v = 0; v < static_cast<Var>(occ.size() / 2); v++) {
            const uint64_t p = occ[mk_lit(v, false)].size(), n = occ[mk_lit(v, true)].size();
            if (p + n > 0) q.push({p * n, v});
        }
        while (!q.empty() && !unsat) {
            if (steps > budget || now_seconds() > deadline) break;
            const auto [cost, v] = q.top();
            q.pop();
            if (frozen_or_done(v)) continue;
            const uint64_t now_cost = static_cast<uint64_t>(live(mk_lit(v, false)).size()) * live(mk_lit(v, true)).size();
            if (now_cost > cost) {  // stale entry: requeue with its current cost
                q.push({now_cost, v});
                continue;
            }
            if (!eliminate(v)) {
                if (unsat) return false;
            }
        }
        return !unsat;
    }
};

}  // namespace

bool Solver::preprocess() {
    if (!opt.elim) return true;
    const double t0 = now_seconds();
    // Budget: proportional to the formula, and at most a fifth of the time limit (or 60 s).
    uint64_t total = 0;
    for (auto& c : pending) total += c.size();
    const double limit = opt.timeout > 0 ? std::min(60.0, opt.timeout / 5) : 60.0;
    Pre pre(*this, proof, eliminated, elim_stack, num_vars(), 200 * total + 10000000, t0 + limit);
    for (auto& c : pending) pre.add(std::move(c));
    pending.clear();
    const bool ok = pre.run();
    stats.elim_seconds = now_seconds() - t0;
    if (!ok) return false;
    for (auto& c : pre.cs)
        if (!c.dead) pending.push_back(std::move(c.lits));
    // Top-level values found here are kept as unit clauses (they are in pending already).
    return true;
}

void Solver::extend_model() {
    // Undo eliminations last to first: a saved clause not satisfied by the model so far is
    // made true by its first literal, the eliminated variable's.
    for (size_t i = elim_stack.size(); i-- > 0;) {
        const auto& c = elim_stack[i];
        bool sat = false;
        for (Lit l : c)
            if (model[var(l)] != sign(l)) {
                sat = true;
                break;
            }
        if (!sat) model[var(c[0])] = !sign(c[0]);
    }
}

}  // namespace lattice
