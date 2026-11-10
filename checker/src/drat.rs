//! Backward DRAT checking, the method of drat-trim (Wetzler, Heule and Hunt, SAT 2014).
//!
//! Forward pass: every clause of the formula and every lemma of the proof is added (deletions
//! applied) while unit propagation runs at the top level, without checking anything, until the
//! top level is in conflict. Backward pass: the clauses that took part in that conflict are
//! marked; going back through the proof, each lemma is removed again and, only if it was marked,
//! checked: it must be RUP (asserting its negation propagates to a conflict) or else RAT on its
//! first literal. Clauses used by a successful check are marked in turn. Lemmas never marked are
//! never checked: they did not contribute to the refutation.
//!
//! As drat-trim does by default, deleting a unit clause or a clause that is the reason of a
//! top-level assignment is ignored (such deletions would change the top-level assignment, which
//! the solver's own deletion did not intend).

use std::collections::HashMap;

const NONE: u32 = u32::MAX;

pub struct Outcome {
    pub outcome: Result<(), String>,
    pub clauses: usize,
    pub lemmas: usize,
    pub deletions: usize,
    pub ignored_deletions: usize,
    pub core_lemmas: usize,
    pub rat_checks: usize,
    pub binary: bool,
}

#[derive(Clone, Copy, PartialEq)]
enum Step {
    Add(u32),
    Del(u32),
    Skip,
}

fn lit(x: i64) -> u32 {
    if x > 0 {
        2 * (x as u32 - 1)
    } else {
        2 * ((-x) as u32 - 1) + 1
    }
}

/// Clauses of a DIMACS file (comments and the header skipped).
pub fn parse_cnf(b: &[u8]) -> Result<Vec<Vec<u32>>, String> {
    let mut out = Vec::new();
    let mut c = Vec::new();
    let mut i = 0;
    let mut line_start = true;
    while i < b.len() {
        let ch = b[i];
        if line_start && (ch == b'c' || ch == b'p') {
            while i < b.len() && b[i] != b'\n' {
                i += 1;
            }
            continue;
        }
        if line_start && ch == b'%' {
            break;
        }
        line_start = ch == b'\n';
        if ch == b'-' || ch.is_ascii_digit() {
            let neg = ch == b'-';
            if neg {
                i += 1;
            }
            let mut v: i64 = 0;
            while i < b.len() && b[i].is_ascii_digit() {
                v = v * 10 + (b[i] - b'0') as i64;
                i += 1;
            }
            if v == 0 {
                out.push(std::mem::take(&mut c));
            } else {
                c.push(lit(if neg { -v } else { v }));
            }
            continue;
        }
        if !ch.is_ascii_whitespace() {
            return Err(format!("formula: unexpected byte {ch:#x}"));
        }
        i += 1;
    }
    if !c.is_empty() {
        out.push(c);
    }
    Ok(out)
}

/// A binary proof begins with 'a' or 'd' and holds bytes that never occur in text proofs.
fn looks_binary(p: &[u8]) -> bool {
    p.iter().take(64).any(|&b| !(b.is_ascii_digit() || b == b'-' || b == b'd' || b.is_ascii_whitespace() || b == b'c'))
}

fn parse_proof(p: &[u8], binary: bool) -> Result<Vec<(bool, Vec<u32>)>, String> {
    let mut out = Vec::new();
    let mut i = 0;
    if binary {
        while i < p.len() {
            let kind = p[i];
            i += 1;
            let del = match kind {
                b'a' => false,
                b'd' => true,
                _ => return Err(format!("binary proof: unexpected byte {kind:#x} at {}", i - 1)),
            };
            let mut c = Vec::new();
            loop {
                let mut u: u64 = 0;
                let mut shift = 0;
                loop {
                    if i >= p.len() {
                        return Err("binary proof: truncated".into());
                    }
                    let b = p[i];
                    i += 1;
                    u |= ((b & 127) as u64) << shift;
                    shift += 7;
                    if b & 128 == 0 {
                        break;
                    }
                }
                if u == 0 {
                    break;
                }
                // 2|x| + (x < 0)  ->  our 2(v-1) + negated
                c.push((u as u32) - 2);
            }
            out.push((del, c));
        }
    } else {
        let mut c = Vec::new();
        let mut del = false;
        let mut line_start = true;
        while i < p.len() {
            let ch = p[i];
            if line_start && ch == b'c' {
                while i < p.len() && p[i] != b'\n' {
                    i += 1;
                }
                continue;
            }
            line_start = ch == b'\n';
            if ch == b'd' {
                del = true;
                i += 1;
                continue;
            }
            if ch == b'-' || ch.is_ascii_digit() {
                let neg = ch == b'-';
                if neg {
                    i += 1;
                }
                let mut v: i64 = 0;
                while i < p.len() && p[i].is_ascii_digit() {
                    v = v * 10 + (p[i] - b'0') as i64;
                    i += 1;
                }
                if v == 0 {
                    out.push((del, std::mem::take(&mut c)));
                    del = false;
                } else {
                    c.push(lit(if neg { -v } else { v }));
                }
                continue;
            }
            if !ch.is_ascii_whitespace() {
                return Err(format!("text proof: unexpected byte {ch:#x}"));
            }
            i += 1;
        }
    }
    Ok(out)
}

struct Checker {
    arena: Vec<u32>,
    start: Vec<u32>,
    len: Vec<u32>,
    active: Vec<bool>,
    core: Vec<bool>,
    pivot: Vec<u32>, // first literal as written (the RAT pivot), NONE for the empty clause
    watches: Vec<Vec<u32>>,
    val: Vec<i8>,
    reason: Vec<u32>,
    trail: Vec<u32>,
    seen: Vec<bool>,
    // Top-level literals whose reason chain is already marked as core. The top-level trail
    // only shrinks from its end (undo) and reasons never change while a literal stays on it, so
    // a marked chain stays marked until the literal is unassigned.
    chained: Vec<bool>,
    pos: Vec<u32>,
    top: usize,
    stack: Vec<u32>,
    touched: Vec<usize>,
    nvars: usize,
}

impl Checker {
    fn grow(&mut self, l: u32) {
        let v = (l >> 1) as usize + 1;
        if v > self.nvars {
            self.nvars = v;
            self.val.resize(2 * v, 0);
            self.reason.resize(v, NONE);
            self.seen.resize(v, false);
            self.chained.resize(v, false);
            self.pos.resize(v, 0);
            self.watches.resize(2 * v, Vec::new());
        }
    }

    fn add_clause(&mut self, mut c: Vec<u32>) -> u32 {
        self.pivot.push(c.first().copied().unwrap_or(NONE));
        c.sort_unstable();
        c.dedup();
        for &l in &c {
            self.grow(l);
        }
        let id = self.start.len() as u32;
        self.start.push(self.arena.len() as u32);
        self.len.push(c.len() as u32);
        self.arena.extend_from_slice(&c);
        self.active.push(false);
        self.core.push(false);
        id
    }

    fn lits(&self, id: u32) -> &[u32] {
        let s = self.start[id as usize] as usize;
        &self.arena[s..s + self.len[id as usize] as usize]
    }

    fn value(&self, l: u32) -> i8 {
        self.val[l as usize]
    }

    fn assign(&mut self, l: u32, r: u32) {
        self.val[l as usize] = 1;
        self.val[(l ^ 1) as usize] = -1;
        self.reason[(l >> 1) as usize] = r;
        self.pos[(l >> 1) as usize] = self.trail.len() as u32;
        self.trail.push(l);
    }

    fn undo_to(&mut self, n: usize) {
        while self.trail.len() > n {
            let l = self.trail.pop().unwrap();
            self.val[l as usize] = 0;
            self.val[(l ^ 1) as usize] = 0;
            self.reason[(l >> 1) as usize] = NONE;
            self.chained[(l >> 1) as usize] = false;
        }
    }

    /// Makes a clause active: watches it, or, at the top level, acts on it if it is unit or
    /// falsified. Returns a conflicting clause, if any.
    fn activate(&mut self, id: u32, first_time: bool) -> u32 {
        self.active[id as usize] = true;
        let n = self.len[id as usize] as usize;
        if n == 0 {
            return id;
        }
        if n == 1 {
            let l = self.lits(id)[0];
            return match self.value(l) {
                1 => NONE,
                -1 => id,
                _ => {
                    self.assign(l, id);
                    NONE
                }
            };
        }
        if first_time {
            // Non-false literals first, so the watches are on them where possible.
            let s = self.start[id as usize] as usize;
            let mut k = 0;
            for i in 0..n {
                if self.val[self.arena[s + i] as usize] != -1 {
                    self.arena.swap(s + k, s + i);
                    k += 1;
                    if k == 2 {
                        break;
                    }
                }
            }
            let (a, b) = (self.arena[s], self.arena[s + 1]);
            self.watches[a as usize].push(id);
            self.watches[b as usize].push(id);
        }
        let (a, b) = (self.lits(id)[0], self.lits(id)[1]);
        let (va, vb) = (self.value(a), self.value(b));
        if va == 1 || vb == 1 {
            return NONE;
        }
        // Non-false literals were moved to the front when the clause was added, and the
        // top-level assignment only grows in the forward pass, so: both watches false means
        // every literal is false; only the second false means the first is implied.
        if va == -1 {
            return id;
        }
        if vb == -1 && va == 0 {
            self.assign(a, id);
        }
        NONE
    }

    /// Unit propagation from trail position `from`; returns a conflicting clause or NONE.
    fn propagate(&mut self, mut from: usize) -> u32 {
        while from < self.trail.len() {
            let p = self.trail[from];
            from += 1;
            let f = p ^ 1;
            let mut ws = std::mem::take(&mut self.watches[f as usize]);
            let mut i = 0;
            let mut j = 0;
            let mut confl = NONE;
            while i < ws.len() {
                let id = ws[i];
                i += 1;
                // Inactive (deleted, or a lemma the backward pass has undone): drop the watch.
                // A deleted clause is watched again when the backward pass reaches its deletion.
                if !self.active[id as usize] {
                    continue;
                }
                let s = self.start[id as usize] as usize;
                let n = self.len[id as usize] as usize;
                if self.arena[s] == f {
                    self.arena.swap(s, s + 1);
                } else if self.arena[s + 1] != f {
                    continue; // a stale watch left over from an earlier life of the clause
                }
                let first = self.arena[s];
                if self.val[first as usize] == 1 {
                    ws[j] = id;
                    j += 1;
                    continue;
                }
                let mut moved = false;
                for k in 2..n {
                    let l = self.arena[s + k];
                    if self.val[l as usize] != -1 {
                        self.arena.swap(s + 1, s + k);
                        self.watches[l as usize].push(id);
                        moved = true;
                        break;
                    }
                }
                if moved {
                    continue;
                }
                ws[j] = id;
                j += 1;
                if self.val[first as usize] == -1 {
                    confl = id;
                    while i < ws.len() {
                        ws[j] = ws[i];
                        j += 1;
                        i += 1;
                    }
                } else {
                    self.assign(first, id);
                }
            }
            ws.truncate(j);
            // Watches added to this same list while it was taken out are in self.watches[f].
            let added = std::mem::take(&mut self.watches[f as usize]);
            ws.extend(added);
            self.watches[f as usize] = ws;
            if confl != NONE {
                return confl;
            }
        }
        NONE
    }

    /// Marks as core the clause `id` and, recursively, the reasons of its false literals.
    /// Literals on the top-level trail (positions below `self.top`) whose chain is already
    /// marked are not walked again.
    fn mark(&mut self, id: u32) {
        self.core[id as usize] = true;
        let mut stack = std::mem::take(&mut self.stack);
        let mut touched = std::mem::take(&mut self.touched);
        stack.clear();
        stack.extend_from_slice(self.lits(id));
        while let Some(l) = stack.pop() {
            let v = (l >> 1) as usize;
            if self.seen[v] || self.chained[v] {
                continue;
            }
            self.seen[v] = true;
            touched.push(v);
            let r = self.reason[v];
            if r != NONE {
                self.core[r as usize] = true;
                stack.extend_from_slice(self.lits(r));
            }
        }
        for &v in &touched {
            self.seen[v] = false;
            if self.val[2 * v] != 0 && (self.pos[v] as usize) < self.top {
                self.chained[v] = true;
            }
        }
        touched.clear();
        self.stack = stack;
        self.touched = touched;
    }

    /// Is clause c implied by unit propagation? On success, the clauses used are marked.
    fn rup(&mut self, c: &[u32]) -> bool {
        let base = self.trail.len();
        self.top = base;
        for &l in c {
            match self.value(l) {
                1 => {
                    // Already true at the top level: its reason chain is the justification.
                    let r = self.reason[(l >> 1) as usize];
                    if r != NONE {
                        self.mark(r);
                    }
                    self.undo_to(base);
                    return true;
                }
                -1 => {}
                _ => self.assign(l ^ 1, NONE),
            }
        }
        let confl = self.propagate(base);
        let ok = confl != NONE;
        if ok {
            self.mark(confl);
        }
        self.undo_to(base);
        ok
    }
}

pub fn check(cnf: &[u8], proof: &[u8], format: Option<bool>) -> Outcome {
    let binary = format.unwrap_or_else(|| looks_binary(proof));
    let mut out = Outcome { outcome: Ok(()), clauses: 0, lemmas: 0, deletions: 0, ignored_deletions: 0, core_lemmas: 0, rat_checks: 0, binary };
    let formula = match parse_cnf(cnf) {
        Ok(f) => f,
        Err(e) => {
            out.outcome = Err(e);
            return out;
        }
    };
    let steps_raw = match parse_proof(proof, binary) {
        Ok(s) => s,
        Err(e) => {
            out.outcome = Err(e);
            return out;
        }
    };
    let mut ck = Checker {
        arena: Vec::new(),
        start: Vec::new(),
        len: Vec::new(),
        active: Vec::new(),
        core: Vec::new(),
        pivot: Vec::new(),
        watches: Vec::new(),
        val: Vec::new(),
        reason: Vec::new(),
        trail: Vec::new(),
        seen: Vec::new(),
        chained: Vec::new(),
        pos: Vec::new(),
        top: 0,
        stack: Vec::new(),
        touched: Vec::new(),
        nvars: 0,
    };
    // Clauses by their sorted literals, to find what a deletion refers to.
    let mut by_lits: HashMap<Vec<u32>, Vec<u32>> = HashMap::new();
    out.clauses = formula.len();
    let mut conflict = NONE;
    for c in formula {
        let id = ck.add_clause(c);
        by_lits.entry(ck.lits(id).to_vec()).or_default().push(id);
        if conflict == NONE {
            conflict = ck.activate(id, true);
        }
    }
    if conflict == NONE {
        conflict = ck.propagate(0);
    }
    // Forward pass.
    let mut steps = Vec::with_capacity(steps_raw.len());
    let mut trail_at: HashMap<u32, usize> = HashMap::new();
    if conflict == NONE {
        for (del, c) in steps_raw.into_iter() {
            if del {
                out.deletions += 1;
                let mut key = c.clone();
                key.sort_unstable();
                key.dedup();
                let found = by_lits.get_mut(&key).and_then(|v| v.pop());
                match found {
                    None => {
                        out.ignored_deletions += 1;
                        steps.push(Step::Skip);
                    }
                    Some(id) => {
                        let lits = ck.lits(id);
                        let is_reason = lits.len() == 1 || lits.iter().any(|&l| ck.value(l) == 1 && ck.reason[(l >> 1) as usize] == id);
                        if is_reason {
                            out.ignored_deletions += 1;
                            by_lits.get_mut(&key).unwrap().push(id);
                            steps.push(Step::Skip);
                        } else {
                            ck.active[id as usize] = false;
                            steps.push(Step::Del(id));
                        }
                    }
                }
            } else {
                out.lemmas += 1;
                let id = ck.add_clause(c);
                by_lits.entry(ck.lits(id).to_vec()).or_default().push(id);
                trail_at.insert(id, ck.trail.len());
                steps.push(Step::Add(id));
                let from = ck.trail.len();
                conflict = ck.activate(id, true);
                if conflict == NONE {
                    conflict = ck.propagate(from.min(ck.trail.len()));
                }
                if conflict != NONE {
                    break;
                }
            }
        }
    }
    if conflict == NONE {
        out.outcome = Err("the proof never reaches a conflict: no empty clause can be derived".into());
        return out;
    }
    // Backward pass.
    ck.top = ck.trail.len();
    ck.mark(conflict);
    for k in (0..steps.len()).rev() {
        match steps[k] {
            Step::Skip => {}
            Step::Del(id) => {
                // Back before its deletion: active again, watched on the same two literals as
                // when it was deleted (its literal order has not changed since).
                ck.active[id as usize] = true;
                if ck.len[id as usize] >= 2 {
                    let (a, b) = (ck.lits(id)[0], ck.lits(id)[1]);
                    ck.watches[a as usize].push(id);
                    ck.watches[b as usize].push(id);
                }
            }
            Step::Add(id) => {
                ck.active[id as usize] = false;
                ck.undo_to(trail_at[&id]);
                if !ck.core[id as usize] {
                    continue;
                }
                out.core_lemmas += 1;
                let c = ck.lits(id).to_vec();
                if ck.rup(&c) {
                    continue;
                }
                // RAT on the lemma's first literal as written: for every clause D containing
                // its negation, the lemma plus D without that literal must be RUP.
                out.rat_checks += 1;
                let p = ck.pivot[id as usize];
                let mut ok = false;
                if p != NONE {
                    let partners: Vec<u32> = (0..ck.start.len() as u32)
                        .filter(|&d| ck.active[d as usize] && ck.lits(d).contains(&(p ^ 1)))
                        .collect();
                    ok = partners.iter().all(|&d| {
                        let mut r: Vec<u32> = c.clone();
                        r.extend(ck.lits(d).iter().copied().filter(|&l| l != (p ^ 1)));
                        let good = ck.rup(&r);
                        if good {
                            ck.core[d as usize] = true;
                        }
                        good
                    });
                }
                if !ok {
                    out.outcome = Err(format!("lemma {} (step {}) is neither RUP nor RAT", out.lemmas.min(k + 1), k + 1));
                    return out;
                }
            }
        }
    }
    out
}

#[cfg(test)]
mod tests {
    use super::check;

    // (a ∨ b) (a ∨ ¬b) (¬a ∨ c) (¬a ∨ ¬c): unsatisfiable, but unit propagation alone does not
    // see it (no unit clauses).
    const F: &str = "p cnf 3 4
1 2 0
1 -2 0
-1 3 0
-1 -3 0
";

    fn binary(lines: &[(bool, &[i64])]) -> Vec<u8> {
        let mut out = Vec::new();
        for (del, c) in lines {
            out.push(if *del { b'd' } else { b'a' });
            for &x in *c {
                let mut u = (2 * x.unsigned_abs() + u64::from(x < 0)) as u32;
                while u > 127 {
                    out.push((u & 127) as u8 | 128);
                    u >>= 7;
                }
                out.push(u as u8);
            }
            out.push(0);
        }
        out
    }

    #[test]
    fn a_valid_rup_proof_is_verified_in_both_formats() {
        // "a" is RUP; with it, propagation reaches a conflict and checking stops there.
        let text = check(F.as_bytes(), b"1 0
0
", Some(false));
        assert!(text.outcome.is_ok(), "{:?}", text.outcome);
        assert_eq!(text.lemmas, 1);
        let bin = check(F.as_bytes(), &binary(&[(false, &[1]), (false, &[])]), None);
        assert!(bin.binary && bin.outcome.is_ok());
    }

    #[test]
    fn a_lemma_that_does_not_follow_is_rejected() {
        // Without (¬a ∨ ¬c) the formula is satisfiable: "¬a" is not implied, and no proof works.
        let sat = "p cnf 3 3
1 2 0
1 -2 0
-1 3 0
";
        let r = check(sat.as_bytes(), b"-1 0
0
", Some(false));
        assert!(r.outcome.is_err());
    }

    #[test]
    fn a_proof_that_never_reaches_a_conflict_is_rejected() {
        // "c ∨ a" is RUP but leads nowhere, and there is no empty clause.
        let r = check(F.as_bytes(), b"3 1 0
", Some(false));
        assert!(r.outcome.is_err());
        // An empty clause that does not follow by propagation is rejected too.
        let r = check(F.as_bytes(), b"0
", Some(false));
        assert!(r.outcome.is_err());
    }

    #[test]
    fn deletions_apply_and_unit_deletions_are_ignored() {
        // Deleting (a ∨ ¬b) first: "a" no longer follows.
        let r = check(F.as_bytes(), b"d 1 -2 0
1 0
0
", Some(false));
        assert!(r.outcome.is_err());
        // Deleting the unit "a" that the rest relies on is ignored, as drat-trim does.
        let g = "p cnf 4 6
1 2 0
1 -2 0
-1 3 4 0
-1 3 -4 0
-1 -3 4 0
-1 -3 -4 0
";
        let r = check(g.as_bytes(), b"1 0
d 1 0
3 0
0
", Some(false));
        assert!(r.outcome.is_ok(), "{:?}", r.outcome);
        assert_eq!(r.ignored_deletions, 1);
    }

    #[test]
    fn rat_lemmas_are_checked_on_their_first_literal() {
        // x5 is new: the unit (x5) is not RUP but is RAT (no clause contains ¬x5 when it is
        // added); then (¬x5 ∨ a) is RUP and drives the refutation, so (x5) is in the core.
        let r = check(F.as_bytes(), b"5 0
-5 1 0
0
", Some(false));
        assert!(r.outcome.is_ok(), "{:?}", r.outcome);
        assert_eq!(r.rat_checks, 1);
        // Satisfiable formula with (¬x5 ∨ a): now (x5) is not RAT (x5 ∨ a is not RUP), and
        // a "proof" built on it must be rejected.
        let g = "p cnf 5 4
1 2 0
-1 -2 0
-1 2 0
-5 1 0
";
        let r = check(g.as_bytes(), b"5 0
0
", Some(false));
        assert!(r.outcome.is_err());
    }
}
