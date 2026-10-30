//! Move checker over the typed HIR: use-after-move of owned (`String`) values is a compile-time error
//! (docs/MEMORY.md section 3). Flow-sensitive and conservative: a value moved on *any* path is considered moved
//! afterwards; loop bodies are analysed twice so a move in one iteration is seen by the next.

use crate::diag::{Diag, Span};
use crate::hir::*;

struct Mv<'a> {
    f: &'a HFn,
    moved: Vec<bool>,
    dead: bool,
    /// Per enclosing loop: values moved at some `break`/`continue`.
    exits: Vec<(Vec<bool>, Vec<bool>)>,
    diags: Vec<Diag>,
}

pub fn check(p: &HProgram) -> Vec<Diag> {
    let mut all = Vec::new();
    for f in &p.fns {
        let mut m = Mv { f, moved: vec![false; f.nslots.max(f.nparams)], dead: false, exits: vec![], diags: vec![] };
        m.block(&f.body);
        all.extend(m.diags);
    }
    all
}

impl<'a> Mv<'a> {
    fn name(&self, s: usize) -> String { self.f.slot_names.get(s).cloned().unwrap_or_else(|| format!("${}", s)) }
    fn err(&mut self, span: Span, m: String) { self.diags.push(Diag::new(span, m)); }

    fn block(&mut self, b: &HBlock) {
        for s in &b.stmts { self.stmt(s); }
        if let Some(t) = &b.tail { self.expr(t); }
    }

    fn stmt(&mut self, s: &HStmt) {
        match s {
            HStmt::Let(slot, e) => { self.expr(e); self.moved[*slot] = false; }
            HStmt::Assign(pl, rhs) => {
                self.expr(rhs);
                for pr in &pl.proj { if let Proj::Index(i) = pr { self.expr(i); } }
                // Assigning to an owned local re-initialises it.
                if pl.proj.is_empty() { self.moved[pl.root] = false; }
                else if self.moved[pl.root] { let n = self.name(pl.root); self.err(rhs.span, format!("assignment to a field of moved value `{}`", n)); }
            }
            HStmt::Expr(e) => self.expr(e),
            HStmt::While(c, body) => {
                self.expr(c);
                let before = self.moved.clone();
                let n = before.len();
                self.exits.push((vec![false; n], vec![false; n]));
                self.block(body);
                // State carried to the next iteration: the end of the body (if reachable) and every `continue`/`break`.
                let mut carry = self.exits.last().unwrap().1.clone();
                if !self.dead { for (c2, m) in carry.iter_mut().zip(&self.moved) { *c2 = *c2 || *m; } }
                // second pass: what the body moved is visible to the next iteration
                self.moved = before.iter().zip(&carry).map(|(b, c2)| *b || *c2).collect();
                self.dead = false;
                self.expr(c);
                self.block(body);
                let (exits, conts) = self.exits.pop().unwrap();
                let mut fin: Vec<bool> = (0..n).map(|i| before[i] || carry[i] || exits[i] || conts[i]).collect();
                if !self.dead { for (f, m) in fin.iter_mut().zip(&self.moved) { *f = *f || *m; } }
                self.moved = fin;
                self.dead = false;
            }
            HStmt::Break | HStmt::Continue => {
                if let Some(x) = self.exits.last_mut() {
                    // `break` leaves the loop; `continue` feeds the next iteration
                    let t = if matches!(s, HStmt::Break) { &mut x.0 } else { &mut x.1 };
                    for (a, m) in t.iter_mut().zip(&self.moved) { *a = *a || *m; }
                }
                self.dead = true;
            }
            HStmt::Return(e) => { if let Some(e) = e { self.expr(e); } self.dead = true; }
            HStmt::Drop(_) => {}
        }
    }

    /// Run `f` from the current state; returns the resulting (moved, dead) and restores nothing.
    fn branch(&mut self, start: &[bool], f: impl FnOnce(&mut Self)) -> (Vec<bool>, bool) {
        self.moved = start.to_vec();
        self.dead = false;
        f(self);
        (self.moved.clone(), self.dead)
    }

    fn merge(&mut self, arms: Vec<(Vec<bool>, bool)>) {
        let live: Vec<&(Vec<bool>, bool)> = arms.iter().filter(|a| !a.1).collect();
        if live.is_empty() {
            self.dead = true;
            self.moved = arms.into_iter().next().map(|a| a.0).unwrap_or_default();
            return;
        }
        let mut m = vec![false; self.moved.len()];
        for a in live { for (x, y) in m.iter_mut().zip(&a.0) { *x = *x || *y; } }
        self.moved = m;
        self.dead = false;
    }

    fn expr(&mut self, e: &HExpr) {
        match &e.kind {
            HKind::Lit(_) => {}
            HKind::Local(s) => {
                if self.moved[*s] { let n = self.name(*s); self.err(e.span, format!("use of moved value `{}` (it was moved earlier, possibly in a previous loop iteration or another branch)", n)); }
            }
            HKind::Move(s) => {
                if self.moved[*s] { let n = self.name(*s); self.err(e.span, format!("use of moved value `{}` (it was moved earlier, possibly in a previous loop iteration or another branch)", n)); }
                self.moved[*s] = true;
            }
            HKind::AddrOf(pl, _) => {
                for pr in &pl.proj { if let Proj::Index(i) = pr { self.expr(i); } }
                if self.moved[pl.root] { let n = self.name(pl.root); self.err(e.span, format!("borrow of moved value `{}`", n)); }
            }
            HKind::Unary(_, x) | HKind::Cast(x) | HKind::Repeat(x, _) | HKind::Field(x, _) | HKind::Deref(x) => self.expr(x),
            HKind::Binary(_, a, b) | HKind::Index(a, b) => { self.expr(a); self.expr(b); }
            HKind::Call(_, xs) | HKind::Builtin(_, xs) | HKind::Array(xs) | HKind::Variant(_, xs) => for x in xs { self.expr(x); },
            HKind::Struct(_, fs) => for (_, x) in fs { self.expr(x); },
            HKind::Block(b) => self.block(b),
            HKind::If(c, t, el) => {
                self.expr(c);
                let start = self.moved.clone();
                let a = self.branch(&start, |s| s.block(t));
                let b = match el { Some(b) => self.branch(&start, |s| s.block(b)), None => (start.clone(), false) };
                self.merge(vec![a, b]);
            }
            HKind::Match(s, arms) => {
                self.expr(s);
                let start = self.moved.clone();
                let mut results = Vec::new();
                for a in arms {
                    results.push(self.branch(&start, |m| {
                        // pattern bindings are (re)initialised when the arm is entered
                        let mut bs = Vec::new();
                        pat_slots(&a.pat, &mut bs);
                        for b in bs { m.moved[b] = false; }
                        m.expr(&a.body)
                    }));
                }
                if !results.is_empty() { self.merge(results); }
            }
        }
    }
}

fn pat_slots(p: &HPat, out: &mut Vec<usize>) {
    match p {
        HPat::Bind(s) => out.push(*s),
        HPat::Variant(_, subs) => for s in subs { pat_slots(s, out); },
        HPat::Wild | HPat::Lit(..) => {}
    }
}
