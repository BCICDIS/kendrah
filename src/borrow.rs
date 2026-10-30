//! Borrow checker over the typed HIR (rules: docs/MEMORY.md section 2).
//!
//! References are second-class (parameters and `let` locals only), so loans are tracked lexically: a loan made
//! by `let r = &place;` lasts until the end of the enclosing block, and a loan made for a call argument lasts until
//! the call returns. The pass is conservative: it may reject safe programs, never accept aliasing ones.

use crate::diag::{Diag, Span};
use crate::hir::*;
use crate::ty::Ty;

#[derive(Clone, Copy, PartialEq, Debug)]
enum Key { Deref, Field(usize), Any }

#[derive(Clone, Copy, PartialEq, Debug)]
enum Acc { Read, Write, Shared, Mut, Move }

struct Loan { root: usize, path: Vec<Key>, mutable: bool, span: Span }

struct Cx<'a> {
    p: &'a HProgram,
    f: &'a HFn,
    loans: Vec<Loan>,
    diags: Vec<Diag>,
}

/// Check every function; returns diagnostics sorted by position.
pub fn check(p: &HProgram) -> Vec<Diag> {
    let mut all = Vec::new();
    for f in &p.fns {
        let mut cx = Cx { p, f, loans: vec![], diags: vec![] };
        cx.block(&f.body);
        all.extend(cx.diags);
    }
    all.sort_by_key(|d| (d.span.line, d.span.col));
    all.dedup();
    all
}

fn overlap(a: &[Key], b: &[Key]) -> bool {
    for (x, y) in a.iter().zip(b) {
        if let (Key::Field(i), Key::Field(j)) = (x, y) { if i != j { return false; } }
    }
    true
}

/// Root slot and key path of a pure place chain (`x`, `x.f`, `x[i]`, `*r`, `r.f`...). Index expressions are not evaluated here.
fn chain_path(e: &HExpr) -> Option<(usize, Vec<Key>)> {
    match &e.kind {
        HKind::Local(s) => Some((*s, vec![])),
        HKind::Deref(b) => { let (r, mut p) = chain_path(b)?; p.push(Key::Deref); Some((r, p)) }
        HKind::Field(b, i) => { let (r, mut p) = chain_path(b)?; p.push(Key::Field(*i)); Some((r, p)) }
        HKind::Index(b, _) => { let (r, mut p) = chain_path(b)?; p.push(Key::Any); Some((r, p)) }
        _ => None,
    }
}

fn place_keys(pl: &HPlace) -> Vec<Key> {
    pl.proj.iter().map(|p| match p { Proj::Deref => Key::Deref, Proj::Field(i) => Key::Field(*i), Proj::Index(_) => Key::Any }).collect()
}

impl<'a> Cx<'a> {
    fn name(&self, slot: usize) -> String { self.f.slot_names.get(slot).cloned().unwrap_or_else(|| format!("${}", slot)) }

    fn err(&mut self, span: Span, m: String) { self.diags.push(Diag::new(span, m)); }

    fn access(&mut self, root: usize, path: &[Key], acc: Acc, span: Span) {
        let hit = self.loans.iter().find(|l| {
            l.root == root && overlap(&l.path, path) && match acc {
                Acc::Read | Acc::Shared => l.mutable,
                Acc::Write | Acc::Mut | Acc::Move => true,
            }
        }).map(|l| (l.span, l.mutable));
        if let Some((ls, lm)) = hit {
            let n = self.name(root);
            let through = if path.first() == Some(&Key::Deref) { format!("`*{}`", n) } else { format!("`{}`", n) };
            let at = format!("(the {} borrow is at {}:{})", if lm { "mutable" } else { "shared" }, ls.line, ls.col);
            let m = match acc {
                Acc::Read => format!("cannot use {} because it is mutably borrowed {}", through, at),
                Acc::Write => format!("cannot assign to {} because it is borrowed {}", through, at),
                Acc::Move => format!("cannot move out of {} because it is borrowed {}", through, at),
                Acc::Shared => format!("cannot borrow {} as shared because it is mutably borrowed {}", through, at),
                Acc::Mut => format!("cannot borrow {} as mutable because it is already borrowed {}", through, at),
            };
            self.err(span, m);
        }
    }

    /// Evaluate the index expressions of a place, check the borrow, and register the loan.
    fn borrow(&mut self, pl: &HPlace, m: bool, span: Span) {
        self.place_indices(pl);
        let path = place_keys(pl);
        self.access(pl.root, &path, if m { Acc::Mut } else { Acc::Shared }, span);
        self.loans.push(Loan { root: pl.root, path, mutable: m, span });
    }

    fn place_indices(&mut self, pl: &HPlace) {
        for pr in &pl.proj { if let Proj::Index(i) = pr { self.expr(i); } }
    }

    fn block(&mut self, b: &HBlock) {
        let mark = self.loans.len();
        for s in &b.stmts { self.stmt(s); }
        if let Some(t) = &b.tail { self.expr(t); }
        self.loans.truncate(mark);
    }

    fn stmt(&mut self, s: &HStmt) {
        match s {
            HStmt::Let(_, init) => match &init.kind {
                // The loan outlives this statement: it stays until the enclosing block ends.
                HKind::AddrOf(pl, m) => self.borrow(pl, *m, init.span),
                _ => self.expr(init),
            },
            HStmt::Assign(pl, rhs) => {
                self.expr(rhs);
                self.place_indices(pl);
                let path = place_keys(pl);
                self.access(pl.root, &path, Acc::Write, rhs.span);
            }
            HStmt::Expr(e) => self.expr(e),
            HStmt::While(c, b) => { self.expr(c); self.block(b); }
            HStmt::Return(e) => { if let Some(e) = e { self.expr(e); } }
            HStmt::Break | HStmt::Continue => {}
            HStmt::Drop(_) => {}
        }
    }

    fn expr(&mut self, e: &HExpr) {
        match &e.kind {
            HKind::Lit(_) => {}
            HKind::Local(s) => self.access(*s, &[], Acc::Read, e.span),
            // Moving out invalidates any outstanding loan of the value.
            HKind::Move(s) => self.access(*s, &[], Acc::Move, e.span),
            HKind::Deref(_) | HKind::Field(..) | HKind::Index(..) => {
                if let Some((root, path)) = chain_path(e) {
                    self.chain_indices(e);
                    self.access(root, &path, Acc::Read, e.span);
                } else {
                    match &e.kind {
                        HKind::Field(b, _) => self.expr(b),
                        HKind::Index(b, i) => { self.expr(b); self.expr(i); }
                        HKind::Deref(b) => self.expr(b),
                        _ => unreachable!(),
                    }
                }
            }
            HKind::Unary(_, x) | HKind::Cast(x) | HKind::Repeat(x, _) => self.expr(x),
            HKind::Binary(_, a, b) => { self.expr(a); self.expr(b); }
            HKind::Call(id, args) => {
                let mark = self.loans.len();
                let params = &self.p.fns[*id].params;
                for (i, a) in args.iter().enumerate() {
                    match (&a.kind, &a.ty) {
                        (HKind::AddrOf(pl, m), _) => self.borrow(pl, *m, a.span),
                        (HKind::Local(r), Ty::Ref(..)) => {
                            // Passing a reference re-borrows its referent for the duration of the call.
                            let want_mut = matches!(params.get(i), Some(Ty::Ref(_, true)));
                            let path = [Key::Deref];
                            self.access(*r, &path, if want_mut { Acc::Mut } else { Acc::Shared }, a.span);
                            self.loans.push(Loan { root: *r, path: path.to_vec(), mutable: want_mut, span: a.span });
                        }
                        _ => self.expr(a),
                    }
                }
                self.loans.truncate(mark);
            }
            // Borrow arguments of builtins live only for the call, like call-argument temporaries.
            HKind::Builtin(_, xs) => {
                let mark = self.loans.len();
                for x in xs { self.expr(x); }
                self.loans.truncate(mark);
            }
            HKind::Array(xs) | HKind::Variant(_, xs) => for x in xs { self.expr(x); },
            HKind::Struct(_, fs) => for (_, x) in fs { self.expr(x); },
            HKind::If(c, t, el) => { self.expr(c); self.block(t); if let Some(b) = el { self.block(b); } }
            HKind::Block(b) => self.block(b),
            HKind::Match(s, arms) => { self.expr(s); for a in arms { self.expr(&a.body); } }
            // A borrow in any other position cannot occur (the checker only allows `let` initialisers and call arguments).
            HKind::AddrOf(pl, m) => self.borrow(pl, *m, e.span),
        }
    }

    /// Evaluate the index sub-expressions inside a chain (for their own borrow checking).
    fn chain_indices(&mut self, e: &HExpr) {
        match &e.kind {
            HKind::Deref(b) | HKind::Field(b, _) => self.chain_indices(b),
            HKind::Index(b, i) => { self.chain_indices(b); self.expr(i); }
            _ => {}
        }
    }
}
