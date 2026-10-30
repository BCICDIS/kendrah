//! Drop elaboration (HIR -> HIR, runs after all checks). Makes ownership explicit so every engine executes the
//! same drops: owned locals are dropped in reverse declaration order at the end of their block and before every
//! `return`; discarded owned temporaries and overwritten owned values are dropped. `HStmt::Drop` is a no-op on a
//! value that was moved out, so no static drop flags are needed. See docs/MEMORY.md section 3.

use crate::diag::Span;
use crate::hir::*;
use crate::ty::Ty;

pub fn elaborate(p: &mut HProgram) {
    let (ss, es) = (p.structs.clone(), p.enums.clone());
    for f in &mut p.fns { elaborate_fn(f, &ss, &es); }
}

struct El {
    structs: Vec<StructDef>,
    enums: Vec<EnumDef>,
    tys: Vec<Ty>,
    names: Vec<String>,
    scopes: Vec<Vec<usize>>,
    /// `scopes.len()` when each enclosing loop body was entered.
    loops: Vec<usize>,
    /// Slots already live when the next block's scope opens (owned `match` arm bindings).
    seed: Vec<usize>,
}

fn pat_slots(p: &HPat, out: &mut Vec<usize>) {
    match p {
        HPat::Bind(s) => out.push(*s),
        HPat::Variant(_, subs) => for s in subs { pat_slots(s, out); },
        HPat::Wild | HPat::Lit(..) => {}
    }
}


fn elaborate_fn(f: &mut HFn, ss: &[StructDef], es: &[EnumDef]) {
    let owned = |t: &Ty| owned_ty(t, ss, es);
    let mut el = El { structs: ss.to_vec(), enums: es.to_vec(), tys: f.slot_tys.clone(), names: f.slot_names.clone(), scopes: vec![], loops: vec![], seed: vec![] };
    let params: Vec<usize> = (0..f.nparams).filter(|i| owned(&f.slot_tys[*i])).collect();
    el.scopes.push(params.clone());
    el.block(&mut f.body, Some(&params));
    f.slot_tys = el.tys;
    f.slot_names = el.names;
    f.nslots = f.slot_tys.len();
}

fn place(slot: usize) -> HPlace { HPlace { root: slot, proj: vec![] } }
fn sp() -> Span { Span::default() }

impl El {
    fn owned(&self, t: &Ty) -> bool { owned_ty(t, &self.structs, &self.enums) }

    fn tmp(&mut self, ty: Ty) -> usize {
        self.tys.push(ty);
        self.names.push("<temp>".into());
        self.tys.len() - 1
    }

    fn read(&self, slot: usize, span: Span) -> HExpr {
        let ty = self.tys[slot].clone();
        HExpr { kind: if self.owned(&ty) { HKind::Move(slot) } else { HKind::Local(slot) }, ty, span }
    }

    /// Slots to drop when leaving every enclosing scope (innermost first, reverse declaration order).
    fn all_live(&self) -> Vec<usize> { self.scopes.iter().rev().flat_map(|s| s.iter().rev().copied()).collect() }

    fn block(&mut self, b: &mut HBlock, fn_params: Option<&Vec<usize>>) {
        let seed = std::mem::take(&mut self.seed);
        self.scopes.push(seed);
        let old = std::mem::take(&mut b.stmts);
        let mut out: Vec<HStmt> = Vec::with_capacity(old.len());
        for s in old { self.stmt(s, &mut out); }
        let mut tail = b.tail.take();
        if let Some(t) = &mut tail { self.expr(t); }
        let mut drops: Vec<usize> = self.scopes.pop().unwrap().into_iter().rev().collect();
        if let Some(ps) = fn_params { drops.extend(ps.iter().rev().copied()); }
        let ends_in_return = matches!(out.last(), Some(HStmt::Return(_) | HStmt::Break | HStmt::Continue));
        let diverging_tail = tail.as_ref().map_or(false, |t| t.ty == Ty::Never);
        if drops.is_empty() || ends_in_return || diverging_tail {
            b.stmts = out;
            b.tail = tail;
            return;
        }
        match tail {
            None => { for d in drops { out.push(HStmt::Drop(place(d))); } b.tail = None; }
            Some(t) if t.ty == Ty::Unit => {
                out.push(HStmt::Expr(*t));
                for d in drops { out.push(HStmt::Drop(place(d))); }
                b.tail = None;
            }
            Some(t) => {
                let span = t.span;
                let tmp = self.tmp(t.ty.clone());
                out.push(HStmt::Let(tmp, *t));
                for d in drops { out.push(HStmt::Drop(place(d))); }
                b.tail = Some(Box::new(self.read(tmp, span)));
            }
        }
        b.stmts = out;
    }

    fn stmt(&mut self, s: HStmt, out: &mut Vec<HStmt>) {
        match s {
            HStmt::Let(slot, mut e) => {
                self.expr(&mut e);
                if self.owned(&self.tys[slot].clone()) { self.scopes.last_mut().unwrap().push(slot); }
                out.push(HStmt::Let(slot, e));
            }
            HStmt::Assign(pl, mut rhs) => {
                self.expr(&mut rhs);
                if self.owned(&rhs.ty) {
                    // evaluate the right-hand side first (it may read the old value), then drop the old value, then store
                    let span = rhs.span;
                    let tmp = self.tmp(rhs.ty.clone());
                    out.push(HStmt::Let(tmp, rhs));
                    out.push(HStmt::Drop(pl.clone()));
                    out.push(HStmt::Assign(pl, self.read(tmp, span)));
                } else {
                    let mut pl = pl;
                    for pr in &mut pl.proj { if let Proj::Index(i) = pr { self.expr(i); } }
                    out.push(HStmt::Assign(pl, rhs));
                }
            }
            HStmt::Expr(mut e) => {
                self.expr(&mut e);
                if self.owned(&e.ty) {
                    let tmp = self.tmp(e.ty.clone());
                    out.push(HStmt::Let(tmp, e));
                    out.push(HStmt::Drop(place(tmp)));
                } else { out.push(HStmt::Expr(e)); }
            }
            HStmt::While(mut c, mut body) => {
                self.expr(&mut c);
                self.loops.push(self.scopes.len());
                self.block(&mut body, None);
                self.loops.pop();
                out.push(HStmt::While(c, body));
            }
            HStmt::Return(e) => {
                let live = self.all_live();
                match e {
                    None => { for d in live { out.push(HStmt::Drop(place(d))); } out.push(HStmt::Return(None)); }
                    Some(mut e) => {
                        self.expr(&mut e);
                        if live.is_empty() { out.push(HStmt::Return(Some(e))); return; }
                        if e.ty == Ty::Unit {
                            out.push(HStmt::Expr(e));
                            for d in live { out.push(HStmt::Drop(place(d))); }
                            out.push(HStmt::Return(None));
                        } else {
                            let span = e.span;
                            let tmp = self.tmp(e.ty.clone());
                            out.push(HStmt::Let(tmp, e));
                            for d in live { out.push(HStmt::Drop(place(d))); }
                            let r = self.read(tmp, span);
                            out.push(HStmt::Return(Some(r)));
                        }
                    }
                }
            }
            HStmt::Drop(p) => out.push(HStmt::Drop(p)),
            s @ (HStmt::Break | HStmt::Continue) => {
                // leave every scope opened inside the loop body
                let mark = *self.loops.last().expect("checked: break/continue only inside loops");
                let live: Vec<usize> = self.scopes[mark..].iter().rev().flat_map(|s| s.iter().rev().copied()).collect();
                for d in live { out.push(HStmt::Drop(place(d))); }
                out.push(s);
            }
        }
    }

    fn expr(&mut self, e: &mut HExpr) {
        let _ = sp;
        match &mut e.kind {
            HKind::Lit(_) | HKind::Local(_) | HKind::Move(_) => {}
            HKind::AddrOf(pl, _) => { for pr in &mut pl.proj { if let Proj::Index(i) = pr { self.expr(i); } } }
            HKind::Unary(_, x) | HKind::Cast(x) | HKind::Repeat(x, _) | HKind::Field(x, _) | HKind::Deref(x) => self.expr(x),
            HKind::Binary(_, a, b) | HKind::Index(a, b) => { self.expr(a); self.expr(b); }
            HKind::Call(_, xs) | HKind::Builtin(_, xs) | HKind::Array(xs) | HKind::Variant(_, xs) => for x in xs { self.expr(x); },
            HKind::Struct(_, fs) => for (_, x) in fs { self.expr(x); },
            HKind::Block(b) => self.block(b, None),
            HKind::If(c, t, el) => { self.expr(c); self.block(t, None); if let Some(b) = el { self.block(b, None); } }
            HKind::Match(s, arms) => {
                self.expr(s);
                for a in arms {
                    // owned bindings live exactly as long as the arm body and are dropped when it ends
                    let mut binds = Vec::new();
                    pat_slots(&a.pat, &mut binds);
                    binds.retain(|b| owned_ty(&self.tys[*b], &self.structs, &self.enums));
                    if binds.is_empty() { self.expr(&mut a.body); continue; }
                    let span = a.body.span;
                    let ty = a.body.ty.clone();
                    let body = std::mem::replace(&mut a.body, HExpr { kind: HKind::Lit(Value::Unit), ty: Ty::Unit, span });
                    let mut blk = HBlock { stmts: vec![], tail: Some(Box::new(body)) };
                    self.seed = binds;
                    self.block(&mut blk, None);
                    a.body = HExpr { kind: HKind::Block(blk), ty, span };
                }
            }
        }
    }
}
