//! HIR -> UIR lowering (docs/UIR.md section 5).
//!
//! Strategy: every HIR local becomes a UIR slot with the same index; expression results are temps; any value
//! that must survive control flow (the result of `if`/`match`/`&&`/`||`, scrutinees, spilled operands) goes
//! through a slot, because temps never cross basic blocks.

use crate::ast::BinOp;
use crate::diag::Span;
use crate::hir::*;
use crate::ty::Ty;
use crate::uir::*;

pub fn lower_program(h: &HProgram) -> UProgram {
    UProgram {
        fns: h.fns.iter().map(|f| lower_fn(h, f)).collect(),
        structs: h.structs.clone(),
        enums: h.enums.clone(),
        main: h.main,
    }
}

struct L<'a> {
    h: &'a HProgram,
    slots: Vec<Ty>,
    temps: Vec<Ty>,
    blocks: Vec<(Vec<UInstr>, Option<UTerm>)>,
    cur: BlockId,
    /// True while emitting into a block that cannot be reached (after `return`).
    dead: bool,
    /// (continue target, break target) of the enclosing loops.
    loops: Vec<(BlockId, BlockId)>,
}

fn lower_fn(h: &HProgram, f: &HFn) -> UFn {
    if f.ext == crate::ast::Ext::Import {
        // a C function: no body to lower; the single block is a trap so the verifier's shape rules hold
        return UFn { name: f.name.clone(), layer: f.layer, ext: f.ext, nparams: f.nparams, ret: f.ret.clone(), slots: f.slot_tys.clone(), temps: vec![],
            blocks: vec![UBlock { instrs: vec![], term: UTerm::Trap("extern function has no body") }] };
    }
    let mut l = L { h, slots: f.slot_tys.clone(), temps: vec![], blocks: vec![(vec![], None)], cur: 0, dead: false, loops: vec![] };
    let v = l.block(&f.body);
    if !l.dead { l.term(UTerm::Ret(v)); }
    let blocks = l.blocks.into_iter()
        .map(|(instrs, t)| UBlock { instrs, term: t.unwrap_or(UTerm::Trap("unreachable")) })
        .collect();
    UFn { name: f.name.clone(), layer: f.layer, ext: f.ext, nparams: f.nparams, ret: f.ret.clone(), slots: l.slots, temps: l.temps, blocks }
}

fn simple(e: &HExpr) -> bool {
    match &e.kind {
        HKind::Lit(_) | HKind::Local(_) | HKind::Move(_) => true,
        HKind::AddrOf(pl, _) => pl.proj.iter().all(|p| match p { Proj::Index(i) => simple(i), _ => true }),
        HKind::Unary(_, x) | HKind::Cast(x) | HKind::Field(x, _) | HKind::Repeat(x, _) | HKind::Deref(x) => simple(x),
        HKind::Binary(op, a, b) => !matches!(op, BinOp::And | BinOp::Or) && simple(a) && simple(b),
        HKind::Index(a, b) => simple(a) && simple(b),
        HKind::Call(_, xs) | HKind::Builtin(_, xs) | HKind::Array(xs) | HKind::Variant(_, xs) => xs.iter().all(simple),
        HKind::Struct(_, fs) => fs.iter().all(|(_, x)| simple(x)),
        HKind::If(..) | HKind::Block(_) | HKind::Match(..) => false,
    }
}

fn is_chain(e: &HExpr) -> bool {
    match &e.kind {
        HKind::Local(_) => true,
        HKind::Field(b, _) | HKind::Index(b, _) | HKind::Deref(b) => is_chain(b),
        _ => false,
    }
}

enum Step<'a> { Deref, Field(usize), Index(&'a HExpr) }

fn chain_steps<'a>(e: &'a HExpr, out: &mut Vec<Step<'a>>) -> usize {
    match &e.kind {
        HKind::Local(s) => *s,
        HKind::Deref(b) => { let r = chain_steps(b, out); out.push(Step::Deref); r }
        HKind::Field(b, i) => { let r = chain_steps(b, out); out.push(Step::Field(*i)); r }
        HKind::Index(b, ie) => { let r = chain_steps(b, out); out.push(Step::Index(ie)); r }
        _ => unreachable!("is_chain checked"),
    }
}

impl<'a> L<'a> {
    fn new_block(&mut self) -> BlockId { self.blocks.push((vec![], None)); self.blocks.len() - 1 }
    fn switch(&mut self, b: BlockId) { self.cur = b; self.dead = false; }
    fn new_slot(&mut self, t: Ty) -> Slot { self.slots.push(t); self.slots.len() - 1 }

    fn emit(&mut self, op: UOp, ty: Ty, span: Span) -> Temp {
        let t = self.temps.len();
        self.temps.push(ty);
        self.blocks[self.cur].0.push(UInstr { dest: Some(t), op, span });
        t
    }
    fn emit_void(&mut self, op: UOp, span: Span) { self.blocks[self.cur].0.push(UInstr { dest: None, op, span }); }

    fn term(&mut self, t: UTerm) {
        if self.blocks[self.cur].1.is_none() { self.blocks[self.cur].1 = Some(t); }
    }
    /// Branch to `target` if the current position is reachable.
    fn br(&mut self, target: BlockId) { if !self.dead { self.term(UTerm::Br(target)); } }
    fn ret(&mut self, t: Temp) {
        if !self.dead { self.term(UTerm::Ret(t)); }
        let nb = self.new_block();
        self.switch(nb);
        self.dead = true;
    }

    fn unit(&mut self, span: Span) -> Temp { self.emit(UOp::Const(Value::Unit), Ty::Unit, span) }

    /// Evaluate `es` left to right so that every returned temp is usable in the *current* block afterwards,
    /// spilling earlier operands through slots when a later operand contains control flow.
    fn operands(&mut self, es: &[&HExpr]) -> Vec<Temp> {
        let n = es.len();
        let mut temps = Vec::with_capacity(n);
        let mut spills: Vec<Option<(Slot, Ty)>> = Vec::with_capacity(n);
        for k in 0..n {
            let t = self.expr(es[k]);
            let later_complex = es[k + 1..].iter().any(|e| !simple(e));
            if later_complex {
                let ty = self.temps[t].clone();
                let s = self.new_slot(ty.clone());
                self.emit_void(UOp::Store(s, t), es[k].span);
                spills.push(Some((s, ty)));
            } else { spills.push(None); }
            temps.push(t);
        }
        for k in 0..n {
            if let Some((s, ty)) = spills[k].take() { temps[k] = self.emit(UOp::Load(s), ty, es[k].span); }
        }
        temps
    }

    fn block(&mut self, b: &HBlock) -> Temp {
        for s in &b.stmts { self.stmt(s); }
        match &b.tail {
            Some(e) => self.expr(e),
            None => self.unit(Span::default()),
        }
    }

    fn stmt(&mut self, s: &HStmt) {
        match s {
            HStmt::Let(slot, e) => { let t = self.expr(e); self.emit_void(UOp::Store(*slot, t), e.span); }
            HStmt::Expr(e) => { self.expr(e); }
            HStmt::Drop(place) => {
                let projs = place.proj.iter().map(|p| match p {
                    Proj::Deref => UProj::Deref,
                    Proj::Field(i) => UProj::Field(*i),
                    Proj::Index(_) => unreachable!("arrays never hold owned values"),
                }).collect();
                self.emit_void(UOp::Drop(place.root, projs), Span::default());
            }
            HStmt::Assign(place, e) => {
                let idx: Vec<&HExpr> = place.proj.iter().filter_map(|p| if let Proj::Index(i) = p { Some(i) } else { None }).collect();
                let mut all: Vec<&HExpr> = vec![e];
                all.extend(idx.iter().copied());
                let ts = self.operands(&all);
                let mut k = 1;
                let projs = place.proj.iter().map(|p| match p {
                    Proj::Deref => UProj::Deref,
                    Proj::Field(i) => UProj::Field(*i),
                    Proj::Index(ie) => { let t = ts[k]; k += 1; UProj::Index(t, ie.span) }
                }).collect();
                self.emit_void(UOp::StoreProj(place.root, projs, ts[0]), e.span);
            }
            HStmt::While(c, body) => {
                let head = self.new_block();
                self.br(head);
                self.switch(head);
                let ct = self.expr(c);
                let (bb, exit) = (self.new_block(), self.new_block());
                self.term(UTerm::CondBr(ct, bb, exit));
                self.switch(bb);
                self.loops.push((head, exit));
                self.block(body);
                self.loops.pop();
                self.br(head);
                self.switch(exit);
            }
            HStmt::Break | HStmt::Continue => {
                let (cont, brk) = *self.loops.last().expect("checked: inside a loop");
                self.br(if matches!(s, HStmt::Break) { brk } else { cont });
                let nb = self.new_block();
                self.switch(nb);
                self.dead = true;
            }
            HStmt::Return(e) => {
                let t = match e { Some(e) => self.expr(e), None => self.unit(Span::default()) };
                self.ret(t);
            }
        }
    }

    fn result_slot(&mut self, ty: &Ty) -> Option<Slot> {
        if matches!(ty, Ty::Unit | Ty::Never) { None } else { Some(self.new_slot(ty.clone())) }
    }

    fn join_value(&mut self, slot: Option<Slot>, ty: &Ty, span: Span) -> Temp {
        match (slot, ty) {
            (Some(s), _) => self.emit(UOp::Load(s), ty.clone(), span),
            (None, Ty::Never) => self.emit(UOp::Const(Value::Unit), Ty::Never, span),
            (None, _) => self.unit(span),
        }
    }

    fn expr(&mut self, e: &HExpr) -> Temp {
        let span = e.span;
        match &e.kind {
            HKind::Lit(v) => self.emit(UOp::Const(v.clone()), e.ty.clone(), span),
            HKind::Local(s) => self.emit(UOp::Load(*s), e.ty.clone(), span),
            HKind::Move(s) => self.emit(UOp::Take(*s), e.ty.clone(), span),
            HKind::Unary(op, x) => { let t = self.expr(x); self.emit(UOp::Unary(*op, t), e.ty.clone(), span) }
            HKind::Binary(op @ (BinOp::And | BinOp::Or), l, r) => {
                let res = self.new_slot(Ty::Bool);
                let a = self.expr(l);
                self.emit_void(UOp::Store(res, a), span);
                let (rhs, end) = (self.new_block(), self.new_block());
                if *op == BinOp::And { self.term(UTerm::CondBr(a, rhs, end)); } else { self.term(UTerm::CondBr(a, end, rhs)); }
                self.switch(rhs);
                let b = self.expr(r);
                self.emit_void(UOp::Store(res, b), span);
                self.br(end);
                self.switch(end);
                self.emit(UOp::Load(res), Ty::Bool, span)
            }
            HKind::Binary(op, l, r) => {
                let ts = self.operands(&[l, r]);
                self.emit(UOp::Binary(*op, ts[0], ts[1]), e.ty.clone(), span)
            }
            HKind::Call(id, args) => {
                let refs: Vec<&HExpr> = args.iter().collect();
                let ts = self.operands(&refs);
                self.emit(UOp::Call(*id, ts), e.ty.clone(), span)
            }
            HKind::Builtin(b, args) => {
                let refs: Vec<&HExpr> = args.iter().collect();
                let ts = self.operands(&refs);
                self.emit(UOp::Builtin(*b, ts), e.ty.clone(), span)
            }
            HKind::If(c, then, els) => {
                let ct = self.expr(c);
                let res = self.result_slot(&e.ty);
                let (tb, join) = (self.new_block(), self.new_block());
                let eb = if els.is_some() { self.new_block() } else { join };
                self.term(UTerm::CondBr(ct, tb, eb));
                self.switch(tb);
                let v = self.block(then);
                if let (Some(s), false) = (res, self.dead) { self.emit_void(UOp::Store(s, v), span); }
                self.br(join);
                if let Some(b) = els {
                    self.switch(eb);
                    let v = self.block(b);
                    if let (Some(s), false) = (res, self.dead) { self.emit_void(UOp::Store(s, v), span); }
                    self.br(join);
                }
                self.switch(join);
                self.join_value(res, &e.ty, span)
            }
            HKind::Block(b) => self.block(b),
            HKind::Cast(x) => { let t = self.expr(x); self.emit(UOp::Cast(t), e.ty.clone(), span) }
            HKind::Struct(id, fields) => {
                let refs: Vec<&HExpr> = fields.iter().map(|(_, x)| x).collect();
                let ts = self.operands(&refs);
                let fs = fields.iter().zip(ts).map(|((i, _), t)| (*i, t)).collect();
                self.emit(UOp::MakeStruct(*id, fs), e.ty.clone(), span)
            }
            HKind::AddrOf(place, _) => {
                let idx: Vec<&HExpr> = place.proj.iter().filter_map(|p| if let Proj::Index(i) = p { Some(i) } else { None }).collect();
                let ts = self.operands(&idx);
                let mut k = 0;
                let projs = place.proj.iter().map(|p| match p {
                    Proj::Deref => UProj::Deref,
                    Proj::Field(i) => UProj::Field(*i),
                    Proj::Index(ie) => { let t = ts[k]; k += 1; UProj::Index(t, ie.span) }
                }).collect();
                self.emit(UOp::AddrOf(place.root, projs), e.ty.clone(), span)
            }
            HKind::Field(..) | HKind::Index(..) | HKind::Deref(_) if is_chain(e) => {
                let mut steps = Vec::new();
                let root = chain_steps(e, &mut steps);
                let idx: Vec<&HExpr> = steps.iter().filter_map(|s| if let Step::Index(i) = s { Some(*i) } else { None }).collect();
                let ts = self.operands(&idx);
                let mut k = 0;
                let projs = steps.iter().map(|s| match s {
                    Step::Deref => UProj::Deref,
                    Step::Field(i) => UProj::Field(*i),
                    Step::Index(ie) => { let t = ts[k]; k += 1; UProj::Index(t, ie.span) }
                }).collect();
                self.emit(UOp::LoadProj(root, projs), e.ty.clone(), span)
            }
            HKind::Deref(_) => unreachable!("checked program: deref operand is a local"),
            HKind::Field(b, i) => { let t = self.expr(b); self.emit(UOp::Field(t, *i), e.ty.clone(), span) }
            HKind::Index(b, ie) => {
                let ts = self.operands(&[b, ie]);
                self.emit(UOp::Index(ts[0], ts[1], ie.span), e.ty.clone(), span)
            }
            HKind::Array(xs) => {
                let refs: Vec<&HExpr> = xs.iter().collect();
                let ts = self.operands(&refs);
                self.emit(UOp::MakeArray(ts), e.ty.clone(), span)
            }
            HKind::Repeat(x, n) => { let t = self.expr(x); self.emit(UOp::Repeat(t, *n), e.ty.clone(), span) }
            HKind::Variant(vi, args) => {
                let refs: Vec<&HExpr> = args.iter().collect();
                let ts = self.operands(&refs);
                self.emit(UOp::MakeVariant(*vi, ts), e.ty.clone(), span)
            }
            HKind::Match(s, arms) => {
                let st = self.expr(s);
                let sty = self.temps[st].clone();
                let owned_scrut = crate::hir::owned_ty(&sty, &self.h.structs, &self.h.enums);
                let scrut = self.new_slot(sty);
                self.emit_void(UOp::Store(scrut, st), span);
                let res = self.result_slot(&e.ty);
                let join = self.new_block();
                for arm in arms {
                    let next = self.new_block();
                    if owned_scrut {
                        // by-value match on an owning scrutinee: test first (no side effects), then move the bound
                        // payloads out and drop whatever the pattern did not bind
                        self.pat_test(&arm.pat, scrut, next);
                        self.pat_bind(&arm.pat, scrut);
                        self.emit_void(UOp::Drop(scrut, vec![]), span);
                    } else {
                        self.pat(&arm.pat, scrut, next);
                    }
                    let v = self.expr(&arm.body);
                    if let (Some(rs), false) = (res, self.dead) { self.emit_void(UOp::Store(rs, v), span); }
                    self.br(join);
                    self.switch(next);
                }
                self.term(UTerm::Trap("no `match` arm matched"));
                self.switch(join);
                self.join_value(res, &e.ty, span)
            }
        }
    }

    fn owned_t(&self, t: &Ty) -> bool { crate::hir::owned_ty(t, &self.h.structs, &self.h.enums) }

    /// Phase 1 of a by-value match on an owning scrutinee: only tests, never binds or moves.
    fn pat_test(&mut self, p: &HPat, src: Slot, fail: BlockId) {
        match p {
            HPat::Wild | HPat::Bind(_) => {}
            HPat::Lit(..) => self.pat(p, src, fail),
            HPat::Variant(vi, subs) => {
                let ty = self.slots[src].clone();
                let t = self.emit(UOp::Load(src), ty.clone(), Span::default());
                let b = self.emit(UOp::IsVariant(t, *vi), Ty::Bool, Span::default());
                let ok = self.new_block();
                self.term(UTerm::CondBr(b, ok, fail));
                self.switch(ok);
                let id = match ty { Ty::Enum(id) => id, _ => unreachable!("checked: variant pattern on enum") };
                for (j, sp) in subs.iter().enumerate() {
                    if matches!(sp, HPat::Wild | HPat::Bind(_)) { continue; }
                    let pty = self.h.enums[id].variants[*vi as usize].1[j].clone();
                    let t2 = self.emit(UOp::Load(src), ty.clone(), Span::default());
                    let pj = self.emit(UOp::Payload(t2, *vi, j), pty.clone(), Span::default());
                    let ns = self.new_slot(pty);
                    self.emit_void(UOp::Store(ns, pj), Span::default());
                    self.pat_test(sp, ns, fail);
                }
            }
        }
    }

    /// Phase 2: the pattern is known to match; move owned parts into the binding slots (copy the others).
    fn pat_bind(&mut self, p: &HPat, src: Slot) {
        match p {
            HPat::Wild | HPat::Lit(..) => {}
            HPat::Bind(hs) => {
                let ty = self.slots[src].clone();
                let t = if self.owned_t(&ty) { self.emit(UOp::Take(src), ty, Span::default()) } else { self.emit(UOp::Load(src), ty, Span::default()) };
                self.emit_void(UOp::Store(*hs, t), Span::default());
            }
            HPat::Variant(vi, subs) => {
                let ty = self.slots[src].clone();
                let id = match ty { Ty::Enum(id) => id, _ => unreachable!("checked: variant pattern on enum") };
                for (j, sp) in subs.iter().enumerate() {
                    if matches!(sp, HPat::Wild | HPat::Lit(..)) { continue; }
                    let pty = self.h.enums[id].variants[*vi as usize].1[j].clone();
                    let owned = self.owned_t(&pty);
                    let pj = if owned {
                        self.emit(UOp::TakePayload(src, *vi, j), pty.clone(), Span::default())
                    } else {
                        let t2 = self.emit(UOp::Load(src), ty.clone(), Span::default());
                        self.emit(UOp::Payload(t2, *vi, j), pty.clone(), Span::default())
                    };
                    if let HPat::Bind(hs) = sp {
                        self.emit_void(UOp::Store(*hs, pj), Span::default());
                    } else {
                        let ns = self.new_slot(pty);
                        self.emit_void(UOp::Store(ns, pj), Span::default());
                        self.pat_bind(sp, ns);
                        if owned { self.emit_void(UOp::Drop(ns, vec![]), Span::default()); }
                    }
                }
            }
        }
    }

    /// Test `p` against the value in slot `src`; on failure branch to `fail`; on success continue in a fresh block
    /// with the pattern's bindings stored in their slots.
    fn pat(&mut self, p: &HPat, src: Slot, fail: BlockId) {
        match p {
            HPat::Wild => {}
            HPat::Bind(hs) => {
                let ty = self.slots[src].clone();
                let t = self.emit(UOp::Load(src), ty, Span::default());
                self.emit_void(UOp::Store(*hs, t), Span::default());
            }
            HPat::Lit(v, ty, sp) => {
                let t = self.emit(UOp::Load(src), ty.clone(), *sp);
                let c = self.emit(UOp::Const(v.clone()), ty.clone(), *sp);
                let eq = self.emit(UOp::Binary(BinOp::Eq, t, c), Ty::Bool, *sp);
                let ok = self.new_block();
                self.term(UTerm::CondBr(eq, ok, fail));
                self.switch(ok);
            }
            HPat::Variant(vi, subs) => {
                let ty = self.slots[src].clone();
                let t = self.emit(UOp::Load(src), ty.clone(), Span::default());
                let b = self.emit(UOp::IsVariant(t, *vi), Ty::Bool, Span::default());
                let ok = self.new_block();
                self.term(UTerm::CondBr(b, ok, fail));
                self.switch(ok);
                let id = match ty { Ty::Enum(id) => id, _ => unreachable!("checked: variant pattern on enum") };
                for (j, sp) in subs.iter().enumerate() {
                    if matches!(sp, HPat::Wild) { continue; }
                    let pty = self.h.enums[id].variants[*vi as usize].1[j].clone();
                    let t2 = self.emit(UOp::Load(src), ty.clone(), Span::default());
                    let pj = self.emit(UOp::Payload(t2, *vi, j), pty.clone(), Span::default());
                    let ns = self.new_slot(pty);
                    self.emit_void(UOp::Store(ns, pj), Span::default());
                    self.pat(sp, ns, fail);
                }
            }
        }
    }
}
