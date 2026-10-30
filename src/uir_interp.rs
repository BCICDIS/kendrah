//! Reference interpreter for UIR. It must agree with the HIR interpreter on every program (output and runtime
//! errors, including spans); `lib::run_differential` and the test-suite enforce that. All value-level
//! semantics (arithmetic, casts, builtins) are *shared* with the HIR interpreter, not re-implemented.
//!
//! Frames live on one shared value stack (like the HIR interpreter) so a reference can designate a caller's slot.

use crate::diag::Span;
use crate::hir::Value;
use crate::interp::{as_bool, as_int, cast_value, deref_value, exec_builtin, rt, unary_value, Ctl, Heap, Interp, RuntimeError, FUEL_MSG, MAX_DEPTH, MEM_SIZE, P};
use crate::ty::Ty;
use crate::uir::*;
use std::io::Write;

type R<T> = Result<T, RuntimeError>;

fn un(c: Ctl) -> RuntimeError {
    match c { Ctl::Err(e) => e, _ => unreachable!("return/break/continue escaped") }
}

struct M<'a> {
    p: &'a UProgram,
    depth: usize,
    mem: [u8; MEM_SIZE],
    out: &'a mut dyn Write,
    fuel: Option<u64>,
    stack: Vec<Value>,
    bp: usize,
    heap: Heap,
}

pub fn run(p: &UProgram, out: &mut dyn Write, fuel: Option<u64>) -> Result<(), RuntimeError> {
    let main = p.main.ok_or(RuntimeError { span: Span::default(), message: "no `main` function defined".into() })?;
    let mut m = M { p, depth: 0, mem: [0; MEM_SIZE], out, fuel, stack: Vec::new(), bp: 0, heap: Heap::default() };
    m.call(main, vec![], Span::default())?;
    m.heap.check_leaks()
}

fn oob(sp: Span, i: i128, len: usize) -> RuntimeError { un(Interp::oob(sp, i, len)) }

fn walk<'v>(mut cur: &'v Value, path: &[P]) -> R<&'v Value> {
    for p in path {
        cur = match (p, cur) {
            (P::Field(i) | P::Raw(i), Value::Struct(f)) => &f[*i],
            (P::Raw(i), Value::Array(a)) => &a[*i],
            (P::Index(i, sp), Value::Array(a)) => {
                if *i < 0 || *i >= a.len() as i128 { return Err(oob(*sp, *i, a.len())); }
                &a[*i as usize]
            }
            _ => unreachable!("verified: bad projection"),
        };
    }
    Ok(cur)
}

fn walk_mut<'v>(mut cur: &'v mut Value, path: &[P]) -> R<&'v mut Value> {
    for p in path {
        cur = match (p, cur) {
            (P::Field(i) | P::Raw(i), Value::Struct(f)) => &mut f[*i],
            (P::Raw(i), Value::Array(a)) => &mut a[*i],
            (P::Index(i, sp), Value::Array(a)) => {
                if *i < 0 || *i >= a.len() as i128 { return Err(oob(*sp, *i, a.len())); }
                &mut a[*i as usize]
            }
            _ => unreachable!("verified: bad projection"),
        };
    }
    Ok(cur)
}

impl<'a> M<'a> {
    fn tick(&mut self, span: Span) -> R<()> {
        if let Some(f) = &mut self.fuel {
            if *f == 0 { return Err(un(rt(span, FUEL_MSG))); }
            *f -= 1;
        }
        Ok(())
    }

    /// Absolute stack index and projection path for `slot` + `ps`; a leading `Deref` follows the stored reference.
    fn target(&self, slot: usize, ps: &[UProj], temps: &[Value]) -> (usize, Vec<P>) {
        let mut abs = self.bp + slot;
        let mut path = Vec::with_capacity(ps.len());
        for p in ps {
            match p {
                UProj::Deref => match &self.stack[abs] {
                    Value::Ref(a, raw) => { path.extend(raw.iter().map(|x| P::Raw(*x))); abs = *a; }
                    _ => unreachable!("verified: deref of a non-reference"),
                },
                UProj::Field(i) => path.push(P::Field(*i)),
                UProj::Index(t, sp) => path.push(P::Index(as_int(&temps[*t]), *sp)),
            }
        }
        (abs, path)
    }

    fn call(&mut self, fid: usize, args: Vec<Value>, span: Span) -> R<Value> {
        self.tick(span)?;
        if self.depth >= MAX_DEPTH {
            return Err(un(rt(span, format!("stack overflow: call depth exceeded {}", MAX_DEPTH))));
        }
        let p = self.p;
        let f = &p.fns[fid];
        if f.ext == crate::ast::Ext::Import {
            return Err(un(rt(span, format!("cannot call the C function `{}` in the interpreter: build a native executable with `kendrah build` (see docs/INTEROP.md)", f.name))));
        }
        let new_bp = self.stack.len();
        self.stack.extend(args);
        self.stack.resize(new_bp + f.slots.len(), Value::Unit);
        let old_bp = std::mem::replace(&mut self.bp, new_bp);
        let mut temps = vec![Value::Unit; f.temps.len()];
        self.depth += 1;
        let mut b = 0usize;
        loop {
            self.tick(Span::default())?;
            let blk = &f.blocks[b];
            for ins in &blk.instrs {
                let v = self.exec(f, &temps, ins)?;
                if let Some(d) = ins.dest { temps[d] = v; }
            }
            match &blk.term {
                UTerm::Br(t) => b = *t,
                UTerm::CondBr(c, x, y) => b = if as_bool(&temps[*c]) { *x } else { *y },
                UTerm::Ret(t) => {
                    self.depth -= 1;
                    self.bp = old_bp;
                    self.stack.truncate(new_bp);
                    return Ok(std::mem::replace(&mut temps[*t], Value::Unit));
                }
                UTerm::Trap(m) => return Err(un(rt(Span::default(), format!("internal error: reached trap: {}", m)))),
            }
        }
    }

    /// Execute one instruction; returns the value for its destination (Unit for stores).
    fn exec(&mut self, f: &UFn, temps: &[Value], ins: &UInstr) -> R<Value> {
        let span = ins.span;
        let dty = |f: &UFn| -> Ty { f.temps[ins.dest.expect("verified: dest")].clone() };
        Ok(match &ins.op {
            UOp::Const(v) => v.clone(),
            UOp::Load(s) => self.stack[self.bp + *s].clone(),
            UOp::Store(s, t) => { let i = self.bp + *s; self.stack[i] = temps[*t].clone(); Value::Unit }
            UOp::LoadProj(s, ps) => { let (abs, path) = self.target(*s, ps, temps); walk(&self.stack[abs], &path)?.clone() }
            UOp::StoreProj(s, ps, t) => {
                let (abs, path) = self.target(*s, ps, temps);
                *walk_mut(&mut self.stack[abs], &path)? = temps[*t].clone();
                Value::Unit
            }
            UOp::Take(s) => std::mem::replace(&mut self.stack[self.bp + *s], Value::Unit),
            UOp::Drop(s, ps) => {
                let (abs, path) = self.target(*s, ps, temps);
                let slot = walk_mut(&mut self.stack[abs], &path)?;
                let old = std::mem::replace(slot, Value::Unit);
                crate::interp::free_value(&mut self.heap, old, Span::default()).map_err(un)?;
                Value::Unit
            }
            UOp::AddrOf(s, ps) => {
                let (abs, path) = self.target(*s, ps, temps);
                // Bounds-check now and resolve to child indices.
                let mut cur = &self.stack[abs];
                let mut raw = Vec::with_capacity(path.len());
                for p in &path {
                    let (i, next) = match (p, cur) {
                        (P::Field(i) | P::Raw(i), Value::Struct(f)) => (*i, &f[*i]),
                        (P::Raw(i), Value::Array(a)) => (*i, &a[*i]),
                        (P::Index(i, sp), Value::Array(a)) => {
                            if *i < 0 || *i >= a.len() as i128 { return Err(oob(*sp, *i, a.len())); }
                            (*i as usize, &a[*i as usize])
                        }
                        _ => unreachable!("verified: bad projection"),
                    };
                    raw.push(i);
                    cur = next;
                }
                Value::Ref(abs, raw)
            }
            UOp::Unary(op, t) => unary_value(*op, temps[*t].clone(), &dty(f), span).map_err(un)?,
            UOp::Binary(op, a, b) => {
                let aty = &f.temps[*a];
                match (&temps[*a], &temps[*b], aty) {
                    (Value::Int(x), Value::Int(y), Ty::Int(k)) => Interp::int_op(*op, *k, *x, *y, span).map_err(un)?,
                    (l, r, _) => Interp::binary(*op, aty, l.clone(), r.clone(), span).map_err(un)?,
                }
            }
            UOp::Cast(t) => cast_value(temps[*t].clone(), &dty(f)),
            UOp::Call(id, args) => {
                let vs: Vec<Value> = args.iter().map(|a| temps[*a].clone()).collect();
                self.call(*id, vs, span)?
            }
            UOp::Builtin(b, args) => {
                let vs: Vec<Value> = args.iter().map(|a| deref_value(&self.stack, temps[*a].clone())).collect();
                exec_builtin(*b, vs, &mut self.mem, &mut self.heap, self.out, span).map_err(un)?
            }
            UOp::MakeStruct(id, fs) => {
                let mut vals = vec![Value::Unit; self.p.structs[*id].fields.len()];
                for (i, t) in fs { vals[*i] = temps[*t].clone(); }
                Value::Struct(vals)
            }
            UOp::Field(t, i) => match &temps[*t] { Value::Struct(fs) => fs[*i].clone(), _ => unreachable!("verified") },
            UOp::Index(a, i, sp) => {
                let idx = as_int(&temps[*i]);
                match &temps[*a] {
                    Value::Array(v) => {
                        if idx < 0 || idx >= v.len() as i128 { return Err(oob(*sp, idx, v.len())); }
                        v[idx as usize].clone()
                    }
                    _ => unreachable!("verified"),
                }
            }
            UOp::MakeArray(ts) => Value::Array(ts.iter().map(|t| temps[*t].clone()).collect()),
            UOp::Repeat(t, n) => Value::Array(vec![temps[*t].clone(); *n]),
            UOp::MakeVariant(v, ts) => Value::Enum(*v, ts.iter().map(|t| temps[*t].clone()).collect()),
            UOp::IsVariant(t, v) => match &temps[*t] { Value::Enum(j, _) => Value::Bool(j == v), _ => unreachable!("verified") },
            UOp::TakePayload(s, _, j) => match &mut self.stack[self.bp + *s] {
                Value::Enum(_, args) => std::mem::replace(&mut args[*j], Value::Unit),
                _ => unreachable!("verified"),
            },
            UOp::Payload(t, _, j) => match &temps[*t] { Value::Enum(_, args) => args[*j].clone(), _ => unreachable!("verified") },
        })
    }
}
