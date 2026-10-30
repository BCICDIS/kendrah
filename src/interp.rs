//! Tree-walking interpreter over the typed HIR. Runs only programs that passed `check`.
//!
//! Runtime semantics (see docs/SPEC.md): integer arithmetic is checked against the static integer type
//! (overflow, division by zero, bad shift amounts, out-of-range memory/array access are runtime errors,
//! never undefined behavior); `f64` follows IEEE-754. Aggregates (structs, enums, arrays) have value
//! semantics: reading a variable copies it. `peek`/`poke` operate on a 256-byte simulated memory.

use crate::ast::{BinOp, UnOp};
use crate::diag::Span;
use crate::hir::*;
use crate::ty::{IntTy, Ty};
use std::io::Write;

#[derive(Debug, Clone, PartialEq)]
pub struct RuntimeError { pub span: Span, pub message: String }

pub(crate) enum Ctl { Return(Value), Break, Continue, Err(RuntimeError) }
pub(crate) type R<T> = Result<T, Ctl>;

pub const MEM_SIZE: usize = 256;

/// Interpreter heap for owned `String`s. A handle that is freed twice, or still live when the program ends normally,
/// is a *compiler* bug (drop elaboration is wrong) and is reported as an internal error.
pub enum Obj { S(String), V(Vec<Value>), B(Value) }
#[derive(Default)]
pub struct Heap { items: Vec<Option<Obj>>, live: usize }

impl Heap {
    pub(crate) fn alloc(&mut self, s: String) -> usize { self.items.push(Some(Obj::S(s))); self.live += 1; self.items.len() - 1 }
    pub(crate) fn alloc_vec(&mut self, v: Vec<Value>) -> usize { self.items.push(Some(Obj::V(v))); self.live += 1; self.items.len() - 1 }
    pub(crate) fn alloc_box(&mut self, v: Value) -> usize { self.items.push(Some(Obj::B(v))); self.live += 1; self.items.len() - 1 }
    /// The value inside a box cell, if `h` is one (used by `free_value` to free the contents first).
    pub(crate) fn take_box(&mut self, h: usize) -> Option<Value> {
        match self.items.get_mut(h) { Some(Some(Obj::B(v))) => Some(std::mem::replace(v, Value::Unit)), _ => None }
    }
    pub(crate) fn boxed(&self, h: usize) -> &Value { match self.items[h].as_ref() { Some(Obj::B(v)) => v, _ => panic!("use of freed Box (compiler bug)") } }
    pub(crate) fn boxed_mut(&mut self, h: usize) -> &mut Value { match self.items[h].as_mut() { Some(Obj::B(v)) => v, _ => panic!("use of freed Box (compiler bug)") } }
    pub(crate) fn vec(&self, h: usize) -> &Vec<Value> { match self.items[h].as_ref() { Some(Obj::V(v)) => v, _ => panic!("use of freed Vec (compiler bug)") } }
    pub(crate) fn vec_mut(&mut self, h: usize) -> &mut Vec<Value> { match self.items[h].as_mut() { Some(Obj::V(v)) => v, _ => panic!("use of freed Vec (compiler bug)") } }
    pub(crate) fn free(&mut self, h: usize, span: Span) -> R<()> {
        match self.items.get_mut(h) {
            Some(slot @ Some(_)) => { *slot = None; self.live -= 1; Ok(()) }
            _ => Err(rt(span, format!("internal error: double free of String #{}", h))),
        }
    }
    pub(crate) fn get(&self, h: usize) -> &String { match self.items[h].as_ref() { Some(Obj::S(s)) => s, _ => panic!("use of freed String (compiler bug)") } }
    pub(crate) fn get_mut(&mut self, h: usize) -> &mut String { match self.items[h].as_mut() { Some(Obj::S(s)) => s, _ => panic!("use of freed String (compiler bug)") } }
    pub(crate) fn check_leaks(&self) -> Result<(), RuntimeError> {
        if self.live == 0 { Ok(()) } else {
            Err(RuntimeError { span: Span::default(), message: format!("internal error: memory leak: {} owned allocation(s) were not freed", self.live) })
        }
    }
}

/// Free every heap object reachable by value from `v` (drop glue for owned aggregates).
pub(crate) fn free_value(heap: &mut Heap, v: Value, span: Span) -> R<()> {
    // iterative: a long `Box` chain (a linked list) must not recurse once per node
    let mut work = vec![v];
    while let Some(v) = work.pop() {
        match v {
            Value::Heap(h) => {
                let inner = heap.take_box(h);
                heap.free(h, span)?;
                if let Some(i) = inner { work.push(i); }
            }
            Value::Struct(fs) | Value::Enum(_, fs) | Value::Array(fs) => work.extend(fs),
            _ => {}
        }
    }
    Ok(())
}

/// Follow a `Value::Ref` to the value it designates (used to pass `&String` arguments to builtins).
pub(crate) fn deref_value(stack: &[Value], v: Value) -> Value {
    match v {
        Value::Ref(abs, path) => {
            let mut cur = &stack[abs];
            for i in path {
                cur = match cur { Value::Struct(f) => &f[i], Value::Array(a) => &a[i], _ => unreachable!("bad reference path") };
            }
            cur.clone()
        }
        o => o,
    }
}
pub const MAX_DEPTH: usize = 2000;

/// A projection step; `Raw` is an already-resolved child index (from a reference).
pub(crate) enum P { Field(usize), Index(i128, Span), Raw(usize) }

pub struct Interp<'a> {
    p: &'a HProgram,
    depth: usize,
    mem: [u8; MEM_SIZE],
    out: &'a mut dyn Write,
    fuel: Option<u64>,
    /// All frames live on one stack so references can designate a caller's locals; `bp` is the current frame base.
    stack: Vec<Value>,
    bp: usize,
    heap: Heap,
}

pub(crate) fn rt(span: Span, m: impl Into<String>) -> Ctl { Ctl::Err(RuntimeError { span, message: m.into() }) }

pub const FUEL_MSG: &str = "execution step limit exceeded";

pub fn run(p: &HProgram, out: &mut dyn Write) -> Result<(), RuntimeError> { run_with_fuel(p, out, None) }

/// Like `run`, but aborts with a runtime error after about `fuel` steps (statements, calls, loop iterations).
pub fn run_with_fuel(p: &HProgram, out: &mut dyn Write, fuel: Option<u64>) -> Result<(), RuntimeError> {
    let main = p.main.ok_or(RuntimeError { span: Span::default(), message: "no `main` function defined".into() })?;
    let mut it = Interp { p, depth: 0, mem: [0; MEM_SIZE], out, fuel, stack: Vec::new(), bp: 0, heap: Heap::default() };
    match it.call_fn(main, vec![], Span::default()) {
        Ok(_) => it.heap.check_leaks(),
        Err(Ctl::Err(e)) => Err(e),
        Err(_) => unreachable!("return/break/continue escaped call_fn"),
    }
}

fn display(v: &Value) -> String {
    match v {
        Value::Int(i) => i.to_string(),
        Value::Float(f) => format!("{:?}", f),
        Value::Bool(b) => b.to_string(),
        Value::Str(s) => s.clone(),
        _ => "<aggregate>".into(),
    }
}

pub(crate) fn as_int(v: &Value) -> i128 { match v { Value::Int(i) => *i, _ => unreachable!("checked program: integer expected") } }
pub(crate) fn as_bool(v: &Value) -> bool { match v { Value::Bool(b) => *b, _ => unreachable!("checked program: bool expected") } }

pub(crate) fn unary_value(op: UnOp, v: Value, ty: &Ty, span: Span) -> R<Value> {
    Ok(match (op, v) {
        (UnOp::Neg, Value::Int(i)) => {
            let k = match ty { Ty::Int(k) => *k, _ => unreachable!() };
            fit(k, i.checked_neg(), "negation", span)?
        }
        (UnOp::Neg, Value::Float(f)) => Value::Float(-f),
        (UnOp::Not, Value::Bool(b)) => Value::Bool(!b),
        _ => unreachable!("checked program"),
    })
}

/// Numeric/bool conversion to `to` (see SPEC section 3: integer casts wrap, float->int saturates).
pub(crate) fn cast_value(v: Value, to: &Ty) -> Value {
    match (v, to) {
        (Value::Int(i), Ty::Int(k)) => Value::Int(k.wrap(i)),
        (Value::Int(i), Ty::Float) => Value::Float(i as f64),
        (Value::Float(f), Ty::Int(k)) => Value::Int(if f.is_nan() { 0 } else { (f as i128).clamp(k.min(), k.max()) }),
        (Value::Bool(b), Ty::Int(_)) => Value::Int(b as i128),
        (v, _) => v,
    }
}


pub(crate) fn fit(k: IntTy, v: Option<i128>, what: &str, span: Span) -> R<Value> {
    match v {
        Some(x) if k.contains(x) => Ok(Value::Int(x)),
        _ => Err(rt(span, format!("integer overflow in {} ({})", what, k.name()))),
    }
}

/// Builtin semantics shared by every execution engine.
pub(crate) fn exec_builtin(b: Builtin, mut args: Vec<Value>, mem: &mut [u8; MEM_SIZE], heap: &mut Heap, out: &mut dyn Write, span: Span) -> R<Value> {
    fn addr(i: i128, span: Span) -> R<usize> {
        if i >= 0 && (i as usize) < MEM_SIZE { Ok(i as usize) }
        else { Err(rt(span, format!("memory access out of bounds: address {} (valid: 0..{})", i, MEM_SIZE))) }
    }
    match b {
        Builtin::Print => {
            let text = match &args[0] { Value::Heap(h) => heap.get(*h).clone(), v => display(v) };
            writeln!(out, "{}", text).map_err(|e| rt(span, format!("output error: {}", e)))?;
            Ok(Value::Unit)
        }
        Builtin::StringFrom => match &args[0] { Value::Str(s) => Ok(Value::Heap(heap.alloc(s.clone()))), _ => unreachable!() },
        Builtin::StringConcat => match (&args[0], &args[1]) {
            (Value::Heap(a), Value::Heap(b)) => { let s = format!("{}{}", heap.get(*a), heap.get(*b)); Ok(Value::Heap(heap.alloc(s))) }
            _ => unreachable!(),
        },
        Builtin::StringPush => match (&args[0], &args[1]) {
            (Value::Heap(a), Value::Str(t)) => { let t = t.clone(); heap.get_mut(*a).push_str(&t); Ok(Value::Unit) }
            _ => unreachable!(),
        },
        Builtin::StringLen => match &args[0] { Value::Heap(a) => Ok(Value::Int(heap.get(*a).len() as i128)), _ => unreachable!() },
        Builtin::StringClone => match &args[0] { Value::Heap(a) => { let s = heap.get(*a).clone(); Ok(Value::Heap(heap.alloc(s))) } _ => unreachable!() },
        Builtin::StringEq => match (&args[0], &args[1]) { (Value::Heap(a), Value::Heap(b)) => Ok(Value::Bool(heap.get(*a) == heap.get(*b))), _ => unreachable!() },
        Builtin::VecNew => Ok(Value::Heap(heap.alloc_vec(vec![]))),
        Builtin::VecPush => match &args[0] { Value::Heap(h) => { let h = *h; let v = args.remove(1); heap.vec_mut(h).push(v); Ok(Value::Unit) } _ => unreachable!() },
        Builtin::VecLen => match &args[0] { Value::Heap(h) => Ok(Value::Int(heap.vec(*h).len() as i128)), _ => unreachable!() },
        Builtin::VecGet | Builtin::VecSet => {
            let h = match &args[0] { Value::Heap(h) => *h, _ => unreachable!() };
            let i = as_int(&args[1]);
            let n = heap.vec(h).len();
            if i < 0 || i as usize >= n { return Err(rt(span, format!("vector index out of bounds: the index is {} but the length is {}", i, n))); }
            if b == Builtin::VecGet { Ok(heap.vec(h)[i as usize].clone()) } else { let v = args.remove(2); heap.vec_mut(h)[i as usize] = v; Ok(Value::Unit) }
        }
        Builtin::VecPop => match &args[0] {
            Value::Heap(h) => heap.vec_mut(*h).pop().ok_or_else(|| rt(span, "pop from an empty Vec".to_string())),
            _ => unreachable!(),
        },
        Builtin::VecClone => match &args[0] { Value::Heap(h) => { let v = heap.vec(*h).clone(); Ok(Value::Heap(heap.alloc_vec(v))) } _ => unreachable!() },
        Builtin::BoxNew => { let v = args.remove(0); Ok(Value::Heap(heap.alloc_box(v))) }
        Builtin::BoxInto => match &args[0] {
            Value::Heap(h) => {
                let h = *h;
                let v = heap.take_box(h).expect("box_into of a Box (compiler bug)");
                heap.free(h, span)?;
                Ok(v)
            }
            _ => unreachable!(),
        },
        Builtin::BoxGet => match &args[0] { Value::Heap(h) => Ok(heap.boxed(*h).clone()), _ => unreachable!() },
        Builtin::BoxSet => match &args[0] { Value::Heap(h) => { let h = *h; let v = args.remove(1); *heap.boxed_mut(h) = v; Ok(Value::Unit) } _ => unreachable!() },
        Builtin::Peek => { let a = addr(as_int(&args[0]), span)?; Ok(Value::Int(mem[a] as i128)) }
        Builtin::Poke => {
            let a = addr(as_int(&args[0]), span)?;
            let v = as_int(&args.remove(1));
            if !(0..=255).contains(&v) { return Err(rt(span, format!("poke value {} does not fit in a byte", v))); }
            mem[a] = v as u8;
            Ok(Value::Unit)
        }
        Builtin::Len => match &args[0] { Value::Array(a) => Ok(Value::Int(a.len() as i128)), _ => unreachable!() },
    }
}

impl<'a> Interp<'a> {
    #[inline]
    fn tick(&mut self, span: Span) -> R<()> {
        if let Some(f) = &mut self.fuel {
            if *f == 0 { return Err(rt(span, FUEL_MSG)); }
            *f -= 1;
        }
        Ok(())
    }

    fn call_fn(&mut self, id: usize, args: Vec<Value>, span: Span) -> R<Value> {
        self.tick(span)?;
        if self.depth >= MAX_DEPTH {
            return Err(rt(span, format!("stack overflow: call depth exceeded {}", MAX_DEPTH)));
        }
        let f = &self.p.fns[id];
        if f.ext == crate::ast::Ext::Import {
            return Err(rt(span, format!("cannot call the C function `{}` in the interpreter: build a native executable with `kendrah build` (see docs/INTEROP.md)", f.name)));
        }
        let new_bp = self.stack.len();
        self.stack.extend(args);
        self.stack.resize(new_bp + f.nslots.max(f.nparams), Value::Unit);
        let old_bp = std::mem::replace(&mut self.bp, new_bp);
        self.depth += 1;
        let r = self.block(&f.body);
        self.depth -= 1;
        self.bp = old_bp;
        self.stack.truncate(new_bp);
        match r {
            Ok(v) => Ok(v),
            Err(Ctl::Return(v)) => Ok(v),
            Err(e) => Err(e),
        }
    }

    fn block(&mut self, b: &HBlock) -> R<Value> {
        for s in &b.stmts {
            self.tick(Span::default())?;
            match s {
                HStmt::Let(slot, e) => { let v = self.expr(e)?; let i = self.bp + *slot; self.stack[i] = v; }
                HStmt::Assign(place, e) => {
                    // Rust-like order: the right-hand side is evaluated before the place's index expressions.
                    let v = self.expr(e)?;
                    let (abs, path) = self.place_target(place)?;
                    let slot = Self::walk_mut(&mut self.stack[abs], &path)?;
                    *slot = v;
                }
                HStmt::Expr(e) => { self.expr(e)?; }
                HStmt::Drop(place) => {
                    let (abs, path) = self.place_target(place)?;
                    let slot = Self::walk_mut(&mut self.stack[abs], &path)?;
                    let old = std::mem::replace(slot, Value::Unit);
                    free_value(&mut self.heap, old, Span::default())?;
                }
                HStmt::While(c, body) => {
                    while as_bool(&self.expr(c)?) {
                        self.tick(c.span)?;
                        match self.block(body) {
                            Ok(_) | Err(Ctl::Continue) => {}
                            Err(Ctl::Break) => break,
                            Err(e) => return Err(e),
                        }
                    }
                }
                HStmt::Break => return Err(Ctl::Break),
                HStmt::Continue => return Err(Ctl::Continue),
                HStmt::Return(e) => {
                    let v = match e { Some(e) => self.expr(e)?, None => Value::Unit };
                    return Err(Ctl::Return(v));
                }
            }
        }
        match &b.tail { Some(e) => self.expr(e), None => Ok(Value::Unit) }
    }

    /// Absolute stack index and projection path designated by a place; a leading `Deref` follows the reference.
    fn place_target(&mut self, pl: &HPlace) -> R<(usize, Vec<P>)> {
        let mut abs = self.bp + pl.root;
        let mut path = Vec::with_capacity(pl.proj.len());
        for pr in &pl.proj {
            match pr {
                Proj::Deref => match &self.stack[abs] {
                    Value::Ref(a, p) => { path.extend(p.iter().map(|x| P::Raw(*x))); abs = *a; }
                    _ => unreachable!("checked program: deref of a non-reference"),
                },
                Proj::Field(i) => path.push(P::Field(*i)),
                Proj::Index(ie) => { let v = as_int(&self.expr(ie)?); path.push(P::Index(v, ie.span)); }
            }
        }
        Ok((abs, path))
    }

    /// Bounds-check `path` against the value at `abs` and convert it to child indices.
    fn to_raw(&self, abs: usize, path: &[P]) -> R<Vec<usize>> {
        let mut cur = &self.stack[abs];
        let mut out = Vec::with_capacity(path.len());
        for p in path {
            let (i, next) = match (p, cur) {
                (P::Field(i), Value::Struct(f)) => (*i, &f[*i]),
                (P::Raw(i), Value::Struct(f)) => (*i, &f[*i]),
                (P::Raw(i), Value::Array(a)) => (*i, &a[*i]),
                (P::Index(i, sp), Value::Array(a)) => {
                    if *i < 0 || *i >= a.len() as i128 { return Err(Self::oob(*sp, *i, a.len())); }
                    (*i as usize, &a[*i as usize])
                }
                _ => unreachable!("checked program: bad projection"),
            };
            out.push(i);
            cur = next;
        }
        Ok(out)
    }

    pub(crate) fn oob(span: Span, i: i128, len: usize) -> Ctl {
        rt(span, format!("array index out of bounds: the index is {} but the length is {}", i, len))
    }

    fn walk_mut<'v>(mut cur: &'v mut Value, path: &[P]) -> R<&'v mut Value> {
        for p in path {
            cur = match (p, cur) {
                (P::Field(i) | P::Raw(i), Value::Struct(f)) => &mut f[*i],
                (P::Raw(i), Value::Array(a)) => &mut a[*i],
                (P::Index(i, sp), Value::Array(a)) => {
                    if *i < 0 || *i >= a.len() as i128 { return Err(Self::oob(*sp, *i, a.len())); }
                    &mut a[*i as usize]
                }
                _ => unreachable!("checked program: bad place projection"),
            };
        }
        Ok(cur)
    }

    fn walk<'v>(mut cur: &'v Value, path: &[P]) -> R<&'v Value> {
        for p in path {
            cur = match (p, cur) {
                (P::Field(i) | P::Raw(i), Value::Struct(f)) => &f[*i],
                (P::Raw(i), Value::Array(a)) => &a[*i],
                (P::Index(i, sp), Value::Array(a)) => {
                    if *i < 0 || *i >= a.len() as i128 { return Err(Self::oob(*sp, *i, a.len())); }
                    &a[*i as usize]
                }
                _ => unreachable!("checked program: bad projection"),
            };
        }
        Ok(cur)
    }

    /// If `e` is a chain of field/index/deref projections rooted at a local, collect it without copying the
    /// aggregate. Returns the absolute stack index of the root value.
    fn chain(&mut self, e: &HExpr, path: &mut Vec<P>) -> R<Option<usize>> {
        match &e.kind {
            HKind::Local(s) => Ok(Some(self.bp + *s)),
            HKind::Deref(b) => {
                let r = self.chain(b, path)?;
                match r {
                    Some(abs) => match &self.stack[abs] {
                        Value::Ref(a, p) if path.is_empty() => { let a = *a; path.extend(p.iter().map(|x| P::Raw(*x))); Ok(Some(a)) }
                        _ => unreachable!("checked program: deref of a non-reference"),
                    },
                    None => Ok(None),
                }
            }
            HKind::Field(b, i) => {
                let r = self.chain(b, path)?;
                if r.is_some() { path.push(P::Field(*i)); }
                Ok(r)
            }
            HKind::Index(b, ie) => {
                let r = self.chain(b, path)?;
                if r.is_some() {
                    let i = as_int(&self.expr(ie)?);
                    path.push(P::Index(i, ie.span));
                }
                Ok(r)
            }
            _ => Ok(None),
        }
    }

    /// Integer value of a literal or local, read without cloning (fast path for the hottest operands).
    #[inline]
    fn leaf_int(e: &HExpr, stack: &[Value], bp: usize) -> Option<i128> {
        match &e.kind {
            HKind::Lit(Value::Int(v)) => Some(*v),
            HKind::Local(s) => match &stack[bp + *s] { Value::Int(v) => Some(*v), _ => None },
            _ => None,
        }
    }

    fn is_chain(e: &HExpr) -> bool {
        match &e.kind {
            HKind::Local(_) => true,
            HKind::Field(b, _) | HKind::Index(b, _) | HKind::Deref(b) => Self::is_chain(b),
            _ => false,
        }
    }

    fn expr(&mut self, e: &HExpr) -> R<Value> {
        Ok(match &e.kind {
            HKind::Lit(v) => v.clone(),
            HKind::Local(s) => self.stack[self.bp + *s].clone(),
            HKind::Move(s) => std::mem::replace(&mut self.stack[self.bp + *s], Value::Unit),
            HKind::Unary(op, x) => {
                let v = self.expr(x)?;
                unary_value(*op, v, &e.ty, e.span)?
            }
            HKind::Binary(op, l, r) => {
                if matches!(op, BinOp::And | BinOp::Or) {
                    let lv = as_bool(&self.expr(l)?);
                    return Ok(Value::Bool(match op {
                        BinOp::And => lv && as_bool(&self.expr(r)?),
                        _ => lv || as_bool(&self.expr(r)?),
                    }));
                }
                if let (Some(a), Some(b), Ty::Int(k)) = (Self::leaf_int(l, &self.stack, self.bp), Self::leaf_int(r, &self.stack, self.bp), &l.ty) {
                    return Self::int_op(*op, *k, a, b, e.span);
                }
                let lv = self.expr(l)?;
                let rv = self.expr(r)?;
                Self::binary(*op, &l.ty, lv, rv, e.span)?
            }
            HKind::Call(id, args) => {
                let mut vs = Vec::with_capacity(args.len());
                for a in args { vs.push(self.expr(a)?); }
                self.call_fn(*id, vs, e.span)?
            }
            HKind::Builtin(b, args) => {
                let mut vs = Vec::with_capacity(args.len());
                for a in args { vs.push(self.expr(a)?); }
                self.builtin(*b, vs, e.span)?
            }
            HKind::If(c, t, els) => {
                if as_bool(&self.expr(c)?) { self.block(t)? }
                else if let Some(b) = els { self.block(b)? } else { Value::Unit }
            }
            HKind::Block(b) => self.block(b)?,
            HKind::Cast(x) => {
                let v = self.expr(x)?;
                cast_value(v, &e.ty)
            }
            HKind::Struct(id, fields) => {
                let mut vals = vec![Value::Unit; self.p.structs[*id].fields.len()];
                for (i, fe) in fields { vals[*i] = self.expr(fe)?; }
                Value::Struct(vals)
            }
            HKind::AddrOf(pl, _) => {
                let (abs, path) = self.place_target(pl)?;
                let raw = self.to_raw(abs, &path)?;
                Value::Ref(abs, raw)
            }
            HKind::Field(..) | HKind::Index(..) | HKind::Deref(_) => {
                if Self::is_chain(e) {
                    let mut path = Vec::new();
                    let root = self.chain(e, &mut path)?.expect("chain");
                    Self::walk(&self.stack[root], &path)?.clone()
                } else {
                    // Projection of a temporary (e.g. a call result).
                    match &e.kind {
                        HKind::Field(b, i) => match self.expr(b)? { Value::Struct(mut f) => f.swap_remove(*i), _ => unreachable!() },
                        HKind::Index(b, ie) => {
                            let a = self.expr(b)?;
                            let i = as_int(&self.expr(ie)?);
                            match a {
                                Value::Array(mut v) => {
                                    if i < 0 || i >= v.len() as i128 { return Err(Self::oob(ie.span, i, v.len())); }
                                    v.swap_remove(i as usize)
                                }
                                _ => unreachable!(),
                            }
                        }
                        _ => unreachable!(),
                    }
                }
            }
            HKind::Array(xs) => {
                let mut vs = Vec::with_capacity(xs.len());
                for x in xs { vs.push(self.expr(x)?); }
                Value::Array(vs)
            }
            HKind::Repeat(x, n) => { let v = self.expr(x)?; Value::Array(vec![v; *n]) }
            HKind::Variant(vi, args) => {
                let mut vs = Vec::with_capacity(args.len());
                for a in args { vs.push(self.expr(a)?); }
                Value::Enum(*vi, vs)
            }
            HKind::Match(s, arms) => {
                let mut v = self.expr(s)?;
                let owned = owned_ty(&s.ty, &self.p.structs, &self.p.enums);
                for a in arms {
                    if owned {
                        if self.pat_test(&a.pat, &v) {
                            // by-value match: move bound parts out of the scrutinee, free the rest
                            self.pat_take(&a.pat, &mut v);
                            free_value(&mut self.heap, std::mem::replace(&mut v, Value::Unit), e.span)?;
                            return self.expr(&a.body);
                        }
                    } else if self.pat(&a.pat, &v) { return self.expr(&a.body); }
                }
                return Err(rt(e.span, "no `match` arm matched (checker invariant violated)"));
            }
        })
    }

    /// Pure test (no bindings), used for by-value matches on owning scrutinees.
    fn pat_test(&self, p: &HPat, v: &Value) -> bool {
        match p {
            HPat::Wild | HPat::Bind(_) => true,
            HPat::Lit(l, _, _) => l == v,
            HPat::Variant(i, subs) => match v {
                Value::Enum(j, args) if j == i => subs.iter().zip(args).all(|(s, a)| self.pat_test(s, a)),
                _ => false,
            },
        }
    }

    /// Bind by moving: the bound part is replaced by `Unit` in the scrutinee so freeing the remainder skips it.
    fn pat_take(&mut self, p: &HPat, v: &mut Value) {
        match p {
            HPat::Wild | HPat::Lit(..) => {}
            HPat::Bind(s) => { let i = self.bp + *s; self.stack[i] = std::mem::replace(v, Value::Unit); }
            HPat::Variant(_, subs) => {
                if let Value::Enum(_, args) = v { for (s, a) in subs.iter().zip(args.iter_mut()) { self.pat_take(s, a); } }
            }
        }
    }

    fn pat(&mut self, p: &HPat, v: &Value) -> bool {
        match p {
            HPat::Wild => true,
            HPat::Bind(s) => { let i = self.bp + *s; self.stack[i] = v.clone(); true }
            HPat::Lit(l, _, _) => l == v,
            HPat::Variant(i, subs) => match v {
                Value::Enum(j, args) if j == i => subs.iter().zip(args).all(|(s, a)| self.pat(s, a)),
                _ => false,
            },
        }
    }

    fn builtin(&mut self, b: Builtin, args: Vec<Value>, span: Span) -> R<Value> {
        let args: Vec<Value> = args.into_iter().map(|a| deref_value(&self.stack, a)).collect();
        exec_builtin(b, args, &mut self.mem, &mut self.heap, self.out, span)
    }

    #[inline]
    pub(crate) fn int_op(op: BinOp, k: IntTy, a: i128, b: i128, span: Span) -> R<Value> {
        use BinOp::*;
        use Value::*;
        Ok(match op {
                    Add => fit(k, a.checked_add(b), "addition", span)?,
                    Sub => fit(k, a.checked_sub(b), "subtraction", span)?,
                    Mul => fit(k, a.checked_mul(b), "multiplication", span)?,
                    Div => { if b == 0 { return Err(rt(span, "division by zero")); } fit(k, a.checked_div(b), "division", span)? }
                    Rem => {
                        if b == 0 { return Err(rt(span, "remainder by zero")); }
                        // MIN % -1 is an overflow error, consistent with MIN / -1 (and with what native targets trap/UB on).
                        if k.signed() && a == k.min() && b == -1 { return Err(rt(span, format!("integer overflow in remainder ({})", k.name()))); }
                        fit(k, a.checked_rem(b), "remainder", span)?
                    }
                    BitAnd => Int(a & b), BitOr => Int(a | b), BitXor => Int(a ^ b),
                    Shl | Shr => {
                        if b < 0 || b >= k.bits() as i128 {
                            return Err(rt(span, format!("shift amount {} out of range for {} (valid: 0..{})", b, k.name(), k.bits())));
                        }
                        if op == Shl { Int(k.wrap(a << b)) } else { Int(a >> b) }
                    }
                    Eq => Bool(a == b), Ne => Bool(a != b),
                    Lt => Bool(a < b), Le => Bool(a <= b), Gt => Bool(a > b), Ge => Bool(a >= b),
                    And | Or => unreachable!(),
                })
    }

    pub(crate) fn binary(op: BinOp, lty: &Ty, l: Value, r: Value, span: Span) -> R<Value> {
        use BinOp::*;
        use Value::*;
        Ok(match (l, r) {
            (Int(a), Int(b)) => {
                let k = match lty { Ty::Int(k) => *k, _ => unreachable!("checked program: integer operands") };
                Self::int_op(op, k, a, b, span)?
            }
            (Float(a), Float(b)) => match op {
                Add => Float(a + b), Sub => Float(a - b), Mul => Float(a * b), Div => Float(a / b), Rem => Float(a % b),
                Eq => Bool(a == b), Ne => Bool(a != b),
                Lt => Bool(a < b), Le => Bool(a <= b), Gt => Bool(a > b), Ge => Bool(a >= b),
                _ => unreachable!("checked program"),
            },
            (Str(a), Str(b)) => match op {
                Add => Str(a + &b), Eq => Bool(a == b), Ne => Bool(a != b),
                _ => unreachable!("checked program"),
            },
            (Bool(a), Bool(b)) => match op { Eq => Bool(a == b), Ne => Bool(a != b), _ => unreachable!("checked program") },
            _ => unreachable!("checked program"),
        })
    }
}
