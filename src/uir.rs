//! UIR v0: the Universal Intermediate Representation (see docs/UIR.md for the full specification).
//!
//! A function is a CFG of basic blocks over *typed* values:
//! * **slots** are mutable, function-local storage cells (the first `nparams` hold the arguments), accessed
//!   only by `Load`/`Store`/`LoadProj`/`StoreProj` (an "alloca" model, like unoptimised LLVM IR);
//! * **temps** are single-assignment values that live **inside one basic block** (they never cross blocks;
//!   anything that must survive a branch goes through a slot). This makes the dataflow trivially checkable
//!   and leaves SSA construction (slot promotion to block parameters) to a later optimisation pass.
//! Every instruction carries the source span that runtime errors are reported at.

use crate::ast::{BinOp, Layer, UnOp};
use crate::diag::Span;
use crate::hir::{Builtin, EnumDef, StructDef, Value};
use crate::ty::{IntTy, Ty};
use std::collections::HashSet;
use std::fmt::Write as _;

pub type Temp = usize;
pub type Slot = usize;
pub type BlockId = usize;

#[derive(Debug, Clone, PartialEq)]
pub enum UProj {
    /// Follow a reference (only valid as the first projection of a slot of reference type).
    Deref,
    Field(usize),
    Index(Temp, Span),
}

#[derive(Debug, Clone, PartialEq)]
pub enum UOp {
    Const(Value),
    Load(Slot),
    Store(Slot, Temp),
    /// Read through a projection path of a slot without copying the whole aggregate.
    LoadProj(Slot, Vec<UProj>),
    StoreProj(Slot, Vec<UProj>, Temp),
    Unary(UnOp, Temp),
    /// Never `And`/`Or` (those are lowered to control flow).
    Binary(BinOp, Temp, Temp),
    /// Conversion of the operand to the destination type.
    Cast(Temp),
    Call(usize, Vec<Temp>),
    Builtin(Builtin, Vec<Temp>),
    /// Field values as (field index, value) in source evaluation order.
    MakeStruct(usize, Vec<(usize, Temp)>),
    Field(Temp, usize),
    /// Bounds-checked element read; the span is the index expression's.
    Index(Temp, Temp, Span),
    MakeArray(Vec<Temp>),
    Repeat(Temp, usize),
    MakeVariant(u32, Vec<Temp>),
    IsVariant(Temp, u32),
    /// Field `j` of the payload of variant `v` (only valid after `IsVariant` succeeded).
    Payload(Temp, u32, usize),
    /// Move field `j` of variant `v`'s payload out of the enum stored in a slot (only after `IsVariant` succeeded);
    /// the payload is left empty so the enum's drop glue skips it. Used by by-value `match` on owning enums.
    TakePayload(Slot, u32, usize),
    /// Create a reference to the place `slot` + projection path (bounds-checked now). Result type is `&T`/`&mut T`.
    AddrOf(Slot, Vec<UProj>),
    /// Move the owned value out of a slot (the slot is left empty).
    Take(Slot),
    /// Drop the owned value at the place (no-op if already moved out); the place is left empty. No destination.
    Drop(Slot, Vec<UProj>),
}

#[derive(Debug, Clone, PartialEq)]
pub struct UInstr { pub dest: Option<Temp>, pub op: UOp, pub span: Span }

#[derive(Debug, Clone, PartialEq)]
pub enum UTerm {
    Br(BlockId),
    CondBr(Temp, BlockId, BlockId),
    Ret(Temp),
    /// Control must never reach here (message is for diagnostics of compiler bugs).
    Trap(&'static str),
}

#[derive(Debug, Clone, PartialEq)]
pub struct UBlock { pub instrs: Vec<UInstr>, pub term: UTerm }

#[derive(Debug, Clone)]
pub struct UFn {
    pub name: String, pub layer: Layer, pub ext: crate::ast::Ext,
    pub nparams: usize, pub ret: Ty,
    pub slots: Vec<Ty>, pub temps: Vec<Ty>,
    pub blocks: Vec<UBlock>,
}

#[derive(Debug, Clone)]
pub struct UProgram { pub fns: Vec<UFn>, pub structs: Vec<StructDef>, pub enums: Vec<EnumDef>, pub main: Option<usize> }

// ---------------------------------------------------------------- printing

fn tn(p: &UProgram, t: &Ty) -> String {
    match t {
        Ty::Int(i) => i.name().into(), Ty::Float => "f64".into(), Ty::Bool => "bool".into(), Ty::Str => "str".into(),
        Ty::Unit => "()".into(), Ty::Never => "!".into(), Ty::Error => "<error>".into(), Ty::Var(v) => format!("?{}", v),
        Ty::Struct(i) => p.structs.get(*i).map(|s| s.name.clone()).unwrap_or_else(|| format!("struct#{}", i)),
        Ty::Enum(i) => p.enums.get(*i).map(|s| s.name.clone()).unwrap_or_else(|| format!("enum#{}", i)),
        Ty::Array(e, n) => format!("[{}; {}]", tn(p, e), n),
        Ty::Ref(t, m) => format!("&{}{}", if *m { "mut " } else { "" }, tn(p, t)),
        Ty::String => "String".into(),
        Ty::Vec(e) => format!("Vec<{}>", tn(p, e)),
        Ty::Box(e) => format!("Box<{}>", tn(p, e)),
    }
}

fn vals(v: &Value) -> String {
    match v {
        Value::Int(i) => i.to_string(), Value::Float(f) => format!("{:?}", f), Value::Bool(b) => b.to_string(),
        Value::Str(s) => format!("{:?}", s), Value::Unit => "()".into(),
        _ => "<aggregate>".into(),
    }
}

fn ts(v: &[Temp]) -> String { v.iter().map(|t| format!("%{}", t)).collect::<Vec<_>>().join(", ") }

fn projs(v: &[UProj]) -> String {
    v.iter().map(|p| match p { UProj::Deref => "*".to_string(), UProj::Field(i) => format!(".{}", i), UProj::Index(t, _) => format!("[%{}]", t) }).collect()
}

impl UProgram {
    /// Human-readable dump (stable format; used by `kendrah dump-uir` and snapshot tests).
    pub fn dump(&self) -> String {
        let mut o = String::new();
        for (fi, f) in self.fns.iter().enumerate() {
            let params: Vec<String> = (0..f.nparams).map(|i| format!("${}: {}", i, tn(self, &f.slots[i]))).collect();
            let _ = writeln!(o, "fn #{} {}({}) -> {} @layer({}) {{", fi, f.name, params.join(", "), tn(self, &f.ret), f.layer.name());
            for (i, t) in f.slots.iter().enumerate().skip(f.nparams) { let _ = writeln!(o, "  slot ${}: {}", i, tn(self, t)); }
            for (bi, b) in f.blocks.iter().enumerate() {
                let _ = writeln!(o, " b{}:", bi);
                for ins in &b.instrs {
                    let rhs = match &ins.op {
                        UOp::Const(v) => format!("const {}", vals(v)),
                        UOp::Load(s) => format!("load ${}", s),
                        UOp::Store(s, t) => format!("store ${}, %{}", s, t),
                        UOp::LoadProj(s, p) => format!("loadproj ${}{}", s, projs(p)),
                        UOp::StoreProj(s, p, t) => format!("storeproj ${}{}, %{}", s, projs(p), t),
                        UOp::Unary(op, t) => format!("{} %{}", if *op == UnOp::Neg { "neg" } else { "not" }, t),
                        UOp::Binary(op, a, b) => format!("{:?} %{}, %{}", op, a, b).to_lowercase(),
                        UOp::Cast(t) => format!("cast %{}", t),
                        UOp::Call(id, a) => format!("call #{}({})", id, ts(a)),
                        UOp::Builtin(b, a) => format!("builtin {:?}({})", b, ts(a)).to_lowercase(),
                        UOp::MakeStruct(id, fs) => format!("struct #{} {{{}}}", id, fs.iter().map(|(i, t)| format!(".{}=%{}", i, t)).collect::<Vec<_>>().join(", ")),
                        UOp::Field(t, i) => format!("field %{}.{}", t, i),
                        UOp::Index(a, i, _) => format!("index %{}[%{}]", a, i),
                        UOp::MakeArray(a) => format!("array [{}]", ts(a)),
                        UOp::Repeat(t, n) => format!("repeat %{}; {}", t, n),
                        UOp::MakeVariant(v, a) => format!("variant {}({})", v, ts(a)),
                        UOp::IsVariant(t, v) => format!("isvariant %{}, {}", t, v),
                        UOp::Payload(t, v, j) => format!("payload %{}, {}.{}", t, v, j),
                        UOp::TakePayload(s, v, j) => format!("takepayload ${}, {}.{}", s, v, j),
                        UOp::AddrOf(s, p) => format!("addrof ${}{}", s, projs(p)),
                        UOp::Take(s) => format!("take ${}", s),
                        UOp::Drop(s, p) => format!("drop ${}{}", s, projs(p)),
                    };
                    match ins.dest {
                        Some(d) => { let _ = writeln!(o, "   %{}: {} = {}", d, tn(self, &f.temps[d]), rhs); }
                        None => { let _ = writeln!(o, "   {}", rhs); }
                    }
                }
                let _ = match &b.term {
                    UTerm::Br(t) => writeln!(o, "   br b{}", t),
                    UTerm::CondBr(c, a, b2) => writeln!(o, "   condbr %{}, b{}, b{}", c, a, b2),
                    UTerm::Ret(t) => writeln!(o, "   ret %{}", t),
                    UTerm::Trap(m) => writeln!(o, "   trap {:?}", m),
                };
            }
            let _ = writeln!(o, "}}");
        }
        o
    }
}

// ---------------------------------------------------------------- verification

/// Type equality where `!` (only produced in unreachable code) is compatible with anything.
/// Reference mutability is a front-end property: UIR only distinguishes reference from non-reference.
fn teq(a: &Ty, b: &Ty) -> bool {
    match (a, b) {
        (Ty::Ref(x, _), Ty::Ref(y, _)) => teq(x, y),
        _ => a == b || *a == Ty::Never || *b == Ty::Never,
    }
}

fn is_int(t: &Ty) -> bool { matches!(t, Ty::Int(_)) }
fn is_num(t: &Ty) -> bool { matches!(t, Ty::Int(_) | Ty::Float) }
fn is_sref(t: &Ty) -> bool { matches!(t, Ty::Ref(i, _) if **i == Ty::String) || *t == Ty::Never }
/// Element type of a `&Vec<T>` / `&mut Vec<T>` operand (`mutable` selects which).
fn vref_elem(t: &Ty, mutable: bool) -> Option<Ty> {
    match t { Ty::Ref(i, m) if (*m || !mutable) => match &**i { Ty::Vec(e) => Some((**e).clone()), _ => None }, _ => None }
}
fn is_scalar(t: &Ty) -> bool { matches!(t, Ty::Int(_) | Ty::Float | Ty::Bool | Ty::Str) }

fn bad_ty(t: &Ty) -> bool {
    match t { Ty::Var(_) | Ty::Error => true, Ty::Array(e, _) | Ty::Ref(e, _) | Ty::Vec(e) | Ty::Box(e) => bad_ty(e), _ => false }
}

/// Check every UIR invariant (docs/UIR.md section 4). Returns all violations found.
pub fn verify(p: &UProgram) -> Result<(), Vec<String>> {
    let mut errs = Vec::new();
    for (fi, f) in p.fns.iter().enumerate() {
        Verifier { p, f, fi, errs: &mut errs }.run();
    }
    if let Some(m) = p.main {
        if m >= p.fns.len() { errs.push(format!("main index {} out of range", m)); }
    }
    if errs.is_empty() { Ok(()) } else { Err(errs) }
}

struct Verifier<'a> { p: &'a UProgram, f: &'a UFn, fi: usize, errs: &'a mut Vec<String> }

impl<'a> Verifier<'a> {
    fn e(&mut self, b: usize, i: Option<usize>, m: impl AsRef<str>) {
        let loc = match i { Some(i) => format!("fn #{} `{}` b{} instr {}", self.fi, self.f.name, b, i), None => format!("fn #{} `{}` b{}", self.fi, self.f.name, b) };
        self.errs.push(format!("{}: {}", loc, m.as_ref()));
    }

    fn run(&mut self) {
        let f = self.f;
        if f.blocks.is_empty() { self.e(0, None, "function has no blocks"); return; }
        if f.nparams > f.slots.len() { self.e(0, None, "more parameters than slots"); }
        for (i, t) in f.slots.iter().chain(f.temps.iter()).chain(std::iter::once(&f.ret)).enumerate() {
            if bad_ty(t) { self.e(0, None, format!("unresolved/error type in declaration #{}", i)); }
        }
        let mut defined_anywhere: HashSet<Temp> = HashSet::new();
        for (bi, b) in f.blocks.iter().enumerate() {
            let mut local: HashSet<Temp> = HashSet::new();
            for (ii, ins) in b.instrs.iter().enumerate() {
                for t in Self::uses(&ins.op) {
                    if t >= f.temps.len() { self.e(bi, Some(ii), format!("temp %{} out of range", t)); }
                    else if !local.contains(&t) { self.e(bi, Some(ii), format!("temp %{} used before definition or outside its defining block", t)); }
                }
                self.instr(bi, ii, ins);
                match ins.dest {
                    Some(d) if d >= f.temps.len() => self.e(bi, Some(ii), format!("dest %{} out of range", d)),
                    Some(d) => {
                        if !defined_anywhere.insert(d) { self.e(bi, Some(ii), format!("temp %{} defined more than once", d)); }
                        local.insert(d);
                    }
                    None => {}
                }
            }
            let tt = |s: &Self, t: Temp| -> Option<Ty> { s.f.temps.get(t).cloned() };
            match &b.term {
                UTerm::Br(t) => if *t >= f.blocks.len() { self.e(bi, None, format!("branch target b{} out of range", t)); },
                UTerm::CondBr(c, x, y) => {
                    for t in [x, y] { if *t >= f.blocks.len() { self.e(bi, None, format!("branch target b{} out of range", t)); } }
                    if !local.contains(c) { self.e(bi, None, format!("condbr condition %{} not defined in this block", c)); }
                    else if let Some(ct) = tt(self, *c) { if !teq(&ct, &Ty::Bool) { self.e(bi, None, format!("condbr condition has type {}", tn(self.p, &ct))); } }
                }
                UTerm::Ret(t) => {
                    if !local.contains(t) { self.e(bi, None, format!("ret value %{} not defined in this block", t)); }
                    else if let Some(rt) = tt(self, *t) { if !teq(&rt, &f.ret) { self.e(bi, None, format!("ret type {} != declared {}", tn(self.p, &rt), tn(self.p, &f.ret))); } }
                }
                UTerm::Trap(_) => {}
            }
        }
    }

    fn uses(op: &UOp) -> Vec<Temp> {
        let proj_uses = |ps: &[UProj]| -> Vec<Temp> { ps.iter().filter_map(|p| if let UProj::Index(t, _) = p { Some(*t) } else { None }).collect() };
        match op {
            UOp::Const(_) | UOp::Load(_) | UOp::Take(_) | UOp::TakePayload(..) => vec![],
            UOp::Drop(_, ps) => proj_uses(ps),
            UOp::Store(_, t) | UOp::Unary(_, t) | UOp::Cast(t) | UOp::Field(t, _) | UOp::Repeat(t, _) | UOp::IsVariant(t, _) | UOp::Payload(t, _, _) => vec![*t],
            UOp::LoadProj(_, ps) => proj_uses(ps),
            UOp::StoreProj(_, ps, t) => { let mut v = proj_uses(ps); v.push(*t); v }
            UOp::Binary(_, a, b) | UOp::Index(a, b, _) => vec![*a, *b],
            UOp::Call(_, a) | UOp::Builtin(_, a) | UOp::MakeArray(a) | UOp::MakeVariant(_, a) => a.clone(),
            UOp::MakeStruct(_, fs) => fs.iter().map(|(_, t)| *t).collect(),
            UOp::AddrOf(_, ps) => proj_uses(ps),
        }
    }

    fn ty(&self, t: Temp) -> Ty { self.f.temps.get(t).cloned().unwrap_or(Ty::Error) }

    /// Type reached by following `ps` from `base`; reports problems.
    fn walk(&mut self, b: usize, i: usize, mut base: Ty, ps: &[UProj]) -> Option<Ty> {
        for (k, p) in ps.iter().enumerate() {
            base = match (p, &base) {
                (UProj::Deref, Ty::Ref(t, _)) if k == 0 => (**t).clone(),
                (UProj::Deref, o) => { self.e(b, Some(i), format!("deref must be the first projection of a reference-typed slot (found on {} at position {})", tn(self.p, o), k)); return None; }
                (UProj::Field(k), Ty::Struct(id)) => match self.p.structs.get(*id).and_then(|s| s.fields.get(*k)) {
                    Some((_, t)) => t.clone(),
                    None => { self.e(b, Some(i), "field index out of range"); return None; }
                },
                (UProj::Index(t, _), Ty::Array(e, _)) => {
                    let it = self.ty(*t);
                    if !is_int(&it) && it != Ty::Never { self.e(b, Some(i), "array index must be an integer"); }
                    (**e).clone()
                }
                (_, other) => { self.e(b, Some(i), format!("cannot project into {}", tn(self.p, other))); return None; }
            };
        }
        Some(base)
    }

    fn instr(&mut self, b: usize, i: usize, ins: &UInstr) {
        let p = self.p;
        let dest_ty = ins.dest.and_then(|d| self.f.temps.get(d).cloned());
        let needs_dest = !matches!(&ins.op, UOp::Store(..) | UOp::StoreProj(..) | UOp::Drop(..));
        if needs_dest && ins.dest.is_none() { self.e(b, Some(i), "instruction requires a destination"); return; }
        if matches!(&ins.op, UOp::Store(..) | UOp::StoreProj(..) | UOp::Drop(..)) && ins.dest.is_some() { self.e(b, Some(i), "store/drop must not have a destination"); }
        let d = dest_ty.clone().unwrap_or(Ty::Unit);
        macro_rules! want { ($cond:expr, $($m:tt)*) => { if !$cond { self.e(b, Some(i), format!($($m)*)); } } }
        match &ins.op {
            UOp::Const(v) => {
                let ok = match (v, &d) {
                    (Value::Int(x), Ty::Int(k)) => k.contains(*x),
                    (Value::Float(_), Ty::Float) | (Value::Bool(_), Ty::Bool) | (Value::Str(_), Ty::Str) | (Value::Unit, Ty::Unit) => true,
                    (_, Ty::Never) => true,
                    _ => false,
                };
                want!(ok, "constant {} does not fit destination type {}", vals(v), tn(p, &d));
            }
            UOp::Load(s) => match self.f.slots.get(*s) {
                Some(st) => want!(teq(st, &d), "load of ${} ({}) into {}", s, tn(p, st), tn(p, &d)),
                None => self.e(b, Some(i), format!("slot ${} out of range", s)),
            },
            UOp::Store(s, t) => match self.f.slots.get(*s) {
                Some(st) => { let tt = self.ty(*t); want!(teq(st, &tt), "store of {} into ${} ({})", tn(p, &tt), s, tn(p, st)) }
                None => self.e(b, Some(i), format!("slot ${} out of range", s)),
            },
            UOp::LoadProj(s, ps) => match self.f.slots.get(*s).cloned() {
                Some(st) => if let Some(t) = self.walk(b, i, st, ps) { want!(teq(&t, &d), "loadproj yields {} but dest is {}", tn(p, &t), tn(p, &d)) },
                None => self.e(b, Some(i), format!("slot ${} out of range", s)),
            },
            UOp::Take(s) => match self.f.slots.get(*s) {
                Some(st) => want!(crate::hir::owned_ty(st, &self.p.structs, &self.p.enums) && teq(&d, st), "take of ${} ({}) into {}", s, tn(p, st), tn(p, &d)),
                None => self.e(b, Some(i), format!("slot ${} out of range", s)),
            },
            UOp::Drop(s, ps) => match self.f.slots.get(*s).cloned() {
                Some(st) => if let Some(t) = self.walk(b, i, st, ps) { want!(crate::hir::owned_ty(&t, &self.p.structs, &self.p.enums), "drop of a place of type {}", tn(p, &t)) },
                None => self.e(b, Some(i), format!("slot ${} out of range", s)),
            },
            UOp::AddrOf(s, ps) => match self.f.slots.get(*s).cloned() {
                Some(st) => if let Some(t) = self.walk(b, i, st, ps) {
                    match &d {
                        Ty::Ref(inner, _) => want!(teq(inner, &t), "addrof place has type {} but result points to {}", tn(p, &t), tn(p, inner)),
                        o => self.e(b, Some(i), format!("addrof must produce a reference, not {}", tn(p, o))),
                    }
                },
                None => self.e(b, Some(i), format!("slot ${} out of range", s)),
            },
            UOp::StoreProj(s, ps, t) => match self.f.slots.get(*s).cloned() {
                Some(st) => if let Some(pt) = self.walk(b, i, st, ps) { let tt = self.ty(*t); want!(teq(&pt, &tt), "storeproj of {} into place of type {}", tn(p, &tt), tn(p, &pt)) },
                None => self.e(b, Some(i), format!("slot ${} out of range", s)),
            },
            UOp::Unary(op, t) => {
                let tt = self.ty(*t);
                let ok = match (op, &tt) {
                    (UnOp::Neg, Ty::Int(k)) => k.signed() && teq(&d, &tt),
                    (UnOp::Neg, Ty::Float) | (UnOp::Not, Ty::Bool) => teq(&d, &tt),
                    (_, Ty::Never) => true,
                    _ => false,
                };
                want!(ok, "bad unary operand {} / result {}", tn(p, &tt), tn(p, &d));
            }
            UOp::Binary(op, a, c) => {
                use BinOp::*;
                let (ta, tc) = (self.ty(*a), self.ty(*c));
                let ok = if ta == Ty::Never || tc == Ty::Never { true } else { match op {
                    And | Or => false,
                    Eq | Ne => ta == tc && is_scalar(&ta) && teq(&d, &Ty::Bool),
                    Lt | Le | Gt | Ge => ta == tc && is_num(&ta) && teq(&d, &Ty::Bool),
                    Add if ta == Ty::Str => tc == Ty::Str && teq(&d, &Ty::Str),
                    Add | Sub | Mul | Div | Rem => ta == tc && is_num(&ta) && teq(&d, &ta),
                    BitAnd | BitOr | BitXor => ta == tc && is_int(&ta) && teq(&d, &ta),
                    Shl | Shr => is_int(&ta) && is_int(&tc) && teq(&d, &ta),
                } };
                want!(ok, "bad binary operands {:?}: {} and {} -> {}", op, tn(p, &ta), tn(p, &tc), tn(p, &d));
            }
            UOp::Cast(t) => {
                let tt = self.ty(*t);
                let ok = (is_num(&tt) && is_num(&d)) || (tt == Ty::Bool && is_int(&d)) || tt == Ty::Never || d == Ty::Never;
                want!(ok, "invalid cast {} -> {}", tn(p, &tt), tn(p, &d));
            }
            UOp::Call(id, args) => match p.fns.get(*id) {
                None => self.e(b, Some(i), format!("call to unknown function #{}", id)),
                Some(callee) => {
                    if callee.nparams != args.len() { self.e(b, Some(i), format!("call to `{}` passes {} args, expects {}", callee.name, args.len(), callee.nparams)); }
                    else { for (k, a) in args.iter().enumerate() { let at = self.ty(*a); if !teq(&at, &callee.slots[k]) { self.e(b, Some(i), format!("argument {} of `{}`: {} != {}", k + 1, callee.name, tn(p, &at), tn(p, &callee.slots[k]))); } } }
                    match ins.dest { Some(_) => want!(teq(&d, &callee.ret), "call result {} != {}", tn(p, &callee.ret), tn(p, &d)), None => self.e(b, Some(i), "call requires a destination") }
                }
            },
            UOp::Builtin(bt, args) => {
                let at: Vec<Ty> = args.iter().map(|a| self.ty(*a)).collect();
                let i64t = Ty::Int(IntTy::I64);
                let ok = match bt {
                    Builtin::Print => at.len() == 1 && (is_scalar(&at[0]) || at[0] == Ty::Never || is_sref(&at[0])),
                    Builtin::Peek => at.len() == 1 && teq(&at[0], &i64t) && teq(&d, &i64t),
                    Builtin::Poke => at.len() == 2 && teq(&at[0], &i64t) && teq(&at[1], &i64t),
                    Builtin::Len => at.len() == 1 && matches!(at[0], Ty::Array(..) | Ty::Never) && teq(&d, &i64t),
                    Builtin::StringFrom => at.len() == 1 && teq(&at[0], &Ty::Str) && teq(&d, &Ty::String),
                    Builtin::StringConcat => at.len() == 2 && at.iter().all(is_sref) && teq(&d, &Ty::String),
                    Builtin::StringPush => at.len() == 2 && is_sref(&at[0]) && teq(&at[1], &Ty::Str),
                    Builtin::StringLen => at.len() == 1 && is_sref(&at[0]) && teq(&d, &i64t),
                    Builtin::StringClone => at.len() == 1 && is_sref(&at[0]) && teq(&d, &Ty::String),
                    Builtin::StringEq => at.len() == 2 && at.iter().all(is_sref) && teq(&d, &Ty::Bool),
                    Builtin::VecNew => at.is_empty() && matches!(d, Ty::Vec(_)),
                    Builtin::VecPush => at.len() == 2 && vref_elem(&at[0], true).map_or(false, |e| teq(&e, &at[1])),
                    Builtin::VecLen => at.len() == 1 && vref_elem(&at[0], false).is_some() && teq(&d, &i64t),
                    Builtin::VecGet => at.len() == 2 && vref_elem(&at[0], false).map_or(false, |e| teq(&e, &d)) && matches!(at[1], Ty::Int(_)),
                    Builtin::VecSet => at.len() == 3 && vref_elem(&at[0], true).map_or(false, |e| teq(&e, &at[2])) && matches!(at[1], Ty::Int(_)),
                    Builtin::VecPop => at.len() == 1 && vref_elem(&at[0], true).map_or(false, |e| teq(&e, &d)),
                    Builtin::BoxNew => at.len() == 1 && matches!(&d, Ty::Box(e) if teq(e, &at[0])),
                    Builtin::BoxInto => at.len() == 1 && matches!(&at[0], Ty::Box(e) if teq(e, &d)),
                    Builtin::BoxGet => at.len() == 1 && matches!(&at[0], Ty::Ref(i, _) if matches!(&**i, Ty::Box(e) if teq(e, &d))),
                    Builtin::BoxSet => at.len() == 2 && matches!(&at[0], Ty::Ref(i, true) if matches!(&**i, Ty::Box(e) if teq(e, &at[1]))) && teq(&d, &Ty::Unit),
                    Builtin::VecClone => at.len() == 1 && vref_elem(&at[0], false).map_or(false, |e| teq(&Ty::Vec(Box::new(e)), &d)),
                };
                want!(ok, "bad builtin call {:?}", bt);
            }
            UOp::MakeStruct(id, fs) => match p.structs.get(*id) {
                None => self.e(b, Some(i), "unknown struct"),
                Some(sd) => {
                    want!(teq(&d, &Ty::Struct(*id)), "struct literal typed {}", tn(p, &d));
                    let mut seen = HashSet::new();
                    for (k, t) in fs {
                        match sd.fields.get(*k) {
                            None => self.e(b, Some(i), "field index out of range"),
                            Some((_, ft)) => { let tt = self.ty(*t); want!(teq(ft, &tt), "field {} expects {} got {}", k, tn(p, ft), tn(p, &tt)); }
                        }
                        want!(seen.insert(*k), "field {} initialised twice", k);
                    }
                    want!(seen.len() == sd.fields.len(), "struct literal initialises {} of {} fields", seen.len(), sd.fields.len());
                }
            },
            UOp::Field(t, k) => {
                let tt = self.ty(*t);
                match &tt {
                    Ty::Struct(id) => match p.structs.get(*id).and_then(|s| s.fields.get(*k)) {
                        Some((_, ft)) => want!(teq(ft, &d), "field type {} != dest {}", tn(p, ft), tn(p, &d)),
                        None => self.e(b, Some(i), "field index out of range"),
                    },
                    Ty::Never => {}
                    o => self.e(b, Some(i), format!("field access on {}", tn(p, o))),
                }
            }
            UOp::Index(a, ix, _) => {
                let (ta, ti) = (self.ty(*a), self.ty(*ix));
                match &ta {
                    Ty::Array(e, _) => { want!(teq(e, &d), "element type {} != dest {}", tn(p, e), tn(p, &d)); want!(is_int(&ti) || ti == Ty::Never, "index must be an integer"); }
                    Ty::Never => {}
                    o => self.e(b, Some(i), format!("index into {}", tn(p, o))),
                }
            }
            UOp::MakeArray(ts_) => match &d {
                Ty::Array(e, n) => {
                    want!(*n == ts_.len(), "array literal has {} elements but type says {}", ts_.len(), n);
                    for t in ts_ { let tt = self.ty(*t); want!(teq(&tt, e), "array element {} != {}", tn(p, &tt), tn(p, e)); }
                }
                Ty::Never => {}
                o => self.e(b, Some(i), format!("array literal typed {}", tn(p, o))),
            },
            UOp::Repeat(t, n) => match &d {
                Ty::Array(e, m) => { let tt = self.ty(*t); want!(m == n, "repeat length {} != type length {}", n, m); want!(teq(&tt, e), "repeat element {} != {}", tn(p, &tt), tn(p, e)); }
                Ty::Never => {}
                o => self.e(b, Some(i), format!("repeat typed {}", tn(p, o))),
            },
            UOp::MakeVariant(v, args) => match &d {
                Ty::Enum(id) => match p.enums.get(*id).and_then(|e| e.variants.get(*v as usize)) {
                    None => self.e(b, Some(i), "variant index out of range"),
                    Some((_, payload)) => {
                        if payload.len() != args.len() { self.e(b, Some(i), "variant payload arity mismatch"); }
                        else { for (pt, a) in payload.iter().zip(args) { let at = self.ty(*a); want!(teq(pt, &at), "payload {} != {}", tn(p, &at), tn(p, pt)); } }
                    }
                },
                Ty::Never => {}
                o => self.e(b, Some(i), format!("variant typed {}", tn(p, o))),
            },
            UOp::IsVariant(t, v) => {
                let tt = self.ty(*t);
                want!(teq(&d, &Ty::Bool), "isvariant must produce bool");
                match &tt {
                    Ty::Enum(id) => want!((*v as usize) < p.enums[*id].variants.len(), "variant index out of range"),
                    Ty::Never => {}
                    o => self.e(b, Some(i), format!("isvariant on {}", tn(p, o))),
                }
            }
            UOp::TakePayload(s, v, j) => match self.f.slots.get(*s) {
                Some(Ty::Enum(id)) => match p.enums[*id].variants.get(*v as usize).and_then(|x| x.1.get(*j)) {
                    Some(pt) => want!(crate::hir::owned_ty(pt, &p.structs, &p.enums) && teq(pt, &d), "takepayload type {} != dest {} (or not owned)", tn(p, pt), tn(p, &d)),
                    None => self.e(b, Some(i), "payload index out of range"),
                },
                Some(o) => self.e(b, Some(i), format!("takepayload of ${} ({})", s, tn(p, o))),
                None => self.e(b, Some(i), format!("slot ${} out of range", s)),
            },
            UOp::Payload(t, v, j) => {
                let tt = self.ty(*t);
                match &tt {
                    Ty::Enum(id) => match p.enums[*id].variants.get(*v as usize).and_then(|x| x.1.get(*j)) {
                        Some(pt) => want!(teq(pt, &d), "payload type {} != dest {}", tn(p, pt), tn(p, &d)),
                        None => self.e(b, Some(i), "payload index out of range"),
                    },
                    Ty::Never => {}
                    o => self.e(b, Some(i), format!("payload of {}", tn(p, o))),
                }
            }
        }
    }
}
