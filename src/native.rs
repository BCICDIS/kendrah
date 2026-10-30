//! Native backend (target T1, x86-64 Linux; see docs/TARGETS.md): verified UIR -> LLVM IR text.
//!
//! The emitter never guesses: constructs it cannot translate faithfully are rejected up front with a located
//! diagnostic (`scan`), so it never produces code with different behaviour from the interpreters.
//!
//! Representation (v0): scalars are SSA values; every aggregate temp is a `ptr` to storage that is immutable for
//! the temp's lifetime (either its own hoisted alloca or a projection into another temp); slots are allocas.

use crate::ast::{BinOp, UnOp};
use crate::diag::{Diag, Span};
use crate::hir::{Builtin, EnumDef, Value};
use crate::interp::{MAX_DEPTH, MEM_SIZE};
use crate::ty::{IntTy, Ty};
use crate::uir::*;
use std::collections::{BTreeSet, HashMap};
use std::fmt::Write as _;
use std::path::{Path, PathBuf};

/// The C runtime linked into every native program.
pub const RUNTIME_C: &str = include_str!("../runtime/kd_rt.c");

// ---------------------------------------------------------------- type mapping

fn is_agg(t: &Ty) -> bool { matches!(t, Ty::Struct(_) | Ty::Enum(_) | Ty::Array(..)) }

/// LLVM type of a value held in a register.
fn vty(t: &Ty) -> String {
    match t {
        Ty::Int(k) => format!("i{}", k.bits()),
        Ty::Float => "double".into(),
        Ty::Bool => "i1".into(),
        Ty::Str => "{ ptr, i64 }".into(),
        Ty::Unit | Ty::Never => "i8".into(),
        Ty::Struct(_) | Ty::Enum(_) | Ty::Array(..) | Ty::Ref(..) | Ty::String | Ty::Vec(_) | Ty::Box(_) => "ptr".into(),
        Ty::Var(_) | Ty::Error => unreachable!("verified UIR has no unresolved types"),
    }
}

/// LLVM type of a value stored in memory.
fn mty(t: &Ty) -> String {
    match t {
        Ty::Struct(i) => format!("%S{}", i),
        Ty::Enum(i) => format!("%E{}", i),
        Ty::Array(e, n) => format!("[{} x {}]", n, mty(e)),
        _ => vty(t),
    }
}

fn sizeof(t: &Ty) -> String { format!("ptrtoint (ptr getelementptr ({}, ptr null, i32 1) to i64)", mty(t)) }

/// Index of the first payload field of variant `v` inside `%E<n>` (index 0 is the tag).
fn variant_base(e: &EnumDef, v: usize) -> usize { 1 + e.variants[..v].iter().map(|x| x.1.len()).sum::<usize>() }

fn used_temps(op: &UOp) -> Vec<Temp> {
    let path = |p: &[UProj]| -> Vec<Temp> { p.iter().filter_map(|x| if let UProj::Index(t, _) = x { Some(*t) } else { None }).collect() };
    match op {
        UOp::Const(_) | UOp::Load(_) | UOp::Take(_) | UOp::TakePayload(..) => vec![],
        UOp::Store(_, t) => vec![*t],
        UOp::LoadProj(_, p) | UOp::AddrOf(_, p) | UOp::Drop(_, p) => path(p),
        UOp::StoreProj(_, p, t) => { let mut v = path(p); v.push(*t); v }
        UOp::Unary(_, t) | UOp::Cast(t) | UOp::Field(t, _) | UOp::Repeat(t, _) | UOp::IsVariant(t, _) | UOp::Payload(t, _, _) => vec![*t],
        UOp::Binary(_, a, b) | UOp::Index(a, b, _) => vec![*a, *b],
        UOp::Call(_, a) | UOp::Builtin(_, a) | UOp::MakeArray(a) | UOp::MakeVariant(_, a) => a.clone(),
        UOp::MakeStruct(_, fs) => fs.iter().map(|x| x.1).collect(),
    }
}

// ---------------------------------------------------------------- support scan

fn reachable(p: &UProgram, main: usize) -> Vec<usize> {
    let mut seen = vec![false; p.fns.len()];
    let mut stack = vec![main];
    seen[main] = true;
    // exported functions are roots: C code may call them although no Kendrah code does
    for (i, f) in p.fns.iter().enumerate() {
        if f.ext == crate::ast::Ext::Export && !seen[i] { seen[i] = true; stack.push(i); }
    }
    while let Some(f) = stack.pop() {
        for b in &p.fns[f].blocks {
            for i in &b.instrs {
                if let UOp::Call(id, _) = &i.op { if !seen[*id] { seen[*id] = true; stack.push(*id); } }
            }
        }
    }
    (0..p.fns.len()).filter(|i| seen[*i]).collect()
}

/// Reject, with located diagnostics, everything the native target cannot translate faithfully.
fn scan(p: &UProgram, fns: &[usize]) -> Vec<Diag> {
    let mut ds = Vec::new();
    for &fi in fns {
        let f = &p.fns[fi];
        for b in &f.blocks {
            for i in &b.instrs {
                match &i.op {
                    UOp::Binary(BinOp::Add, a, _) if f.temps[*a] == Ty::Str => ds.push(Diag::new(i.span,
                        "string concatenation is not supported by the native backend: it needs heap allocation (M4, see docs/TARGETS.md)")),
                    _ => {}
                }
            }
        }
    }
    ds
}

// ---------------------------------------------------------------- module-level state

#[derive(Default)]
struct Globals {
    strs: Vec<Vec<u8>>,
    str_ix: HashMap<Vec<u8>, usize>,
    decls: BTreeSet<String>,
    /// Inner types of every `Box<T>` whose drop glue `@kd_drop_B<k>` is needed.
    boxes: Vec<Ty>,
}

impl Globals {
    fn string(&mut self, b: &[u8]) -> (String, usize) {
        let ix = match self.str_ix.get(b) {
            Some(i) => *i,
            None => { self.strs.push(b.to_vec()); self.str_ix.insert(b.to_vec(), self.strs.len() - 1); self.strs.len() - 1 }
        };
        (format!("@.s{}", ix), b.len())
    }
    fn decl(&mut self, s: impl Into<String>) { self.decls.insert(s.into()); }
    fn box_id(&mut self, inner: &Ty) -> usize {
        match self.boxes.iter().position(|t| t == inner) { Some(i) => i, None => { self.boxes.push(inner.clone()); self.boxes.len() - 1 } }
    }
}

/// C-ABI argument/return extension attribute: x86-64 callers extend sub-32-bit integers to 32 bits.
fn cabi_attr(t: &Ty) -> &'static str {
    match t { Ty::Int(k) if k.bits() < 32 => if k.signed() { " signext" } else { " zeroext" }, _ => "" }
}

/// LLVM return type of a C-ABI function (`void` for Kendrah's unit).
fn cabi_ret(t: &Ty) -> String { if *t == Ty::Unit { "void".into() } else { vty(t) } }

fn llvm_bytes(b: &[u8]) -> String {
    let mut s = String::new();
    for &c in b {
        if (0x20..0x7f).contains(&c) && c != b'"' && c != b'\\' { s.push(c as char); } else { let _ = write!(s, "\\{:02X}", c); }
    }
    s
}

// ---------------------------------------------------------------- per-function emitter

struct Fx<'a> {
    p: &'a UProgram,
    f: &'a UFn,
    g: &'a mut Globals,
    body: String,
    allocas: String,
    n: usize,
    /// Temps whose value is a literal/alias/`undef` instead of an instruction result.
    repl: HashMap<Temp, String>,
}

impl<'a> Fx<'a> {
    fn aux(&mut self) -> String { self.n += 1; format!("%x{}", self.n) }
    fn line(&mut self, s: impl AsRef<str>) { self.body.push_str("  "); self.body.push_str(s.as_ref()); self.body.push('\n'); }
    fn label(&mut self, l: &str) { self.body.push_str(l); self.body.push_str(":\n"); }
    fn op(&self, t: Temp) -> String { self.repl.get(&t).cloned().unwrap_or_else(|| format!("%t{}", t)) }
    fn tty(&self, t: Temp) -> &Ty { &self.f.temps[t] }
    fn vt(&self, t: Temp) -> String { vty(self.tty(t)) }
    fn int_of(&self, t: Temp) -> IntTy { match self.tty(t) { Ty::Int(k) => *k, o => unreachable!("verified: integer expected, got {:?}", o) } }

    fn hoist(&mut self, name: &str, ty: &Ty) { let _ = writeln!(self.allocas, "  {} = alloca {}", name, mty(ty)); }

    fn memcpy(&mut self, dst: &str, src: &str, ty: &Ty) {
        self.g.decl("declare void @llvm.memcpy.p0.p0.i64(ptr, ptr, i64, i1)");
        self.line(format!("call void @llvm.memcpy.p0.p0.i64(ptr {}, ptr {}, i64 {}, i1 false)", dst, src, sizeof(ty)));
    }

    /// Store the temp `t` (scalar or aggregate) into memory at `ptr`.
    fn store_temp(&mut self, ptr: &str, t: Temp) {
        let ty = self.tty(t).clone();
        let v = self.op(t);
        if is_agg(&ty) { self.memcpy(ptr, &v, &ty); } else { self.line(format!("store {} {}, ptr {}", vty(&ty), v, ptr)); }
    }

    /// Define `dest` as the value stored at `ptr` of type `ty`: a load for scalars, an alias of the pointer for
    /// aggregates (sound because temps are immutable and the parent temp outlives it).
    fn read_borrowed(&mut self, dest: Temp, ptr: String, ty: &Ty) {
        if is_agg(ty) { self.repl.insert(dest, ptr); } else { self.line(format!("%t{} = load {}, ptr {}", dest, vty(ty), ptr)); }
    }

    fn fail_call(&mut self, span: Span, msg: &str) -> String {
        self.g.decl("declare void @kd_fail(i32, i32, ptr, i64) noreturn");
        let (s, n) = self.g.string(msg.as_bytes());
        format!("call void @kd_fail(i32 {}, i32 {}, ptr {}, i64 {})", span.line, span.col, s, n)
    }

    /// `if cond { <call>; unreachable }`, continuing in a fresh block.
    fn cond_fail(&mut self, cond: &str, call: String) {
        self.n += 1;
        let (f, k) = (format!("f{}", self.n), format!("k{}", self.n));
        self.line(format!("br i1 {}, label %{}, label %{}", cond, f, k));
        self.label(&f);
        self.line(call);
        self.line("unreachable");
        self.label(&k);
    }

    fn to_i64(&mut self, v: &str, k: IntTy) -> String {
        if k.bits() == 64 { return v.to_string(); }
        let x = self.aux();
        self.line(format!("{} = {} i{} {} to i64", x, if k.signed() { "sext" } else { "zext" }, k.bits(), v));
        x
    }

    /// Bounds-check index temp `it` against `n`; returns the index as i64 (unsigned compare also rejects negatives).
    fn bounds(&mut self, it: Temp, n: usize, span: Span) -> String {
        let k = self.int_of(it);
        let raw = self.op(it);
        let v = self.to_i64(&raw, k);
        let c = self.aux();
        self.line(format!("{} = icmp uge i64 {}, {}", c, v, n));
        self.g.decl("declare void @kd_oob(i32, i32, i64, i32, i64) noreturn");
        let call = format!("call void @kd_oob(i32 {}, i32 {}, i64 {}, i32 {}, i64 {})", span.line, span.col, v, if k.signed() { 0 } else { 1 }, n);
        self.cond_fail(&c, call);
        v
    }

    /// Walk a projection path from `cur` (a pointer to a value of type `ty`); returns the final pointer and type.
    fn walk(&mut self, mut cur: String, mut ty: Ty, path: &[UProj]) -> (String, Ty) {
        for pr in path {
            match (pr, ty.clone()) {
                (UProj::Deref, Ty::Ref(t, _)) => {
                    let x = self.aux();
                    self.line(format!("{} = load ptr, ptr {}", x, cur));
                    ty = *t;
                    cur = x;
                }
                (UProj::Field(i), Ty::Struct(id)) => {
                    let x = self.aux();
                    self.line(format!("{} = getelementptr %S{}, ptr {}, i32 0, i32 {}", x, id, cur, i));
                    ty = self.p.structs[id].fields[*i].1.clone();
                    cur = x;
                }
                (UProj::Index(t, span), Ty::Array(e, n)) => {
                    let idx = self.bounds(*t, n, *span);
                    let x = self.aux();
                    self.line(format!("{} = getelementptr {}, ptr {}, i64 0, i64 {}", x, mty(&ty), cur, idx));
                    ty = *e;
                    cur = x;
                }
                (p, t) => unreachable!("verified: bad projection {:?} on {:?}", p, t),
            }
        }
        (cur, ty)
    }

    fn scalar_lit(&self, v: &Value, ty: &Ty) -> String {
        match (v, ty) {
            (Value::Int(i), Ty::Int(k)) => k.wrap(*i).to_string(),
            (Value::Float(f), _) => format!("0x{:016X}", f.to_bits()),
            (Value::Bool(b), _) => b.to_string(),
            (Value::Unit, _) => "0".into(),
            _ => unreachable!("verified: constant {:?} of type {:?}", v, ty),
        }
    }

    fn str_lit(&mut self, s: &str) -> String {
        let (g, n) = self.g.string(s.as_bytes());
        format!("{{ ptr {}, i64 {} }}", g, n)
    }

    /// Initialise memory at `ptr` (of type `ty`) from a constant.
    fn store_value(&mut self, ptr: &str, ty: &Ty, v: &Value) {
        match (v, ty) {
            (Value::Struct(vs), Ty::Struct(id)) => {
                for (i, x) in vs.iter().enumerate() {
                    let q = self.aux();
                    self.line(format!("{} = getelementptr %S{}, ptr {}, i32 0, i32 {}", q, id, ptr, i));
                    let ft = self.p.structs[*id].fields[i].1.clone();
                    self.store_value(&q, &ft, x);
                }
            }
            (Value::Array(vs), Ty::Array(e, _)) => {
                for (i, x) in vs.iter().enumerate() {
                    let q = self.aux();
                    self.line(format!("{} = getelementptr {}, ptr {}, i64 0, i64 {}", q, mty(ty), ptr, i));
                    self.store_value(&q, e, x);
                }
            }
            (Value::Enum(tag, vs), Ty::Enum(id)) => {
                let base = variant_base(&self.p.enums[*id], *tag as usize);
                let t = self.aux();
                self.line(format!("{} = getelementptr %E{}, ptr {}, i32 0, i32 0", t, id, ptr));
                self.line(format!("store i32 {}, ptr {}", tag, t));
                for (j, x) in vs.iter().enumerate() {
                    let q = self.aux();
                    self.line(format!("{} = getelementptr %E{}, ptr {}, i32 0, i32 {}", q, id, ptr, base + j));
                    let ft = self.p.enums[*id].variants[*tag as usize].1[j].clone();
                    self.store_value(&q, &ft, x);
                }
            }
            (Value::Str(s), _) => { let l = self.str_lit(s); self.line(format!("store {{ ptr, i64 }} {}, ptr {}", l, ptr)); }
            (v, t) => { let l = self.scalar_lit(v, t); self.line(format!("store {} {}, ptr {}", vty(t), l, ptr)); }
        }
    }

    // ---- arithmetic

    fn checked(&mut self, opn: &str, what: &str, k: IntTy, a: &str, b: &str, dest: &str, span: Span) {
        let w = k.bits();
        let name = format!("llvm.{}{}.with.overflow.i{}", if k.signed() { "s" } else { "u" }, opn, w);
        self.g.decl(format!("declare {{ i{w}, i1 }} @{name}(i{w}, i{w})"));
        let r = self.aux();
        self.line(format!("{r} = call {{ i{w}, i1 }} @{name}(i{w} {a}, i{w} {b})"));
        self.line(format!("{dest} = extractvalue {{ i{w}, i1 }} {r}, 0"));
        let o = self.aux();
        self.line(format!("{o} = extractvalue {{ i{w}, i1 }} {r}, 1"));
        let c = self.fail_call(span, &format!("integer overflow in {} ({})", what, k.name()));
        self.cond_fail(&o, c);
    }

    fn int_binary(&mut self, op: BinOp, k: IntTy, a: &str, b: &str, bt: Temp, dest: &str, span: Span) {
        let w = k.bits();
        let s = k.signed();
        match op {
            BinOp::Add => self.checked("add", "addition", k, a, b, dest, span),
            BinOp::Sub => self.checked("sub", "subtraction", k, a, b, dest, span),
            BinOp::Mul => self.checked("mul", "multiplication", k, a, b, dest, span),
            BinOp::Div | BinOp::Rem => {
                let (zmsg, what, ins) = if op == BinOp::Div {
                    ("division by zero", "division", if s { "sdiv" } else { "udiv" })
                } else { ("remainder by zero", "remainder", if s { "srem" } else { "urem" }) };
                let z = self.aux();
                self.line(format!("{z} = icmp eq i{w} {b}, 0"));
                let c = self.fail_call(span, zmsg);
                self.cond_fail(&z, c);
                if s {
                    let (m, n, o) = (self.aux(), self.aux(), self.aux());
                    self.line(format!("{m} = icmp eq i{w} {a}, {}", k.min()));
                    self.line(format!("{n} = icmp eq i{w} {b}, -1"));
                    self.line(format!("{o} = and i1 {m}, {n}"));
                    let c = self.fail_call(span, &format!("integer overflow in {} ({})", what, k.name()));
                    self.cond_fail(&o, c);
                }
                self.line(format!("{dest} = {ins} i{w} {a}, {b}"));
            }
            BinOp::BitAnd => self.line(format!("{dest} = and i{w} {a}, {b}")),
            BinOp::BitOr => self.line(format!("{dest} = or i{w} {a}, {b}")),
            BinOp::BitXor => self.line(format!("{dest} = xor i{w} {a}, {b}")),
            BinOp::Shl | BinOp::Shr => {
                let kb = self.int_of(bt);
                let wb = kb.bits();
                let bad = self.aux();
                // Unsigned compare at the rhs width also rejects negative amounts; `w` always fits in the rhs type.
                self.line(format!("{bad} = icmp uge i{wb} {b}, {w}"));
                self.g.decl("declare void @kd_shift_fail(i32, i32, i64, i32, ptr, i64, i32) noreturn");
                let b64 = self.to_i64(b, kb);
                let (tn, tl) = self.g.string(k.name().as_bytes());
                let call = format!("call void @kd_shift_fail(i32 {}, i32 {}, i64 {}, i32 {}, ptr {}, i64 {}, i32 {})",
                    span.line, span.col, b64, if kb.signed() { 0 } else { 1 }, tn, tl, w);
                self.cond_fail(&bad, call);
                let amt = if wb == w { b.to_string() } else {
                    let x = self.aux();
                    if wb > w { self.line(format!("{x} = trunc i{wb} {b} to i{w}")); } else { self.line(format!("{x} = zext i{wb} {b} to i{w}")); }
                    x
                };
                let ins = if op == BinOp::Shl { "shl" } else if s { "ashr" } else { "lshr" };
                self.line(format!("{dest} = {ins} i{w} {a}, {amt}"));
            }
            BinOp::Eq | BinOp::Ne | BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge => {
                let pr = match (op, s) {
                    (BinOp::Eq, _) => "eq", (BinOp::Ne, _) => "ne",
                    (BinOp::Lt, true) => "slt", (BinOp::Le, true) => "sle", (BinOp::Gt, true) => "sgt", (BinOp::Ge, true) => "sge",
                    (BinOp::Lt, false) => "ult", (BinOp::Le, false) => "ule", (BinOp::Gt, false) => "ugt", (BinOp::Ge, false) => "uge",
                    _ => unreachable!(),
                };
                self.line(format!("{dest} = icmp {pr} i{w} {a}, {b}"));
            }
            BinOp::And | BinOp::Or => unreachable!("verified: no And/Or in UIR"),
        }
    }

    fn cast(&mut self, d: Temp, src: Temp, to: &Ty) {
        let from = self.tty(src).clone();
        let v = self.op(src);
        let dest = format!("%t{}", d);
        match (&from, to) {
            (Ty::Int(a), Ty::Int(b)) => {
                let (wa, wb) = (a.bits(), b.bits());
                if wa == wb { self.repl.insert(d, v); }
                else if wb < wa { self.line(format!("{dest} = trunc i{wa} {v} to i{wb}")); }
                else { self.line(format!("{dest} = {} i{wa} {v} to i{wb}", if a.signed() { "sext" } else { "zext" })); }
            }
            (Ty::Int(a), Ty::Float) => self.line(format!("{dest} = {} i{} {v} to double", if a.signed() { "sitofp" } else { "uitofp" }, a.bits())),
            (Ty::Float, Ty::Int(b)) => {
                let w = b.bits();
                let name = format!("llvm.{}.sat.i{}.f64", if b.signed() { "fptosi" } else { "fptoui" }, w);
                self.g.decl(format!("declare i{w} @{name}(double)"));
                self.line(format!("{dest} = call i{w} @{name}(double {v})"));
            }
            (Ty::Bool, Ty::Int(b)) => self.line(format!("{dest} = zext i1 {v} to i{}", b.bits())),
            (a, b) if a == b => { self.repl.insert(d, v); }
            (a, b) => unreachable!("verified: cast {:?} -> {:?}", a, b),
        }
    }

    /// Bounds-check a simulated-memory address and return a pointer into `@kd_mem`.
    fn mem_addr(&mut self, t: Temp, span: Span) -> String {
        let k = self.int_of(t);
        let raw = self.op(t);
        let v = self.to_i64(&raw, k);
        let c = self.aux();
        self.line(format!("{c} = icmp uge i64 {v}, {}", MEM_SIZE));
        self.g.decl("declare void @kd_mem_oob(i32, i32, i64, i32, i64) noreturn");
        let call = format!("call void @kd_mem_oob(i32 {}, i32 {}, i64 {}, i32 {}, i64 {})", span.line, span.col, v, if k.signed() { 0 } else { 1 }, MEM_SIZE);
        self.cond_fail(&c, call);
        let p = self.aux();
        self.line(format!("{p} = getelementptr [{} x i8], ptr @kd_mem, i64 0, i64 {v}", MEM_SIZE));
        p
    }

    fn print(&mut self, t: Temp) {
        let v = self.op(t);
        match self.tty(t).clone() {
            Ty::Int(k) => {
                let x = self.to_i64(&v, k);
                let name = if k.signed() { "kd_print_i64" } else { "kd_print_u64" };
                self.g.decl(format!("declare void @{}(i64)", name));
                self.line(format!("call void @{}(i64 {})", name, x));
            }
            Ty::Float => { self.g.decl("declare void @kd_print_f64(double)"); self.line(format!("call void @kd_print_f64(double {})", v)); }
            Ty::Bool => {
                let x = self.aux();
                self.line(format!("{x} = zext i1 {v} to i32"));
                self.g.decl("declare void @kd_print_bool(i32)");
                self.line(format!("call void @kd_print_bool(i32 {x})"));
            }
            Ty::Ref(..) => { self.g.decl("declare void @kd_print_string(ptr)"); self.line(format!("call void @kd_print_string(ptr {})", v)); }
            Ty::Str => {
                let (p, n) = (self.aux(), self.aux());
                self.line(format!("{p} = extractvalue {{ ptr, i64 }} {v}, 0"));
                self.line(format!("{n} = extractvalue {{ ptr, i64 }} {v}, 1"));
                self.g.decl("declare void @kd_print_str(ptr, i64)");
                self.line(format!("call void @kd_print_str(ptr {p}, i64 {n})"));
            }
            o => unreachable!("verified: print of {:?}", o),
        }
    }

    fn call(&mut self, ins: &UInstr, id: usize, args: &[Temp]) {
        let prog = self.p;
        let callee = &prog.fns[id];
        if callee.ext == crate::ast::Ext::Import {
            let ps: Vec<String> = callee.slots[..callee.nparams].iter().zip(args.iter())
                .map(|(t, a)| format!("{}{} {}", vty(t), cabi_attr(t), self.op(*a))).collect();
            let decl_ps: Vec<String> = callee.slots[..callee.nparams].iter().map(|t| format!("{}{}", vty(t), cabi_attr(t))).collect();
            self.g.decl(format!("declare{} {} @{}({})", cabi_attr(&callee.ret), cabi_ret(&callee.ret), callee.name, decl_ps.join(", ")));
            let call = format!("call{} {} @{}({})", cabi_attr(&callee.ret), cabi_ret(&callee.ret), callee.name, ps.join(", "));
            match (ins.dest, &callee.ret) {
                (Some(d), Ty::Unit) => { self.line(call); self.repl.insert(d, "0".into()); }
                (Some(d), _) => self.line(format!("%t{} = {}", d, call)),
                (None, _) => self.line(call),
            }
            return;
        }
        let mut parts: Vec<String> = Vec::new();
        let sret = is_agg(&callee.ret);
        let dest = ins.dest.map(|d| format!("%t{}", d));
        if sret {
            let d = ins.dest.expect("verified: aggregate call has a destination");
            self.hoist(&format!("%t{}", d), &callee.ret.clone());
            parts.push(format!("ptr %t{}", d));
        }
        for a in args.iter() {
            parts.push(format!("{} {}", self.vt(*a), self.op(*a)));
        }
        // Reproduce the interpreters' call-depth rule exactly (depth counts active frames, `main` is depth 1).
        let d = self.aux();
        self.line(format!("{d} = load i64, ptr @kd_depth"));
        let c = self.aux();
        self.line(format!("{c} = icmp uge i64 {d}, {}", MAX_DEPTH));
        let fc = self.fail_call(ins.span, &format!("stack overflow: call depth exceeded {}", MAX_DEPTH));
        self.cond_fail(&c, fc);
        let d1 = self.aux();
        self.line(format!("{d1} = add i64 {d}, 1"));
        self.line(format!("store i64 {d1}, ptr @kd_depth"));
        let rty = if sret { "void".to_string() } else { vty(&callee.ret) };
        let call = format!("call {} @kd_f{}({})", rty, id, parts.join(", "));
        match (&dest, sret) {
            (Some(x), false) => self.line(format!("{x} = {call}")),
            _ => self.line(call),
        }
        self.line(format!("store i64 {d}, ptr @kd_depth"));
    }

    fn instr(&mut self, ins: &UInstr) {
        // An instruction that consumes a `!`-typed value can only run after control has diverged: it is dead code.
        if used_temps(&ins.op).iter().any(|t| matches!(self.tty(*t), Ty::Never)) {
            if let Some(d) = ins.dest { self.repl.insert(d, "undef".into()); }
            return;
        }
        let span = ins.span;
        let dty: Option<Ty> = ins.dest.map(|d| self.f.temps[d].clone());
        if let (Some(d), Some(Ty::Never)) = (ins.dest, &dty) {
            if !matches!(ins.op, UOp::Call(..)) { self.repl.insert(d, "undef".into()); return; }
        }
        match &ins.op {
            UOp::Const(v) => {
                let d = ins.dest.expect("verified: const has dest");
                let ty = dty.unwrap();
                match (v, &ty) {
                    (Value::Str(s), _) => { let l = self.str_lit(s); self.repl.insert(d, l); }
                    (Value::Struct(_) | Value::Enum(..) | Value::Array(_), _) => {
                        self.hoist(&format!("%t{}", d), &ty);
                        self.store_value(&format!("%t{}", d), &ty, v);
                    }
                    _ => { let l = self.scalar_lit(v, &ty); self.repl.insert(d, l); }
                }
            }
            UOp::Load(s) => {
                let d = ins.dest.unwrap();
                let ty = self.f.slots[*s].clone();
                if is_agg(&ty) { self.hoist(&format!("%t{}", d), &ty); self.memcpy(&format!("%t{}", d), &format!("%s{}", s), &ty); }
                else { self.line(format!("%t{} = load {}, ptr %s{}", d, vty(&ty), s)); }
            }
            UOp::Store(s, t) => self.store_temp(&format!("%s{}", s), *t),
            UOp::LoadProj(s, path) => {
                let d = ins.dest.unwrap();
                let (ptr, ty) = self.walk(format!("%s{}", s), self.f.slots[*s].clone(), path);
                if is_agg(&ty) { self.hoist(&format!("%t{}", d), &ty); self.memcpy(&format!("%t{}", d), &ptr, &ty); }
                else { self.line(format!("%t{} = load {}, ptr {}", d, vty(&ty), ptr)); }
            }
            UOp::Take(s) => {
                let d = ins.dest.unwrap();
                let st = self.f.slots[*s].clone();
                if is_agg(&st) {
                    // move an owned aggregate: copy it out, then zero the source so its drop glue sees only nulls
                    self.hoist(&format!("%t{}", d), &st);
                    self.memcpy(&format!("%t{}", d), &format!("%s{}", s), &st);
                    self.g.decl("declare void @llvm.memset.p0.i64(ptr, i8, i64, i1)");
                    self.line(format!("call void @llvm.memset.p0.i64(ptr %s{}, i8 0, i64 {}, i1 false)", s, sizeof(&st)));
                } else {
                    self.line(format!("%t{} = load ptr, ptr %s{}", d, s));
                    self.line(format!("store ptr null, ptr %s{}", s));
                }
            }
            UOp::TakePayload(s, v, j) => {
                let d = ins.dest.unwrap();
                let id = match &self.f.slots[*s] { Ty::Enum(id) => *id, o => unreachable!("verified: takepayload of {:?}", o) };
                let base = variant_base(&self.p.enums[id], *v as usize);
                let ft = self.p.enums[id].variants[*v as usize].1[*j].clone();
                let q = self.aux();
                self.line(format!("{} = getelementptr %E{}, ptr %s{}, i32 0, i32 {}", q, id, s, base + j));
                if is_agg(&ft) {
                    self.hoist(&format!("%t{}", d), &ft);
                    self.memcpy(&format!("%t{}", d), &q, &ft);
                    self.g.decl("declare void @llvm.memset.p0.i64(ptr, i8, i64, i1)");
                    self.line(format!("call void @llvm.memset.p0.i64(ptr {}, i8 0, i64 {}, i1 false)", q, sizeof(&ft)));
                } else {
                    self.line(format!("%t{} = load ptr, ptr {}", d, q));
                    self.line(format!("store ptr null, ptr {}", q));
                }
            }
            UOp::Drop(s, path) => {
                let (ptr, dt) = self.walk(format!("%s{}", s), self.f.slots[*s].clone(), path);
                if let Ty::Struct(i) = dt {
                    self.line(format!("call void @kd_drop_S{i}(ptr {ptr})"));
                } else if let Ty::Enum(i) = dt {
                    self.line(format!("call void @kd_drop_E{i}(ptr {ptr})"));
                } else if let Ty::Box(inner) = &dt {
                    let k = self.g.box_id(inner);
                    self.line(format!("call void @kd_drop_B{k}(ptr {ptr})"));
                } else {
                    let v = self.aux();
                    self.line(format!("{v} = load ptr, ptr {ptr}"));
                    let f = if matches!(dt, Ty::Vec(_)) { "kd_vec_drop" } else { "kd_string_drop" };
                    self.g.decl(&format!("declare void @{f}(ptr)"));
                    self.line(format!("call void @{f}(ptr {v})"));
                    self.line(format!("store ptr null, ptr {ptr}"));
                }
            }
            UOp::AddrOf(s, path) => {
                let d = ins.dest.unwrap();
                let (ptr, _) = self.walk(format!("%s{}", s), self.f.slots[*s].clone(), path);
                self.repl.insert(d, ptr);
            }
            UOp::StoreProj(s, path, t) => {
                let (ptr, _) = self.walk(format!("%s{}", s), self.f.slots[*s].clone(), path);
                self.store_temp(&ptr, *t);
            }
            UOp::Unary(op, t) => {
                let d = format!("%t{}", ins.dest.unwrap());
                let v = self.op(*t);
                match (op, self.tty(*t).clone()) {
                    (UnOp::Neg, Ty::Int(k)) => self.checked("sub", "negation", k, "0", &v, &d, span),
                    (UnOp::Neg, Ty::Float) => self.line(format!("{d} = fneg double {v}")),
                    (UnOp::Not, Ty::Bool) => self.line(format!("{d} = xor i1 {v}, true")),
                    (o, t) => unreachable!("verified: unary {:?} on {:?}", o, t),
                }
            }
            UOp::Binary(op, a, b) => {
                let d = format!("%t{}", ins.dest.unwrap());
                let (av, bv) = (self.op(*a), self.op(*b));
                match self.tty(*a).clone() {
                    Ty::Int(k) => self.int_binary(*op, k, &av, &bv, *b, &d, span),
                    Ty::Float => {
                        let (ins_name, is_cmp) = match op {
                            BinOp::Add => ("fadd", false), BinOp::Sub => ("fsub", false), BinOp::Mul => ("fmul", false),
                            BinOp::Div => ("fdiv", false), BinOp::Rem => ("frem", false),
                            BinOp::Eq => ("oeq", true), BinOp::Ne => ("une", true), BinOp::Lt => ("olt", true),
                            BinOp::Le => ("ole", true), BinOp::Gt => ("ogt", true), BinOp::Ge => ("oge", true),
                            o => unreachable!("verified: float op {:?}", o),
                        };
                        if is_cmp { self.line(format!("{d} = fcmp {ins_name} double {av}, {bv}")); }
                        else { self.line(format!("{d} = {ins_name} double {av}, {bv}")); }
                    }
                    Ty::Bool => {
                        let pr = match op { BinOp::Eq => "eq", BinOp::Ne => "ne", o => unreachable!("verified: bool op {:?}", o) };
                        self.line(format!("{d} = icmp {pr} i1 {av}, {bv}"));
                    }
                    Ty::Str => {
                        let (p1, n1, p2, n2, r) = (self.aux(), self.aux(), self.aux(), self.aux(), self.aux());
                        self.line(format!("{p1} = extractvalue {{ ptr, i64 }} {av}, 0"));
                        self.line(format!("{n1} = extractvalue {{ ptr, i64 }} {av}, 1"));
                        self.line(format!("{p2} = extractvalue {{ ptr, i64 }} {bv}, 0"));
                        self.line(format!("{n2} = extractvalue {{ ptr, i64 }} {bv}, 1"));
                        self.g.decl("declare i32 @kd_str_eq(ptr, i64, ptr, i64)");
                        self.line(format!("{r} = call i32 @kd_str_eq(ptr {p1}, i64 {n1}, ptr {p2}, i64 {n2})"));
                        match op {
                            BinOp::Eq => self.line(format!("{d} = icmp ne i32 {r}, 0")),
                            BinOp::Ne => self.line(format!("{d} = icmp eq i32 {r}, 0")),
                            o => unreachable!("verified/scanned: str op {:?}", o),
                        }
                    }
                    o => unreachable!("verified: binary on {:?}", o),
                }
            }
            UOp::Cast(t) => { let d = ins.dest.unwrap(); self.cast(d, *t, &dty.unwrap()); }
            UOp::Call(id, args) => self.call(ins, *id, args),
            UOp::Builtin(b, args) => match b {
                Builtin::Print => self.print(args[0]),
                Builtin::Len => {
                    let n = match self.tty(args[0]) { Ty::Array(_, n) => *n, o => unreachable!("verified: len of {:?}", o) };
                    self.repl.insert(ins.dest.unwrap(), n.to_string());
                }
                Builtin::StringFrom => {
                    let d = ins.dest.unwrap();
                    let v = self.op(args[0]);
                    let (p, n) = (self.aux(), self.aux());
                    self.line(format!("{p} = extractvalue {{ ptr, i64 }} {v}, 0"));
                    self.line(format!("{n} = extractvalue {{ ptr, i64 }} {v}, 1"));
                    self.g.decl("declare ptr @kd_string_from(i32, i32, ptr, i64)");
                    self.line(format!("%t{d} = call ptr @kd_string_from(i32 {}, i32 {}, ptr {p}, i64 {n})", span.line, span.col));
                }
                Builtin::StringConcat => {
                    let d = ins.dest.unwrap();
                    let (a, b) = (self.op(args[0]), self.op(args[1]));
                    self.g.decl("declare ptr @kd_string_concat(i32, i32, ptr, ptr)");
                    self.line(format!("%t{d} = call ptr @kd_string_concat(i32 {}, i32 {}, ptr {a}, ptr {b})", span.line, span.col));
                }
                Builtin::StringPush => {
                    let a = self.op(args[0]);
                    let v = self.op(args[1]);
                    let (p, n) = (self.aux(), self.aux());
                    self.line(format!("{p} = extractvalue {{ ptr, i64 }} {v}, 0"));
                    self.line(format!("{n} = extractvalue {{ ptr, i64 }} {v}, 1"));
                    self.g.decl("declare void @kd_string_push(i32, i32, ptr, ptr, i64)");
                    self.line(format!("call void @kd_string_push(i32 {}, i32 {}, ptr {a}, ptr {p}, i64 {n})", span.line, span.col));
                }
                Builtin::StringLen => {
                    let d = ins.dest.unwrap();
                    let a = self.op(args[0]);
                    self.g.decl("declare i64 @kd_string_len(ptr)");
                    self.line(format!("%t{d} = call i64 @kd_string_len(ptr {a})"));
                }
                Builtin::StringClone => {
                    let d = ins.dest.unwrap();
                    let a = self.op(args[0]);
                    self.g.decl("declare ptr @kd_string_clone(i32, i32, ptr)");
                    self.line(format!("%t{d} = call ptr @kd_string_clone(i32 {}, i32 {}, ptr {a})", span.line, span.col));
                }
                Builtin::StringEq => {
                    let d = ins.dest.unwrap();
                    let (a, b) = (self.op(args[0]), self.op(args[1]));
                    let r = self.aux();
                    self.g.decl("declare i32 @kd_string_eq(ptr, ptr)");
                    self.line(format!("{r} = call i32 @kd_string_eq(ptr {a}, ptr {b})"));
                    self.line(format!("%t{d} = icmp ne i32 {r}, 0"));
                }
                Builtin::VecNew => {
                    let d = ins.dest.unwrap();
                    let e = match dty.as_ref().unwrap() { Ty::Vec(e) => (**e).clone(), o => unreachable!("verified: vec_new of {:?}", o) };
                    self.g.decl("declare ptr @kd_vec_new(i32, i32, i64)");
                    self.line(format!("%t{d} = call ptr @kd_vec_new(i32 {}, i32 {}, i64 {})", span.line, span.col, sizeof(&e)));
                }
                Builtin::VecPush => {
                    let a = self.op(args[0]);
                    let slot = self.aux();
                    self.g.decl("declare ptr @kd_vec_push(i32, i32, ptr)");
                    self.line(format!("{slot} = call ptr @kd_vec_push(i32 {}, i32 {}, ptr {a})", span.line, span.col));
                    self.store_temp(&slot, args[1]);
                }
                Builtin::VecLen => {
                    let d = ins.dest.unwrap();
                    let a = self.op(args[0]);
                    self.g.decl("declare i64 @kd_vec_len(ptr)");
                    self.line(format!("%t{d} = call i64 @kd_vec_len(ptr {a})"));
                }
                Builtin::VecGet | Builtin::VecSet => {
                    let a = self.op(args[0]);
                    let k = self.int_of(args[1]);
                    let raw = self.op(args[1]);
                    let i = self.to_i64(&raw, k);
                    let slot = self.aux();
                    self.g.decl("declare ptr @kd_vec_at(i32, i32, ptr, i64, i32)");
                    self.line(format!("{slot} = call ptr @kd_vec_at(i32 {}, i32 {}, ptr {a}, i64 {i}, i32 {})", span.line, span.col, if k.signed() { 0 } else { 1 }));
                    if *b == Builtin::VecGet {
                        let d = ins.dest.unwrap();
                        self.line(format!("%t{d} = load {}, ptr {slot}", vty(&dty.unwrap())));
                    } else {
                        self.store_temp(&slot, args[2]);
                    }
                }
                Builtin::VecPop => {
                    let d = ins.dest.unwrap();
                    let a = self.op(args[0]);
                    let slot = self.aux();
                    self.g.decl("declare ptr @kd_vec_pop(i32, i32, ptr)");
                    self.line(format!("{slot} = call ptr @kd_vec_pop(i32 {}, i32 {}, ptr {a})", span.line, span.col));
                    self.line(format!("%t{d} = load {}, ptr {slot}", vty(&dty.unwrap())));
                }
                Builtin::VecClone => {
                    let d = ins.dest.unwrap();
                    let a = self.op(args[0]);
                    self.g.decl("declare ptr @kd_vec_clone(i32, i32, ptr)");
                    self.line(format!("%t{d} = call ptr @kd_vec_clone(i32 {}, i32 {}, ptr {a})", span.line, span.col));
                }
                Builtin::BoxNew => {
                    let d = ins.dest.unwrap();
                    let inner = match dty.as_ref().unwrap() { Ty::Box(e) => (**e).clone(), o => unreachable!("verified: box_new of {:?}", o) };
                    self.g.decl("declare ptr @kd_box_new(i32, i32, i64)");
                    self.line(format!("%t{d} = call ptr @kd_box_new(i32 {}, i32 {}, i64 {})", span.line, span.col, sizeof(&inner)));
                    self.store_temp(&format!("%t{d}"), args[0]);
                }
                Builtin::BoxInto | Builtin::BoxGet => {
                    let d = ins.dest.unwrap();
                    let ty = dty.clone().unwrap();
                    let a = self.op(args[0]);
                    let cell = if *b == Builtin::BoxInto { a.clone() } else { let q = self.aux(); self.line(format!("{q} = load ptr, ptr {a}")); q };
                    if is_agg(&ty) { self.hoist(&format!("%t{d}"), &ty); self.memcpy(&format!("%t{d}"), &cell, &ty); }
                    else { self.line(format!("%t{d} = load {}, ptr {cell}", vty(&ty))); }
                    if *b == Builtin::BoxInto { self.g.decl("declare void @kd_box_free(ptr)"); self.line(format!("call void @kd_box_free(ptr {cell})")); }
                }
                Builtin::BoxSet => {
                    let a = self.op(args[0]);
                    let q = self.aux();
                    self.line(format!("{q} = load ptr, ptr {a}"));
                    self.store_temp(&q, args[1]);
                }
                Builtin::Peek => {
                    let d = ins.dest.unwrap();
                    let ptr = self.mem_addr(args[0], span);
                    let b = self.aux();
                    self.line(format!("{b} = load i8, ptr {ptr}"));
                    let dt = vty(&dty.unwrap());
                    let w = dt.trim_start_matches('i').parse::<u32>().unwrap_or(64);
                    if w == 8 { self.repl.insert(d, b); } else { self.line(format!("%t{d} = zext i8 {b} to {dt}")); }
                }
                Builtin::Poke => {
                    let ptr = self.mem_addr(args[0], span);
                    let k = self.int_of(args[1]);
                    let raw = self.op(args[1]);
                    let v = self.to_i64(&raw, k);
                    let c = self.aux();
                    self.line(format!("{c} = icmp ugt i64 {v}, 255"));
                    self.g.decl("declare void @kd_poke_fail(i32, i32, i64, i32) noreturn");
                    let call = format!("call void @kd_poke_fail(i32 {}, i32 {}, i64 {}, i32 {})", span.line, span.col, v, if k.signed() { 0 } else { 1 });
                    self.cond_fail(&c, call);
                    let b = self.aux();
                    self.line(format!("{b} = trunc i64 {v} to i8"));
                    self.line(format!("store i8 {b}, ptr {ptr}"));
                }
            },
            UOp::MakeStruct(id, fs) => {
                let d = ins.dest.unwrap();
                self.hoist(&format!("%t{}", d), &Ty::Struct(*id));
                for (i, t) in fs {
                    let q = self.aux();
                    self.line(format!("{} = getelementptr %S{}, ptr %t{}, i32 0, i32 {}", q, id, d, i));
                    self.store_temp(&q, *t);
                }
            }
            UOp::Field(t, i) => {
                let d = ins.dest.unwrap();
                let id = match self.tty(*t) { Ty::Struct(id) => *id, o => unreachable!("verified: field of {:?}", o) };
                let q = self.aux();
                let base = self.op(*t);
                self.line(format!("{} = getelementptr %S{}, ptr {}, i32 0, i32 {}", q, id, base, i));
                let ft = self.p.structs[id].fields[*i].1.clone();
                self.read_borrowed(d, q, &ft);
            }
            UOp::Index(a, i, sp) => {
                let d = ins.dest.unwrap();
                let (aty, n) = match self.tty(*a).clone() { Ty::Array(e, n) => (Ty::Array(e, n), n), o => unreachable!("verified: index of {:?}", o) };
                let idx = self.bounds(*i, n, *sp);
                let q = self.aux();
                let base = self.op(*a);
                self.line(format!("{} = getelementptr {}, ptr {}, i64 0, i64 {}", q, mty(&aty), base, idx));
                let et = match aty { Ty::Array(e, _) => *e, _ => unreachable!() };
                self.read_borrowed(d, q, &et);
            }
            UOp::MakeArray(ts) => {
                let d = ins.dest.unwrap();
                let ty = dty.unwrap();
                self.hoist(&format!("%t{}", d), &ty);
                for (i, t) in ts.iter().enumerate() {
                    let q = self.aux();
                    self.line(format!("{} = getelementptr {}, ptr %t{}, i64 0, i64 {}", q, mty(&ty), d, i));
                    self.store_temp(&q, *t);
                }
            }
            UOp::Repeat(t, n) => {
                let d = ins.dest.unwrap();
                let ty = dty.unwrap();
                self.hoist(&format!("%t{}", d), &ty);
                if *n > 0 {
                    self.n += 1;
                    let (hd, bd, dn) = (format!("rh{}", self.n), format!("rb{}", self.n), format!("rd{}", self.n));
                    let ctr = format!("%c{}", self.n);
                    let _ = writeln!(self.allocas, "  {} = alloca i64", ctr);
                    self.line(format!("store i64 0, ptr {}", ctr));
                    self.line(format!("br label %{}", hd));
                    self.label(&hd);
                    let (i, c) = (self.aux(), self.aux());
                    self.line(format!("{i} = load i64, ptr {ctr}"));
                    self.line(format!("{c} = icmp ult i64 {i}, {n}"));
                    self.line(format!("br i1 {c}, label %{bd}, label %{dn}"));
                    self.label(&bd);
                    let q = self.aux();
                    self.line(format!("{} = getelementptr {}, ptr %t{}, i64 0, i64 {}", q, mty(&ty), d, i));
                    self.store_temp(&q, *t);
                    let i1 = self.aux();
                    self.line(format!("{i1} = add i64 {i}, 1"));
                    self.line(format!("store i64 {i1}, ptr {ctr}"));
                    self.line(format!("br label %{}", hd));
                    self.label(&dn);
                }
            }
            UOp::MakeVariant(v, ts) => {
                let d = ins.dest.unwrap();
                let id = match dty.unwrap() { Ty::Enum(id) => id, o => unreachable!("verified: variant of {:?}", o) };
                self.hoist(&format!("%t{}", d), &Ty::Enum(id));
                let base = variant_base(&self.p.enums[id], *v as usize);
                let tg = self.aux();
                self.line(format!("{} = getelementptr %E{}, ptr %t{}, i32 0, i32 0", tg, id, d));
                self.line(format!("store i32 {}, ptr {}", v, tg));
                for (j, t) in ts.iter().enumerate() {
                    let q = self.aux();
                    self.line(format!("{} = getelementptr %E{}, ptr %t{}, i32 0, i32 {}", q, id, d, base + j));
                    self.store_temp(&q, *t);
                }
            }
            UOp::IsVariant(t, v) => {
                let d = ins.dest.unwrap();
                let id = match self.tty(*t) { Ty::Enum(id) => *id, o => unreachable!("verified: isvariant of {:?}", o) };
                let (q, x) = (self.aux(), self.aux());
                let base = self.op(*t);
                self.line(format!("{} = getelementptr %E{}, ptr {}, i32 0, i32 0", q, id, base));
                self.line(format!("{x} = load i32, ptr {q}"));
                self.line(format!("%t{} = icmp eq i32 {}, {}", d, x, v));
            }
            UOp::Payload(t, v, j) => {
                let d = ins.dest.unwrap();
                let id = match self.tty(*t) { Ty::Enum(id) => *id, o => unreachable!("verified: payload of {:?}", o) };
                let base = variant_base(&self.p.enums[id], *v as usize);
                let ft = self.p.enums[id].variants[*v as usize].1[*j].clone();
                let q = self.aux();
                let b = self.op(*t);
                self.line(format!("{} = getelementptr %E{}, ptr {}, i32 0, i32 {}", q, id, b, base + j));
                self.read_borrowed(d, q, &ft);
            }
        }
    }

    fn term(&mut self, t: &UTerm) {
        match t {
            UTerm::Br(b) => self.line(format!("br label %b{}", b)),
            UTerm::CondBr(c, x, y) => {
                if matches!(self.tty(*c), Ty::Never) { self.line("unreachable"); }
                else { let v = self.op(*c); self.line(format!("br i1 {}, label %b{}, label %b{}", v, x, y)); }
            }
            UTerm::Ret(t) => {
                if matches!(self.tty(*t), Ty::Never) { self.line("unreachable"); return; }
                if is_agg(&self.f.ret) {
                    let v = self.op(*t);
                    let ty = self.f.ret.clone();
                    self.memcpy("%out", &v, &ty);
                    self.line("ret void");
                } else {
                    let v = self.op(*t);
                    self.line(format!("ret {} {}", vty(&self.f.ret), v));
                }
            }
            UTerm::Trap(m) => {
                let c = self.fail_call(Span::default(), &format!("internal error: reached trap: {}", m));
                self.line(c);
                self.line("unreachable");
            }
        }
    }
}

fn emit_fn(p: &UProgram, fi: usize, g: &mut Globals) -> String {
    let f = &p.fns[fi];
    let mut fx = Fx { p, f, g, body: String::new(), allocas: String::new(), n: 0, repl: HashMap::new() };
    let sret = is_agg(&f.ret);
    let mut params: Vec<String> = Vec::new();
    if sret { params.push("ptr %out".into()); }
    for i in 0..f.nparams { params.push(format!("{} %a{}", vty(&f.slots[i]), i)); }
    let rty = if sret { "void".to_string() } else { vty(&f.ret) };
    for (i, t) in f.slots.iter().enumerate() { fx.hoist(&format!("%s{}", i), t); }
    let mut pre = String::new();
    for (i, t) in f.slots.iter().enumerate().skip(f.nparams) {
        if matches!(t, Ty::String | Ty::Vec(_) | Ty::Box(_) | Ty::Ref(..)) { let _ = writeln!(pre, "  store ptr null, ptr %s{}", i); }
    }
    for i in 0..f.nparams {
        let t = &f.slots[i];
        if is_agg(t) {
            let _ = writeln!(pre, "  call void @llvm.memcpy.p0.p0.i64(ptr %s{i}, ptr %a{i}, i64 {}, i1 false)", sizeof(t));
            fx.g.decl("declare void @llvm.memcpy.p0.p0.i64(ptr, ptr, i64, i1)");
        } else {
            let _ = writeln!(pre, "  store {} %a{i}, ptr %s{i}", vty(t));
        }
    }
    for (bi, b) in f.blocks.iter().enumerate() {
        fx.label(&format!("b{}", bi));
        for ins in &b.instrs { fx.instr(ins); }
        fx.term(&b.term);
    }
    let mut o = String::new();
    let _ = writeln!(o, "; {}  (layer {})", f.name, f.layer.name());
    let _ = writeln!(o, "define {} @kd_f{}({}) {{\nentry:", rty, fi, params.join(", "));
    o.push_str(&fx.allocas);
    o.push_str(&pre);
    o.push_str("  br label %b0\n");
    o.push_str(&fx.body);
    o.push_str("}\n\n");
    o
}

/// The unmangled C-ABI entry point of an `export fn`: `T name(args)` forwarding to the internal `@kd_f<i>`.
fn emit_export_wrapper(p: &UProgram, fi: usize) -> String {
    let f = &p.fns[fi];
    let ps: Vec<String> = (0..f.nparams).map(|i| format!("{}{} %a{}", vty(&f.slots[i]), cabi_attr(&f.slots[i]), i)).collect();
    let cs: Vec<String> = (0..f.nparams).map(|i| format!("{} %a{}", vty(&f.slots[i]), i)).collect();
    let mut o = String::new();
    let _ = writeln!(o, "; C-ABI export of {}", f.name);
    let _ = writeln!(o, "define{} {} @{}({}) {{\nentry:", cabi_attr(&f.ret), cabi_ret(&f.ret), f.name, ps.join(", "));
    if f.ret == Ty::Unit {
        let _ = writeln!(o, "  call i8 @kd_f{}({})\n  ret void", fi, cs.join(", "));
    } else {
        let _ = writeln!(o, "  %r = call {} @kd_f{}({})\n  ret {} %r", vty(&f.ret), fi, cs.join(", "), vty(&f.ret));
    }
    let _ = writeln!(o, "}}\n");
    o
}

/// Translate a verified UIR program to LLVM IR text for target T1. `src_path` is the name printed in runtime errors.
/// Drop glue for every struct that owns heap memory: `@kd_drop_S<i>(ptr)` frees each owned field and nulls it, so
/// running it twice (or on a moved-from, zeroed aggregate) is harmless.
fn emit_drop_glue(p: &UProgram, g: &mut Globals) -> String {
    let owned = |t: &Ty| crate::hir::owned_ty(t, &p.structs, &p.enums);
    // drop the owned value of type `ft` stored at `ptr` (a name valid in the current function); `u` makes temporaries unique
    fn drop_at(o: &mut String, g: &mut Globals, ft: &Ty, ptr: &str, u: &str) {
        match ft {
            Ty::String | Ty::Vec(_) => {
                let f = if matches!(ft, Ty::Vec(_)) { "kd_vec_drop" } else { "kd_string_drop" };
                g.decl(format!("declare void @{f}(ptr)"));
                let _ = writeln!(o, "  %v{u} = load ptr, ptr {ptr}\n  call void @{f}(ptr %v{u})\n  store ptr null, ptr {ptr}");
            }
            Ty::Struct(k) => { let _ = writeln!(o, "  call void @kd_drop_S{k}(ptr {ptr})"); }
            Ty::Enum(k) => { let _ = writeln!(o, "  call void @kd_drop_E{k}(ptr {ptr})"); }
            Ty::Box(inner) => { let k = g.box_id(inner); let _ = writeln!(o, "  call void @kd_drop_B{k}(ptr {ptr})"); }
            other => unreachable!("owned field of type {:?} has no drop glue yet", other),
        }
    }
    let mut o = String::new();
    for (i, s) in p.structs.iter().enumerate() {
        if !owned(&Ty::Struct(i)) { continue; }
        let _ = writeln!(o, "define internal void @kd_drop_S{i}(ptr %p) {{\nentry:");
        for (j, (_, ft)) in s.fields.iter().enumerate() {
            if !owned(ft) { continue; }
            let _ = writeln!(o, "  %f{j} = getelementptr %S{i}, ptr %p, i32 0, i32 {j}");
            drop_at(&mut o, g, ft, &format!("%f{j}"), &j.to_string());
        }
        let _ = writeln!(o, "  ret void\n}}\n");
    }
    // Enums: dispatch on the tag (payload slots of inactive variants are uninitialised). A zeroed, moved-from enum has
    // tag 0 and null owned payloads, which the variant-0 arm frees as a no-op.
    for (i, e) in p.enums.iter().enumerate() {
        if !owned(&Ty::Enum(i)) { continue; }
        let _ = writeln!(o, "define internal void @kd_drop_E{i}(ptr %p) {{\nentry:\n  %tp = getelementptr %E{i}, ptr %p, i32 0, i32 0\n  %tag = load i32, ptr %tp");
        let owning: Vec<usize> = (0..e.variants.len()).filter(|v| e.variants[*v].1.iter().any(|t| owned(t))).collect();
        let cases: Vec<String> = owning.iter().map(|v| format!("i32 {v}, label %v{v}")).collect();
        let _ = writeln!(o, "  switch i32 %tag, label %done [{}]", cases.join(" "));
        for v in owning {
            let base = variant_base(e, v);
            let _ = writeln!(o, "v{v}:");
            for (j, ft) in e.variants[v].1.iter().enumerate() {
                if !owned(ft) { continue; }
                let _ = writeln!(o, "  %f{v}_{j} = getelementptr %E{i}, ptr %p, i32 0, i32 {}", base + j);
                drop_at(&mut o, g, ft, &format!("%f{v}_{j}"), &format!("{v}_{j}"));
            }
            let _ = writeln!(o, "  br label %done");
        }
        let _ = writeln!(o, "done:\n  ret void\n}}\n");
    }
    // Boxes: free the contents (if they own anything), then the cell. The list can grow while we emit (a box inside a box).
    let mut k = 0;
    while k < g.boxes.len() {
        let inner = g.boxes[k].clone();
        let _ = writeln!(o, "define internal void @kd_drop_B{k}(ptr %slot) {{\nentry:\n  %p = load ptr, ptr %slot\n  %n = icmp eq ptr %p, null\n  br i1 %n, label %done, label %go\ngo:");
        if owned(&inner) { drop_at(&mut o, g, &inner, "%p", "b"); }
        g.decl("declare void @kd_box_free(ptr)");
        let _ = writeln!(o, "  call void @kd_box_free(ptr %p)\n  store ptr null, ptr %slot\n  br label %done\ndone:\n  ret void\n}}\n");
        k += 1;
    }
    o
}

pub fn emit_llvm(p: &UProgram, src_path: &str) -> Result<String, Vec<Diag>> { emit_llvm_for(p, src_path, Target::X86Linux) }

/// Code generation targets: T1 = x86-64 Linux (libc runtime), T2 = wasm32 freestanding (host imports).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Target { X86Linux, Wasm32 }

pub fn emit_llvm_for(p: &UProgram, src_path: &str, target: Target) -> Result<String, Vec<Diag>> {
    let main = match p.main {
        Some(m) => m,
        None => return Err(vec![Diag::new(Span::default(), "no `main` function defined")]),
    };
    let fns = reachable(p, main);
    let mut ds = scan(p, &fns);
    if matches!(target, Target::Wasm32) {
        for &fi in &fns {
            let f = &p.fns[fi];
            if f.ext != crate::ast::Ext::None {
                ds.push(Diag::new(Span::default(), format!("`{} fn {}`: C interop is not supported on the wasm32 target in this version (see docs/INTEROP.md)", if f.ext == crate::ast::Ext::Import { "extern" } else { "export" }, f.name)));
            }
        }
    }
    let m = &p.fns[main];
    if m.nparams != 0 || m.ret != Ty::Unit {
        ds.push(Diag::new(Span::default(), "native backend requires `fn main()` with no parameters and no return value"));
    }
    if !ds.is_empty() {
        ds.sort_by_key(|d| (d.span.line, d.span.col));
        return Err(ds);
    }
    let mut g = Globals::default();
    let mut code = String::new();
    for &fi in &fns {
        match p.fns[fi].ext {
            crate::ast::Ext::Import => {}   // declared at its call sites
            crate::ast::Ext::Export => { code.push_str(&emit_fn(p, fi, &mut g)); code.push_str(&emit_export_wrapper(p, fi)); }
            crate::ast::Ext::None => code.push_str(&emit_fn(p, fi, &mut g)),
        }
    }

    code.push_str(&emit_drop_glue(p, &mut g));

    let mut o = String::new();
    match target {
        Target::X86Linux => o.push_str("; K.E.N.D.R.A.H. native backend output (target T1: x86-64 Linux)\ntarget triple = \"x86_64-pc-linux-gnu\"\n\n"),
        Target::Wasm32 => o.push_str("; K.E.N.D.R.A.H. backend output (target T2: wasm32 freestanding)\ntarget datalayout = \"e-m:e-p:32:32-p10:8:8-p20:8:8-i64:64-n32:64-S128-ni:1:10:20\"\ntarget triple = \"wasm32-unknown-unknown\"\n\n"),
    }
    for (i, s) in p.structs.iter().enumerate() {
        let fs: Vec<String> = s.fields.iter().map(|f| mty(&f.1)).collect();
        let _ = writeln!(o, "%S{} = type {{ {} }} ; struct {}", i, fs.join(", "), s.name);
    }
    for (i, e) in p.enums.iter().enumerate() {
        let mut fs = vec!["i32".to_string()];
        for v in &e.variants { for t in &v.1 { fs.push(mty(t)); } }
        let _ = writeln!(o, "%E{} = type {{ {} }} ; enum {}", i, fs.join(", "), e.name);
    }
    let _ = writeln!(o, "\n@kd_depth = internal global i64 1");
    let _ = writeln!(o, "@kd_mem = internal global [{} x i8] zeroinitializer", MEM_SIZE);
    let mut path = src_path.as_bytes().to_vec();
    path.push(0);
    let _ = writeln!(o, "@kd_src_path = constant [{} x i8] c\"{}\"", path.len(), llvm_bytes(&path));
    for (i, s) in g.strs.iter().enumerate() {
        let _ = writeln!(o, "@.s{} = private unnamed_addr constant [{} x i8] c\"{}\"", i, s.len(), llvm_bytes(s));
    }
    o.push('\n');
    for d in &g.decls { let _ = writeln!(o, "{}", d); }
    o.push('\n');
    o.push_str(&code);
    let _ = writeln!(o, "define i32 @kd_entry() {{\nentry:\n  call i8 @kd_f{}()\n  ret i32 0\n}}", main);
    Ok(o)
}

// ---------------------------------------------------------------- driver

#[derive(Debug, Clone)]
pub struct BuildOpts { pub out: PathBuf, pub opt_level: u8, pub link: Vec<String> }

fn scratch_dir() -> Result<PathBuf, String> {
    use std::sync::atomic::{AtomicUsize, Ordering};
    static N: AtomicUsize = AtomicUsize::new(0);
    let d = std::env::temp_dir().join(format!("kendrah-build-{}-{}", std::process::id(), N.fetch_add(1, Ordering::SeqCst)));
    std::fs::create_dir_all(&d).map_err(|e| format!("cannot create {}: {}", d.display(), e))?;
    Ok(d)
}

/// Compile LLVM IR text plus the C runtime into an executable with `clang`.
pub fn build_executable(ll: &str, opts: &BuildOpts) -> Result<(), String> {
    let dir = scratch_dir()?;
    let r = (|| {
        let ll_path = dir.join("prog.ll");
        let rt_path = dir.join("kd_rt.c");
        std::fs::write(&ll_path, ll).map_err(|e| e.to_string())?;
        std::fs::write(&rt_path, RUNTIME_C).map_err(|e| e.to_string())?;
        let clang = std::env::var("KENDRAH_CLANG").unwrap_or_else(|_| "clang".into());
        let out = std::process::Command::new(&clang)
            .arg(format!("-O{}", opts.opt_level.min(3)))
            .arg("-Wno-override-module")
            .arg(&ll_path).arg(&rt_path)
            .arg("-o").arg(&opts.out)
            .args(&opts.link)
            .args(["-pthread", "-lm"])
            .output()
            .map_err(|e| format!("cannot run `{}`: {} (install clang >= 15 or set KENDRAH_CLANG)", clang, e))?;
        if !out.status.success() {
            return Err(format!("clang failed (this is a compiler bug if the program passed `check`):\n{}", String::from_utf8_lossy(&out.stderr)));
        }
        Ok(())
    })();
    let _ = std::fs::remove_dir_all(&dir);
    r
}

/// Result of running a natively built program.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct NativeRun { pub stdout: String, pub stderr: String, pub code: i32 }

/// Build `src` natively into a scratch directory and run it (used by tests and benchmarks).
/// `path` is the file name that appears in runtime error messages.
pub fn run_native(src: &str, path: &str, opt_level: u8) -> Result<NativeRun, crate::RunError> {
    use crate::RunError;
    let u = crate::compile_uir(src)?;
    let ll = emit_llvm(&u, path).map_err(RunError::Compile)?;
    let dir = scratch_dir().map_err(RunError::Internal)?;
    let exe: &Path = &dir.join("prog");
    let res = build_executable(&ll, &BuildOpts { out: exe.to_path_buf(), opt_level, link: vec![] }).map_err(RunError::Internal).and_then(|_| {
        let o = std::process::Command::new(exe).output().map_err(|e| RunError::Internal(e.to_string()))?;
        Ok(NativeRun { stdout: String::from_utf8_lossy(&o.stdout).into_owned(), stderr: String::from_utf8_lossy(&o.stderr).into_owned(), code: o.status.code().unwrap_or(-1) })
    });
    let _ = std::fs::remove_dir_all(&dir);
    res
}

/// Run `src` on the UIR interpreter and natively; they must agree on stdout, exit status and the runtime error
/// message (including source location). Returns the agreed stdout, or the runtime error text.
pub fn run_native_differential(src: &str, opt_level: u8) -> Result<String, crate::RunError> {
    differential(src, opt_level, |s, p, o| run_native(s, p, o))
}

fn differential(src: &str, opt_level: u8, run: impl Fn(&str, &str, u8) -> Result<NativeRun, crate::RunError>) -> Result<String, crate::RunError> {
    use crate::RunError;
    let path = "t.kd";
    let h = crate::compile(src).map_err(RunError::Compile)?;
    let u = crate::lower_and_verify(&h)?;
    // The interpreter recurses natively per call, so it needs a big stack (as in the CLI).
    let (want_out, r) = std::thread::scope(|sc| {
        std::thread::Builder::new().stack_size(256 * 1024 * 1024).spawn_scoped(sc, || {
            let mut buf: Vec<u8> = Vec::new();
            let r = crate::uir_interp::run(&u, &mut buf, None);
            (String::from_utf8_lossy(&buf).into_owned(), r)
        }).unwrap().join().unwrap()
    });
    let n = run(src, path, opt_level)?;
    let (want_code, want_err) = match &r {
        Ok(()) => (0, String::new()),
        Err(e) => (2, format!("{}:{}:{}: runtime error: {}\n", path, e.span.line, e.span.col, e.message)),
    };
    if n.stdout != want_out || n.code != want_code || n.stderr != want_err {
        return Err(RunError::Internal(format!(
            "target/interpreter disagree\n interp: out={:?} code={} err={:?}\n target: out={:?} code={} err={:?}",
            want_out, want_code, want_err, n.stdout, n.code, n.stderr)));
    }
    match r { Ok(()) => Ok(want_out), Err(e) => Err(RunError::Runtime(e)) }
}

// ---------------------------------------------------------------- wasm32 target (T2)

pub const WASM_RUNTIME_C: &str = include_str!("../runtime/kd_rt_wasm.c");
pub const WASM_HOST_JS: &str = include_str!("../runtime/kd_wasm_host.js");

/// Compile LLVM IR (from `emit_llvm_for(.., Target::Wasm32)`) plus the freestanding runtime into a `.wasm` module.
pub fn build_wasm(ll: &str, out: &Path, opt_level: u8) -> Result<(), String> {
    let dir = scratch_dir()?;
    let r = (|| {
        let ll_path = dir.join("prog.ll");
        let rt_path = dir.join("kd_rt_wasm.c");
        std::fs::write(&ll_path, ll).map_err(|e| e.to_string())?;
        std::fs::write(&rt_path, WASM_RUNTIME_C).map_err(|e| e.to_string())?;
        let clang = std::env::var("KENDRAH_CLANG").unwrap_or_else(|_| "clang".into());
        let o = std::process::Command::new(&clang)
            .args(["--target=wasm32-unknown-unknown", "-nostdlib", "-mbulk-memory", "-fuse-ld=lld", "-Wno-override-module", "-ffreestanding"])
            .arg(format!("-O{}", opt_level.min(3)))
            .args(["-Wl,--no-entry", "-Wl,--export=kd_start", "-Wl,-z,stack-size=16777216", "-Wl,--initial-memory=33554432"])
            .arg(&ll_path).arg(&rt_path)
            .arg("-o").arg(out)
            .output()
            .map_err(|e| format!("cannot run `{}`: {} (install clang >= 15 with the wasm32 target and lld, or set KENDRAH_CLANG)", clang, e))?;
        if !o.status.success() {
            return Err(format!("clang (wasm32) failed (this is a compiler bug if the program passed `check`):\n{}", String::from_utf8_lossy(&o.stderr)));
        }
        Ok(())
    })();
    let _ = std::fs::remove_dir_all(&dir);
    r
}

/// Build `src` for wasm32 and execute it under Node.js with the host in `runtime/kd_wasm_host.js`.
pub fn run_wasm(src: &str, path: &str, opt_level: u8) -> Result<NativeRun, crate::RunError> {
    use crate::RunError;
    let u = crate::compile_uir(src)?;
    let ll = emit_llvm_for(&u, path, Target::Wasm32).map_err(RunError::Compile)?;
    let dir = scratch_dir().map_err(RunError::Internal)?;
    let wasm = dir.join("prog.wasm");
    let res = build_wasm(&ll, &wasm, opt_level).map_err(RunError::Internal).and_then(|_| {
        let host = dir.join("host.js");
        std::fs::write(&host, WASM_HOST_JS).map_err(|e| RunError::Internal(e.to_string()))?;
        let node = std::env::var("KENDRAH_NODE").unwrap_or_else(|_| "node".into());
        let o = std::process::Command::new(&node).arg(&host).arg(&wasm).output()
            .map_err(|e| RunError::Internal(format!("cannot run `{}`: {} (install Node.js >= 18 or set KENDRAH_NODE)", node, e)))?;
        Ok(NativeRun { stdout: String::from_utf8_lossy(&o.stdout).into_owned(), stderr: String::from_utf8_lossy(&o.stderr).into_owned(), code: o.status.code().unwrap_or(-1) })
    });
    let _ = std::fs::remove_dir_all(&dir);
    res
}

/// Like `run_native_differential` for the wasm32 target: the module run under Node must agree with the UIR
/// interpreter on stdout, exit status and runtime error text.
pub fn run_wasm_differential(src: &str, opt_level: u8) -> Result<String, crate::RunError> {
    differential(src, opt_level, |s, p, o| run_wasm(s, p, o))
}
