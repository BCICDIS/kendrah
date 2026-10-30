//! Typed, name-resolved high-level IR produced by the checker and consumed by the interpreter.
//!
//! Invariants (established by `check`, relied on by `interp`; a violation is a compiler bug):
//! * every `HExpr.ty` is fully resolved (no `Ty::Var`) except after errors, in which case no HIR is produced;
//! * variables are frame slots; each `let`/pattern binding/parameter owns a distinct slot (shadowing = new slot);
//! * operand types of binary operators are equal (except shifts, whose rhs may be any integer type);
//! * calls name functions by index and match their signature; `match` is exhaustive;
//! * `unsafe` blocks have been lowered to plain blocks (their legality was checked against `@layer`).

use crate::ast::{BinOp, Layer, UnOp};
use crate::diag::Span;
use crate::ty::Ty;

#[derive(Debug, Clone, PartialEq)]
pub enum Value {
    Int(i128), Float(f64), Bool(bool), Str(String), Unit,
    Struct(Vec<Value>),
    Enum(u32, Vec<Value>),
    Array(Vec<Value>),
    /// Interpreter-only: a reference to the value stack slot (absolute index) reached through child indices.
    Ref(usize, Vec<usize>),
    /// Interpreter-only: handle of an owned `String` in the interpreter heap.
    Heap(usize),
}

/// Does a value of type `t` own heap memory that must be dropped? `String` and `Vec` do; a struct or enum does when
/// any field/payload does; arrays do when their element does. (Cycle-free after the checker's cycle check; the depth
/// bound only protects code that runs before that check.)
pub fn owned_ty(t: &Ty, structs: &[StructDef], enums: &[EnumDef]) -> bool {
    fn go(t: &Ty, s: &[StructDef], e: &[EnumDef], d: u32) -> bool {
        if d > 32 { return false; }
        match t {
            Ty::String | Ty::Vec(_) | Ty::Box(_) => true,
            Ty::Struct(i) => s.get(*i).map_or(false, |x| x.fields.iter().any(|f| go(&f.1, s, e, d + 1))),
            Ty::Enum(i) => e.get(*i).map_or(false, |x| x.variants.iter().any(|v| v.1.iter().any(|f| go(f, s, e, d + 1)))),
            Ty::Array(el, _) => go(el, s, e, d + 1),
            _ => false,
        }
    }
    go(t, structs, enums, 0)
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Builtin { Print, Peek, Poke, Len, StringFrom, StringConcat, StringPush, StringLen, StringClone, StringEq, VecNew, VecPush, VecLen, VecGet, VecSet, VecPop, VecClone, BoxNew, BoxInto, BoxGet, BoxSet }

#[derive(Debug, Clone)]
pub struct HExpr { pub kind: HKind, pub ty: Ty, pub span: Span }

#[derive(Debug, Clone)]
pub enum HKind {
    Lit(Value),
    Local(usize),
    Unary(UnOp, Box<HExpr>),
    Binary(BinOp, Box<HExpr>, Box<HExpr>),
    Call(usize, Vec<HExpr>),
    Builtin(Builtin, Vec<HExpr>),
    If(Box<HExpr>, HBlock, Option<HBlock>),
    Block(HBlock),
    /// Conversion of the operand to `self.ty`.
    Cast(Box<HExpr>),
    /// Field initialisers as (field index, value), in source evaluation order.
    Struct(usize, Vec<(usize, HExpr)>),
    Field(Box<HExpr>, usize),
    Index(Box<HExpr>, Box<HExpr>),
    Array(Vec<HExpr>),
    Repeat(Box<HExpr>, usize),
    Variant(u32, Vec<HExpr>),
    Match(Box<HExpr>, Vec<HArm>),
    /// `&place` / `&mut place` (bool = mutable). A `Proj::Deref` can only be the first projection.
    AddrOf(HPlace, bool),
    /// Read of the referent; the operand is always a `Local` of reference type.
    Deref(Box<HExpr>),
    /// Read of an owned local that *moves* the value out (the slot is left empty). Operand is the slot.
    Move(usize),
}

#[derive(Debug, Clone)]
pub struct HArm { pub pat: HPat, pub body: HExpr }

#[derive(Debug, Clone)]
pub enum HPat {
    Wild,
    Bind(usize),
    Lit(Value, Ty, Span),
    Variant(u32, Vec<HPat>),
}

#[derive(Debug, Clone)]
pub struct HBlock { pub stmts: Vec<HStmt>, pub tail: Option<Box<HExpr>> }

#[derive(Debug, Clone)]
pub enum HStmt {
    Let(usize, HExpr),
    Assign(HPlace, HExpr),
    Expr(HExpr),
    While(HExpr, HBlock),
    Return(Option<HExpr>),
    Break,
    Continue,
    /// Drop the owned value stored at the place (no-op if it was moved out); inserted by `drops::elaborate`.
    Drop(HPlace),
}

#[derive(Debug, Clone)]
pub struct HPlace { pub root: usize, pub proj: Vec<Proj> }

#[derive(Debug, Clone)]
pub enum Proj { Deref, Field(usize), Index(HExpr) }

#[derive(Debug, Clone)]
pub struct HFn {
    pub name: String, pub layer: Layer, pub ext: crate::ast::Ext,
    pub nparams: usize, pub nslots: usize,
    /// Type of every frame slot (parameters first); fully resolved after checking.
    pub slot_tys: Vec<Ty>,
    /// Source name of every frame slot (diagnostics only; pattern/let shadowing gives duplicates).
    pub slot_names: Vec<String>,
    pub params: Vec<Ty>, pub ret: Ty,
    pub body: HBlock,
}

#[derive(Debug, Clone)]
pub struct StructDef { pub name: String, pub fields: Vec<(String, Ty)> }

#[derive(Debug, Clone)]
pub struct EnumDef { pub name: String, pub variants: Vec<(String, Vec<Ty>)> }

#[derive(Debug, Clone)]
pub struct HProgram {
    pub fns: Vec<HFn>, pub structs: Vec<StructDef>, pub enums: Vec<EnumDef>,
    pub main: Option<usize>,
}
