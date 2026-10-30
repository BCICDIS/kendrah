//! Semantic types.

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum IntTy { I8, I16, I32, I64, U8, U16, U32, U64 }

impl IntTy {
    pub const ALL: [IntTy; 8] = [IntTy::I8, IntTy::I16, IntTy::I32, IntTy::I64, IntTy::U8, IntTy::U16, IntTy::U32, IntTy::U64];
    pub fn name(self) -> &'static str {
        match self {
            IntTy::I8 => "i8", IntTy::I16 => "i16", IntTy::I32 => "i32", IntTy::I64 => "i64",
            IntTy::U8 => "u8", IntTy::U16 => "u16", IntTy::U32 => "u32", IntTy::U64 => "u64",
        }
    }
    pub fn from_name(s: &str) -> Option<IntTy> { IntTy::ALL.into_iter().find(|t| t.name() == s) }
    pub fn bits(self) -> u32 {
        match self { IntTy::I8 | IntTy::U8 => 8, IntTy::I16 | IntTy::U16 => 16, IntTy::I32 | IntTy::U32 => 32, IntTy::I64 | IntTy::U64 => 64 }
    }
    pub fn signed(self) -> bool { matches!(self, IntTy::I8 | IntTy::I16 | IntTy::I32 | IntTy::I64) }
    pub fn min(self) -> i128 { if self.signed() { -(1i128 << (self.bits() - 1)) } else { 0 } }
    pub fn max(self) -> i128 { if self.signed() { (1i128 << (self.bits() - 1)) - 1 } else { (1i128 << self.bits()) - 1 } }
    pub fn contains(self, v: i128) -> bool { v >= self.min() && v <= self.max() }
    /// Two's-complement truncation of `v` to this type's width.
    pub fn wrap(self, v: i128) -> i128 {
        let m = 1i128 << self.bits();
        let r = v.rem_euclid(m);
        if self.signed() && r >= m / 2 { r - m } else { r }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum Ty {
    Int(IntTy), Float, Bool, Str, Unit, Never,
    /// Poison type after an error was reported; compatible with everything to avoid cascades.
    Error,
    /// Inference variable standing for "some integer type" (created by integer literals).
    Var(u32),
    Struct(usize), Enum(usize),
    Array(Box<Ty>, usize),
    /// Second-class reference `&T` / `&mut T` (bool = mutable); see docs/MEMORY.md. Only parameters and
    /// `let` locals have this type.
    Ref(Box<Ty>, bool),
    /// Owned, heap-allocated, move-only string (docs/MEMORY.md section 3). Only locals, parameters and returns.
    String,
    /// Owned, growable vector of scalar elements (integers, f64, bool); move-only like `String` (docs/MEMORY.md section 3b).
    Vec(Box<Ty>),
    /// Owned heap cell holding one value of any non-reference type; move-only (docs/MEMORY.md section 3d). Breaks
    /// the infinite size of recursive types: `enum List { Cons(i64, Box<List>), Nil }`.
    Box(Box<Ty>),
}

impl Ty {
    /// Owned heap values: move-only, dropped exactly once (drop elaboration), leak-checked by every engine.
    pub fn is_owned(&self) -> bool { matches!(self, Ty::String | Ty::Vec(_) | Ty::Box(_)) }
}
