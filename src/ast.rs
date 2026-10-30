//! Abstract syntax tree (untyped, unresolved names).

use crate::diag::Span;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Layer { Hardware, Application, Declarative }

impl Layer {
    pub fn name(self) -> &'static str {
        match self { Layer::Hardware => "hardware", Layer::Application => "application", Layer::Declarative => "declarative" }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum UnOp { Neg, Not }

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BinOp { Add, Sub, Mul, Div, Rem, Eq, Ne, Lt, Le, Gt, Ge, And, Or, BitAnd, BitOr, BitXor, Shl, Shr }

#[derive(Debug, Clone, PartialEq)]
pub struct Path { pub segs: Vec<String>, pub span: Span }

impl Path { pub fn text(&self) -> String { self.segs.join("::") } }

#[derive(Debug, Clone)]
pub enum TyExpr { Named(Path), Generic(Path, Vec<TyExpr>), Array(Box<TyExpr>, u64, Span), Ref(Box<TyExpr>, bool, Span) }

#[derive(Debug, Clone)]
pub struct Expr { pub kind: ExprKind, pub span: Span }

#[derive(Debug, Clone)]
pub enum ExprKind {
    Int(u64), Float(f64), Bool(bool), Str(String),
    Path(Path),
    Unary(UnOp, Box<Expr>),
    Binary(BinOp, Box<Expr>, Box<Expr>),
    Call(Path, Vec<Expr>),
    /// `recv.method(args)`; the span of the method name is the expression span.
    MethodCall(Box<Expr>, String, Vec<Expr>),
    If(Box<Expr>, Block, Option<Block>),
    Block(Block),
    Unsafe(Block),
    Cast(Box<Expr>, TyExpr),
    StructLit(Path, Vec<(String, Expr, Span)>),
    Field(Box<Expr>, String),
    Index(Box<Expr>, Box<Expr>),
    Array(Vec<Expr>),
    Repeat(Box<Expr>, u64),
    Match(Box<Expr>, Vec<Arm>),
    /// `&place` / `&mut place` (bool = mutable).
    AddrOf(Box<Expr>, bool),
    /// `*r`
    Deref(Box<Expr>),
}

#[derive(Debug, Clone)]
pub struct Arm { pub pat: Pattern, pub body: Expr }

#[derive(Debug, Clone)]
pub struct Pattern { pub kind: PatKind, pub span: Span }

#[derive(Debug, Clone)]
pub enum PatKind {
    Wild,
    Bind(String),
    Int(i128),
    Bool(bool),
    Str(String),
    Variant(Path, Vec<Pattern>),
}

#[derive(Debug, Clone)]
pub struct Block { pub stmts: Vec<Stmt>, pub tail: Option<Box<Expr>>, pub span: Span }

#[derive(Debug, Clone)]
pub enum Stmt {
    Let { name: String, mutable: bool, ty: Option<TyExpr>, init: Expr, span: Span },
    Assign { target: Expr, value: Expr, span: Span },
    Expr(Expr),
    While { cond: Expr, body: Block, span: Span },
    Return { value: Option<Expr>, span: Span },
    Break { span: Span },
    Continue { span: Span },
}

#[derive(Debug, Clone)]
pub struct Param { pub name: String, pub ty: TyExpr, pub span: Span }

/// C-interop role of a function: `extern fn f(..) -> T;` imports a C symbol, `export fn f(..) {..}` publishes a
/// Kendrah function under an unmangled C-ABI symbol.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Ext { None, Import, Export }

#[derive(Debug, Clone)]
pub struct FnDecl {
    pub ext: Ext,
    pub name: String, pub span: Span, pub public: bool, pub layer: Layer, pub tparams: Vec<String>,
    pub params: Vec<Param>, pub ret: Option<TyExpr>, pub body: Block,
    /// Set for methods and associated functions declared in an `impl` block.
    pub assoc: Option<AssocInfo>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SelfKind { None, Value, Ref, RefMut }

/// `impl` membership: the target type path, the bare method name and the kind of the `self` parameter.
#[derive(Debug, Clone)]
pub struct AssocInfo { pub ty_path: Path, pub method: String, pub self_kind: SelfKind, pub impl_arity: usize }

#[derive(Debug, Clone)]
pub struct StructDecl { pub name: String, pub span: Span, pub public: bool, pub tparams: Vec<String>, pub fields: Vec<(String, TyExpr, Span)> }

#[derive(Debug, Clone)]
pub struct EnumDecl { pub name: String, pub span: Span, pub public: bool, pub tparams: Vec<String>, pub variants: Vec<(String, Vec<TyExpr>, Span)> }

#[derive(Debug, Clone)]
pub struct ModDecl { pub name: String, pub span: Span, pub public: bool, pub items: Vec<Item> }

#[derive(Debug, Clone)]
pub struct UseDecl { pub path: Path, pub alias: String, pub span: Span }

#[derive(Debug, Clone)]
pub enum Item { Fn(FnDecl), Struct(StructDecl), Enum(EnumDecl), Mod(ModDecl), Use(UseDecl) }

#[derive(Debug, Clone)]
pub struct Program { pub items: Vec<Item> }
