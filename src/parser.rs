//! Recursive-descent parser with precedence climbing. Reports the first syntax error.

use crate::ast::*;
use crate::diag::{Diag, Span};
use crate::lexer::{Tok, Token};

struct ImplCtx { path: Path, ty: TyExpr, tparams: Vec<String> }

pub struct Parser { toks: Vec<Token>, pos: usize, no_struct: bool, for_id: u32, impl_ctx: Option<ImplCtx> }

type PResult<T> = Result<T, Diag>;

pub fn parse(toks: Vec<Token>) -> PResult<Program> {
    let mut p = Parser { toks, pos: 0, no_struct: false, for_id: 0, impl_ctx: None };
    let items = p.items(false)?;
    Ok(Program { items })
}

impl Parser {
    fn peek(&self) -> &Tok { &self.toks[self.pos].tok }
    fn peek_at(&self, n: usize) -> &Tok { &self.toks[(self.pos + n).min(self.toks.len() - 1)].tok }
    fn span(&self) -> Span { self.toks[self.pos].span }
    fn bump(&mut self) -> Token {
        let t = self.toks[self.pos].clone();
        if self.pos < self.toks.len() - 1 { self.pos += 1; }
        t
    }
    fn eat(&mut self, t: &Tok) -> bool {
        if self.peek() == t { self.bump(); true } else { false }
    }
    fn expect(&mut self, t: Tok, what: &str) -> PResult<Span> {
        if *self.peek() == t { Ok(self.bump().span) } else {
            Err(Diag::new(self.span(), format!("expected {}, found {}", what, describe(self.peek()))))
        }
    }
    fn ident(&mut self, what: &str) -> PResult<(String, Span)> {
        match self.peek().clone() {
            Tok::Ident(s) => { let sp = self.bump().span; Ok((s, sp)) }
            other => Err(Diag::new(self.span(), format!("expected {}, found {}", what, describe(&other)))),
        }
    }

    // ---------- items ----------

    /// Parses items until `}` (if `in_mod`) or end of file. A leading `@layer(x);` sets the default layer
    /// for the functions of this module; that default is applied by the checker via `layer` on each fn,
    /// so here we resolve it eagerly and store the result on every function.
    fn items(&mut self, in_mod: bool) -> PResult<Vec<Item>> {
        self.items_with(in_mod, None)
    }

    fn items_with(&mut self, in_mod: bool, inherited: Option<Layer>) -> PResult<Vec<Item>> {
        let mut items = Vec::new();
        let mut default_layer: Option<Layer> = None;
        loop {
            match self.peek() {
                Tok::Eof if !in_mod => break,
                Tok::Eof => return Err(Diag::new(self.span(), "unexpected end of file; missing `}`")),
                Tok::RBrace if in_mod => break,
                _ => {}
            }
            let mut layer = None;
            if *self.peek() == Tok::At {
                let sp = self.span();
                layer = Some(self.layer_attr()?);
                if self.eat(&Tok::Semi) {
                    if !items.is_empty() {
                        return Err(Diag::new(sp, "module-level @layer must appear before all functions"));
                    }
                    if default_layer.is_some() {
                        return Err(Diag::new(sp, "duplicate module-level @layer"));
                    }
                    default_layer = layer;
                    continue;
                }
            }
            let public = self.eat(&Tok::Pub);
            let eff = layer.or(default_layer).or(inherited).unwrap_or(Layer::Application);
            match self.peek() {
                Tok::Fn => items.push(Item::Fn(self.fn_decl(eff, public, Ext::None)?)),
                Tok::Ident(w) if (w == "extern" || w == "export") && *self.peek_at(1) == Tok::Fn => {
                    let ext = if w == "extern" { Ext::Import } else { Ext::Export };
                    self.bump();
                    items.push(Item::Fn(self.fn_decl(eff, public, ext)?));
                }
                Tok::Impl => {
                    if public { return Err(Diag::new(self.span(), "`pub impl` is not allowed (write `pub` on the methods)")); }
                    self.impl_block(eff, &mut items)?;
                }
                Tok::Struct | Tok::Enum | Tok::Mod if layer.is_some() => {
                    return Err(Diag::new(self.span(), "@layer applies only to functions"));
                }
                Tok::Use if layer.is_none() => {
                    let sp = self.bump().span;
                    if public { return Err(Diag::new(sp, "`pub use` (re-export) is not supported; imports are private to their module")); }
                    let path = self.path("path after `use`")?;
                    let alias = if self.eat(&Tok::As) { self.ident("alias name")?.0 } else { path.segs.last().unwrap().clone() };
                    self.expect(Tok::Semi, "`;` after use")?;
                    items.push(Item::Use(UseDecl { path, alias, span: sp }));
                }
                Tok::Use => return Err(Diag::new(self.span(), "@layer applies only to functions")),
                Tok::Struct => items.push(Item::Struct(self.struct_decl(public)?)),
                Tok::Enum => items.push(Item::Enum(self.enum_decl(public)?)),
                Tok::Mod => {
                    self.bump();
                    let (name, span) = self.ident("module name")?;
                    self.expect(Tok::LBrace, "`{`")?;
                    let inner = self.items_with(true, Some(default_layer.or(inherited).unwrap_or(Layer::Application)))?;
                    self.expect(Tok::RBrace, "`}`")?;
                    items.push(Item::Mod(ModDecl { name, span, public, items: inner }));
                }
                other => {
                    let o = other.clone();
                    return Err(Diag::new(self.span(), format!("expected an item (`fn`, `struct`, `enum`, `impl`, `mod`, `use`), found {}", describe(&o))));
                }
            }
        }
        Ok(items)
    }

    fn layer_attr(&mut self) -> PResult<Layer> {
        self.expect(Tok::At, "`@`")?;
        let (name, sp) = self.ident("attribute name")?;
        if name != "layer" {
            return Err(Diag::new(sp, format!("unknown attribute `@{}` (only `@layer` exists)", name)));
        }
        self.expect(Tok::LParen, "`(`")?;
        let (l, lsp) = self.ident("layer name")?;
        let layer = match l.as_str() {
            "hardware" => Layer::Hardware,
            "application" => Layer::Application,
            "declarative" => Layer::Declarative,
            _ => return Err(Diag::new(lsp, format!("unknown layer `{}` (expected hardware, application, or declarative)", l))),
        };
        self.expect(Tok::RParen, "`)`")?;
        Ok(layer)
    }

    fn path(&mut self, what: &str) -> PResult<Path> {
        let (first, span) = self.ident(what)?;
        let mut segs = vec![first];
        while *self.peek() == Tok::ColonColon {
            self.bump();
            let (s, _) = self.ident("name after `::`")?;
            segs.push(s);
        }
        if segs[0] == "Self" {
            match &self.impl_ctx {
                Some(c) => { let mut v = c.path.segs.clone(); v.extend(segs.drain(1..)); segs = v; }
                None => return Err(Diag::new(span, "`Self` is only available inside an `impl` block")),
            }
        }
        Ok(Path { segs, span })
    }

    /// Consume one `>`; a `>>` token is split so nested generic arguments close correctly.
    fn close_angle(&mut self, what: &str) -> PResult<()> {
        if *self.peek() == Tok::Shr { self.toks[self.pos].tok = Tok::Gt; return Ok(()); }
        self.expect(Tok::Gt, what)?;
        Ok(())
    }

    fn tparam_list(&mut self) -> PResult<Vec<String>> {
        let mut tparams: Vec<String> = Vec::new();
        if self.eat(&Tok::Lt) {
            loop {
                let (t, tsp) = self.ident("type parameter name")?;
                if tparams.contains(&t) { return Err(Diag::new(tsp, format!("duplicate type parameter `{}`", t))); }
                tparams.push(t);
                if !self.eat(&Tok::Comma) { break; }
            }
            self.close_angle("`>` after type parameters")?;
        }
        Ok(tparams)
    }

    fn ty(&mut self) -> PResult<TyExpr> { self.ty_inner(true) }

    fn ty_inner(&mut self, args: bool) -> PResult<TyExpr> {
        if *self.peek() == Tok::AndAnd {
            return Err(Diag::new(self.span(), "references to references (`&&T`) are not supported (references are second-class, see docs/MEMORY.md)"));
        }
        if *self.peek() == Tok::Amp {
            let sp = self.bump().span;
            let m = self.eat(&Tok::Mut);
            let t = self.ty()?;
            return Ok(TyExpr::Ref(Box::new(t), m, sp));
        }
        if *self.peek() == Tok::LBracket {
            let sp = self.bump().span;
            let t = self.ty()?;
            self.expect(Tok::Semi, "`;` in array type `[T; N]`")?;
            let n = match self.peek().clone() {
                Tok::Int(n) => { self.bump(); n }
                o => return Err(Diag::new(self.span(), format!("expected array length, found {}", describe(&o)))),
            };
            self.expect(Tok::RBracket, "`]`")?;
            return Ok(TyExpr::Array(Box::new(t), n, sp));
        }
        if matches!(self.peek(), Tok::Ident(s) if s == "Self") {
            if let Some(c) = &self.impl_ctx { let t = c.ty.clone(); self.bump(); return Ok(t); }
        }
        let p = self.path("type name")?;
        if args && *self.peek() == Tok::Lt {
            self.bump();
            let mut targs = vec![self.ty()?];
            while self.eat(&Tok::Comma) { targs.push(self.ty()?); }
            self.close_angle("`>` after type arguments")?;
            return Ok(TyExpr::Generic(p, targs));
        }
        Ok(TyExpr::Named(p))
    }

    fn fn_decl(&mut self, layer: Layer, public: bool, ext: Ext) -> PResult<FnDecl> {
        self.expect(Tok::Fn, "`fn`")?;
        let (name, span) = self.ident("function name")?;
        let mut tparams = self.tparam_list()?;
        let mut self_kind = SelfKind::None;
        let mut params = Vec::new();
        let ctx = self.impl_ctx.as_ref().map(|c| (c.path.clone(), c.ty.clone(), c.tparams.clone()));
        if let Some((_, _, itp)) = &ctx {
            for t in &tparams { if itp.contains(t) { return Err(Diag::new(span, format!("type parameter `{}` shadows a parameter of the `impl`", t))); } }
            let mut all = itp.clone();
            all.extend(tparams);
            tparams = all;
        }
        self.expect(Tok::LParen, "`(`")?;
        if let Some((_, sty, _)) = &ctx {
            let sp = self.span();
            let is_self = |t: &Tok| matches!(t, Tok::Ident(s) if s == "self");
            if is_self(self.peek()) {
                self.bump();
                self_kind = SelfKind::Value;
                params.push(Param { name: "self".into(), ty: sty.clone(), span: sp });
            } else if *self.peek() == Tok::Amp && (is_self(self.peek_at(1)) || (*self.peek_at(1) == Tok::Mut && is_self(self.peek_at(2)))) {
                self.bump();
                let m = self.eat(&Tok::Mut);
                self.bump();
                self_kind = if m { SelfKind::RefMut } else { SelfKind::Ref };
                params.push(Param { name: "self".into(), ty: TyExpr::Ref(Box::new(sty.clone()), m, sp), span: sp });
            }
            if self_kind != SelfKind::None && !self.eat(&Tok::Comma) && *self.peek() != Tok::RParen {
                return Err(Diag::new(self.span(), "expected `,` or `)` after `self`"));
            }
        }
        if *self.peek() != Tok::RParen {
            loop {
                let (pn, psp) = self.ident("parameter name")?;
                self.expect(Tok::Colon, "`:` (parameters need a type annotation)")?;
                let t = self.ty()?;
                params.push(Param { name: pn, ty: t, span: psp });
                if !self.eat(&Tok::Comma) { break; }
            }
        }
        self.expect(Tok::RParen, "`)`")?;
        let ret = if self.eat(&Tok::Arrow) { Some(self.ty()?) } else { None };
        let body = if ext == Ext::Import {
            let sp = self.span();
            self.expect(Tok::Semi, "`;` (an `extern fn` declares a C function and has no body)")?;
            Block { stmts: vec![], tail: None, span: sp }
        } else { self.block()? };
        let (name, assoc) = match ctx {
            Some((path, _, itp)) => (format!("{}::{}", path.segs.last().unwrap(), name), Some(AssocInfo { ty_path: path, method: name, self_kind, impl_arity: itp.len() })),
            None => (name, None),
        };
        Ok(FnDecl { ext, name, span, public, layer, tparams, params, ret, body, assoc })
    }

    /// `impl<T..> Type<T..> { fn .. }`: methods become ordinary function items tagged with their target type.
    fn impl_block(&mut self, layer: Layer, items: &mut Vec<Item>) -> PResult<()> {
        let isp = self.expect(Tok::Impl, "`impl`")?;
        let tparams = self.tparam_list()?;
        let ty = self.ty()?;
        let path = match &ty {
            TyExpr::Named(p) => p.clone(),
            TyExpr::Generic(p, args) => {
                if args.len() != tparams.len() { return Err(Diag::new(p.span, "the type parameters of an `impl` must be exactly the type's arguments, e.g. `impl<T> Opt<T>`")); }
                for a in args {
                    match a {
                        TyExpr::Named(q) if q.segs.len() == 1 && tparams.contains(&q.segs[0]) => {}
                        _ => return Err(Diag::new(p.span, "`impl` arguments must be the impl's own type parameters (specialised impls such as `impl Opt<i64>` are not supported)")),
                    }
                }
                p.clone()
            }
            _ => return Err(Diag::new(isp, "`impl` target must be a struct or enum type")),
        };
        if matches!(ty, TyExpr::Named(_)) && !tparams.is_empty() {
            return Err(Diag::new(isp, "an `impl` with type parameters must name a generic type, e.g. `impl<T> Opt<T>`"));
        }
        self.expect(Tok::LBrace, "`{`")?;
        self.impl_ctx = Some(ImplCtx { path, ty, tparams });
        let r = (|| -> PResult<()> {
            while *self.peek() != Tok::RBrace {
                let public = self.eat(&Tok::Pub);
                if *self.peek() != Tok::Fn { return Err(Diag::new(self.span(), "only `fn` items may appear in an `impl` block")); }
                items.push(Item::Fn(self.fn_decl(layer, public, Ext::None)?));
            }
            Ok(())
        })();
        self.impl_ctx = None;
        r?;
        self.expect(Tok::RBrace, "`}`")?;
        Ok(())
    }

    fn struct_decl(&mut self, public: bool) -> PResult<StructDecl> {
        self.expect(Tok::Struct, "`struct`")?;
        let (name, span) = self.ident("struct name")?;
        let tparams = self.tparam_list()?;
        self.expect(Tok::LBrace, "`{`")?;
        let mut fields = Vec::new();
        while *self.peek() != Tok::RBrace {
            let (f, fsp) = self.ident("field name")?;
            self.expect(Tok::Colon, "`:`")?;
            let t = self.ty()?;
            fields.push((f, t, fsp));
            if !self.eat(&Tok::Comma) { break; }
        }
        self.expect(Tok::RBrace, "`}`")?;
        Ok(StructDecl { name, span, public, tparams, fields })
    }

    fn enum_decl(&mut self, public: bool) -> PResult<EnumDecl> {
        self.expect(Tok::Enum, "`enum`")?;
        let (name, span) = self.ident("enum name")?;
        let tparams = self.tparam_list()?;
        self.expect(Tok::LBrace, "`{`")?;
        let mut variants = Vec::new();
        while *self.peek() != Tok::RBrace {
            let (v, vsp) = self.ident("variant name")?;
            let mut payload = Vec::new();
            if self.eat(&Tok::LParen) {
                if *self.peek() != Tok::RParen {
                    loop {
                        payload.push(self.ty()?);
                        if !self.eat(&Tok::Comma) { break; }
                    }
                }
                self.expect(Tok::RParen, "`)`")?;
            }
            variants.push((v, payload, vsp));
            if !self.eat(&Tok::Comma) { break; }
        }
        self.expect(Tok::RBrace, "`}`")?;
        Ok(EnumDecl { name, span, public, tparams, variants })
    }

    // ---------- statements ----------

    fn block(&mut self) -> PResult<Block> {
        let span = self.expect(Tok::LBrace, "`{`")?;
        let saved = std::mem::replace(&mut self.no_struct, false);
        let mut stmts = Vec::new();
        let mut tail = None;
        loop {
            match self.peek() {
                Tok::RBrace => { self.bump(); break; }
                Tok::Eof => return Err(Diag::new(self.span(), "unexpected end of file; missing `}`")),
                Tok::Semi => { self.bump(); }
                Tok::Let => stmts.push(self.let_stmt()?),
                Tok::While => {
                    let sp = self.bump().span;
                    let cond = self.expr_no_struct()?;
                    let body = self.block()?;
                    stmts.push(Stmt::While { cond, body, span: sp });
                }
                Tok::For => {
                    // `for i in a..b { body }` desugars to a counted `while` with hidden, uniquely named slots:
                    // { let mut $cN = a; let $eN = b; while $cN < $eN { let i = $cN; $cN = $cN + 1; { body } } }
                    let sp = self.bump().span;
                    let (var, vsp) = self.ident("loop variable")?;
                    self.expect(Tok::In, "`in`")?;
                    let lo = self.expr_no_struct()?;
                    self.expect(Tok::DotDot, "`..` (only `a..b` ranges are supported)")?;
                    let hi = self.expr_no_struct()?;
                    let body = self.block()?;
                    self.for_id += 1;
                    let (c, e) = (format!("$c{}", self.for_id), format!("$e{}", self.for_id));
                    let path = |n: &String| Expr { kind: ExprKind::Path(Path { segs: vec![n.clone()], span: sp }), span: sp };
                    let one = Expr { kind: ExprKind::Int(1), span: sp };
                    let cond = Expr { kind: ExprKind::Binary(BinOp::Lt, Box::new(path(&c)), Box::new(path(&e))), span: sp };
                    let step = Expr { kind: ExprKind::Binary(BinOp::Add, Box::new(path(&c)), Box::new(one)), span: sp };
                    let inner = Block { span: body.span, tail: None, stmts: vec![
                        Stmt::Let { name: var, mutable: false, ty: None, init: path(&c), span: vsp },
                        // the counter advances before the body runs, so `continue` needs no special case
                        Stmt::Assign { target: path(&c), value: step, span: sp },
                        Stmt::Expr(Expr { kind: ExprKind::Block(body), span: sp }),
                    ]};
                    let outer = Block { span: sp, tail: None, stmts: vec![
                        Stmt::Let { name: c.clone(), mutable: true, ty: None, init: lo, span: sp },
                        Stmt::Let { name: e.clone(), mutable: false, ty: None, init: hi, span: sp },
                        Stmt::While { cond, body: inner, span: sp },
                    ]};
                    stmts.push(Stmt::Expr(Expr { kind: ExprKind::Block(outer), span: sp }));
                }
                Tok::Break | Tok::Continue => {
                    let t = self.bump();
                    if !self.eat(&Tok::Semi) && *self.peek() != Tok::RBrace {
                        return Err(Diag::new(self.span(), format!("expected `;` after {}, found {}", sym(&t.tok), describe(self.peek()))));
                    }
                    stmts.push(if t.tok == Tok::Break { Stmt::Break { span: t.span } } else { Stmt::Continue { span: t.span } });
                }
                Tok::Return => {
                    let sp = self.bump().span;
                    let value = if matches!(self.peek(), Tok::Semi | Tok::RBrace) { None } else { Some(self.expr()?) };
                    if !self.eat(&Tok::Semi) && *self.peek() != Tok::RBrace {
                        return Err(Diag::new(self.span(), format!("expected `;` after return, found {}", describe(self.peek()))));
                    }
                    stmts.push(Stmt::Return { value, span: sp });
                }
                Tok::LBrace | Tok::If | Tok::Match | Tok::Unsafe => {
                    // A block-like expression at statement start ends the statement at its closing brace
                    // (so `{ .. } *r = 1;` is a block followed by an assignment, not a multiplication).
                    let e = self.primary()?;
                    if self.eat(&Tok::Semi) { stmts.push(Stmt::Expr(e)); }
                    else if *self.peek() == Tok::RBrace { tail = Some(Box::new(e)); }
                    else if *self.peek() == Tok::Dot || *self.peek() == Tok::LBracket {
                        return Err(Diag::new(self.span(), "cannot project from a block-like expression at statement start; bind it to a variable first"));
                    } else { stmts.push(Stmt::Expr(e)); }
                }
                _ => {
                    let e = self.expr()?;
                    if *self.peek() == Tok::Assign {
                        let sp = self.bump().span;
                        if !matches!(e.kind, ExprKind::Path(ref p) if p.segs.len() == 1) && !matches!(e.kind, ExprKind::Field(..) | ExprKind::Index(..) | ExprKind::Deref(..)) {
                            return Err(Diag::new(e.span, "invalid assignment target (expected a variable, field, array element or `*reference`)"));
                        }
                        let value = self.expr()?;
                        self.expect(Tok::Semi, "`;` after assignment")?;
                        stmts.push(Stmt::Assign { target: e, value, span: sp });
                        continue;
                    }
                    let block_like = matches!(e.kind, ExprKind::If(..) | ExprKind::Block(_) | ExprKind::Unsafe(_) | ExprKind::Match(..));
                    if self.eat(&Tok::Semi) {
                        stmts.push(Stmt::Expr(e));
                    } else if *self.peek() == Tok::RBrace {
                        tail = Some(Box::new(e));
                    } else if block_like {
                        stmts.push(Stmt::Expr(e));
                    } else {
                        return Err(Diag::new(self.span(), format!("expected `;` or `}}`, found {}", describe(self.peek()))));
                    }
                }
            }
        }
        self.no_struct = saved;
        Ok(Block { stmts, tail, span })
    }

    fn let_stmt(&mut self) -> PResult<Stmt> {
        let span = self.expect(Tok::Let, "`let`")?;
        let mutable = self.eat(&Tok::Mut);
        let (name, _) = self.ident("variable name")?;
        let ty = if self.eat(&Tok::Colon) { Some(self.ty()?) } else { None };
        self.expect(Tok::Assign, "`=` (variables must be initialized)")?;
        let init = self.expr()?;
        self.expect(Tok::Semi, "`;` after let")?;
        Ok(Stmt::Let { name, mutable, ty, init, span })
    }

    // ---------- expressions ----------

    pub fn expr(&mut self) -> PResult<Expr> { self.binary(0) }

    /// Expression in a position where `Name {` must not start a struct literal (conditions, scrutinees).
    fn expr_no_struct(&mut self) -> PResult<Expr> {
        let saved = std::mem::replace(&mut self.no_struct, true);
        let r = self.expr();
        self.no_struct = saved;
        r
    }

    fn binop_info(t: &Tok) -> Option<(BinOp, u8)> {
        Some(match t {
            Tok::OrOr => (BinOp::Or, 1), Tok::AndAnd => (BinOp::And, 2),
            Tok::EqEq => (BinOp::Eq, 3), Tok::Ne => (BinOp::Ne, 3),
            Tok::Lt => (BinOp::Lt, 4), Tok::Le => (BinOp::Le, 4), Tok::Gt => (BinOp::Gt, 4), Tok::Ge => (BinOp::Ge, 4),
            Tok::Pipe => (BinOp::BitOr, 5), Tok::Caret => (BinOp::BitXor, 6), Tok::Amp => (BinOp::BitAnd, 7),
            Tok::Shl => (BinOp::Shl, 8), Tok::Shr => (BinOp::Shr, 8),
            Tok::Plus => (BinOp::Add, 9), Tok::Minus => (BinOp::Sub, 9),
            Tok::Star => (BinOp::Mul, 10), Tok::Slash => (BinOp::Div, 10), Tok::Percent => (BinOp::Rem, 10),
            _ => return None,
        })
    }

    fn binary(&mut self, min: u8) -> PResult<Expr> {
        let mut lhs = self.cast()?;
        while let Some((op, prec)) = Self::binop_info(self.peek()) {
            if prec < min { break; }
            let span = self.bump().span;
            let rhs = self.binary(prec + 1)?;
            lhs = Expr { kind: ExprKind::Binary(op, Box::new(lhs), Box::new(rhs)), span };
        }
        Ok(lhs)
    }

    fn cast(&mut self) -> PResult<Expr> {
        let mut e = self.unary()?;
        while *self.peek() == Tok::As {
            let span = self.bump().span;
            let t = self.ty_inner(false)?;
            e = Expr { kind: ExprKind::Cast(Box::new(e), t), span };
        }
        Ok(e)
    }

    fn unary(&mut self) -> PResult<Expr> {
        let span = self.span();
        match self.peek() {
            Tok::Minus => { self.bump(); let e = self.unary()?; Ok(Expr { kind: ExprKind::Unary(UnOp::Neg, Box::new(e)), span }) }
            Tok::Bang => { self.bump(); let e = self.unary()?; Ok(Expr { kind: ExprKind::Unary(UnOp::Not, Box::new(e)), span }) }
            Tok::Amp => {
                self.bump();
                let m = self.eat(&Tok::Mut);
                let e = self.unary()?;
                Ok(Expr { kind: ExprKind::AddrOf(Box::new(e), m), span })
            }
            Tok::Star => { self.bump(); let e = self.unary()?; Ok(Expr { kind: ExprKind::Deref(Box::new(e)), span }) }
            Tok::AndAnd => Err(Diag::new(span, "`&&` here would be a reference to a reference, which is not supported (write `&` once)")),
            _ => self.postfix(),
        }
    }

    fn postfix(&mut self) -> PResult<Expr> {
        let mut e = self.primary()?;
        loop {
            match self.peek() {
                Tok::Dot => {
                    let span = self.bump().span;
                    let (f, _) = self.ident("field or method name")?;
                    if *self.peek() == Tok::LParen {
                        self.bump();
                        let saved = std::mem::replace(&mut self.no_struct, false);
                        let mut args = Vec::new();
                        if *self.peek() != Tok::RParen {
                            loop { args.push(self.expr()?); if !self.eat(&Tok::Comma) { break; } }
                        }
                        self.no_struct = saved;
                        self.expect(Tok::RParen, "`)`")?;
                        e = Expr { kind: ExprKind::MethodCall(Box::new(e), f, args), span };
                    } else {
                        e = Expr { kind: ExprKind::Field(Box::new(e), f), span };
                    }
                }
                Tok::LBracket => {
                    let span = self.bump().span;
                    let saved = std::mem::replace(&mut self.no_struct, false);
                    let i = self.expr()?;
                    self.no_struct = saved;
                    self.expect(Tok::RBracket, "`]`")?;
                    e = Expr { kind: ExprKind::Index(Box::new(e), Box::new(i)), span };
                }
                _ => break,
            }
        }
        Ok(e)
    }

    fn primary(&mut self) -> PResult<Expr> {
        let span = self.span();
        match self.peek().clone() {
            Tok::Int(v) => { self.bump(); Ok(Expr { kind: ExprKind::Int(v), span }) }
            Tok::Float(v) => { self.bump(); Ok(Expr { kind: ExprKind::Float(v), span }) }
            Tok::Str(s) => { self.bump(); Ok(Expr { kind: ExprKind::Str(s), span }) }
            Tok::True => { self.bump(); Ok(Expr { kind: ExprKind::Bool(true), span }) }
            Tok::False => { self.bump(); Ok(Expr { kind: ExprKind::Bool(false), span }) }
            Tok::LParen => {
                self.bump();
                let saved = std::mem::replace(&mut self.no_struct, false);
                let e = self.expr()?;
                self.no_struct = saved;
                self.expect(Tok::RParen, "`)`")?;
                Ok(e)
            }
            Tok::LBracket => {
                self.bump();
                let saved = std::mem::replace(&mut self.no_struct, false);
                let r = self.array_body(span);
                self.no_struct = saved;
                r
            }
            Tok::LBrace => { let b = self.block()?; Ok(Expr { kind: ExprKind::Block(b), span }) }
            Tok::Unsafe => { self.bump(); let b = self.block()?; Ok(Expr { kind: ExprKind::Unsafe(b), span }) }
            Tok::If => self.if_expr(),
            Tok::Match => self.match_expr(),
            Tok::Ident(_) => {
                let path = self.path("name")?;
                if self.eat(&Tok::LParen) {
                    let saved = std::mem::replace(&mut self.no_struct, false);
                    let mut args = Vec::new();
                    if *self.peek() != Tok::RParen {
                        loop {
                            args.push(self.expr()?);
                            if !self.eat(&Tok::Comma) { break; }
                        }
                    }
                    self.no_struct = saved;
                    self.expect(Tok::RParen, "`)`")?;
                    Ok(Expr { kind: ExprKind::Call(path, args), span })
                } else if !self.no_struct && *self.peek() == Tok::LBrace
                    && (*self.peek_at(1) == Tok::RBrace || (matches!(self.peek_at(1), Tok::Ident(_)) && *self.peek_at(2) == Tok::Colon)) {
                    self.bump();
                    let saved = std::mem::replace(&mut self.no_struct, false);
                    let mut fields = Vec::new();
                    while *self.peek() != Tok::RBrace {
                        let (f, fsp) = self.ident("field name")?;
                        self.expect(Tok::Colon, "`:`")?;
                        let v = self.expr()?;
                        fields.push((f, v, fsp));
                        if !self.eat(&Tok::Comma) { break; }
                    }
                    self.no_struct = saved;
                    self.expect(Tok::RBrace, "`}`")?;
                    Ok(Expr { kind: ExprKind::StructLit(path, fields), span })
                } else {
                    Ok(Expr { kind: ExprKind::Path(path), span })
                }
            }
            other => Err(Diag::new(span, format!("expected an expression, found {}", describe(&other)))),
        }
    }

    fn array_body(&mut self, span: Span) -> PResult<Expr> {
        if self.eat(&Tok::RBracket) {
            return Ok(Expr { kind: ExprKind::Array(vec![]), span });
        }
        let first = self.expr()?;
        if self.eat(&Tok::Semi) {
            let n = match self.peek().clone() {
                Tok::Int(n) => { self.bump(); n }
                o => return Err(Diag::new(self.span(), format!("expected array length (an integer literal), found {}", describe(&o)))),
            };
            self.expect(Tok::RBracket, "`]`")?;
            return Ok(Expr { kind: ExprKind::Repeat(Box::new(first), n), span });
        }
        let mut elems = vec![first];
        while self.eat(&Tok::Comma) {
            if *self.peek() == Tok::RBracket { break; }
            elems.push(self.expr()?);
        }
        self.expect(Tok::RBracket, "`]`")?;
        Ok(Expr { kind: ExprKind::Array(elems), span })
    }

    fn if_expr(&mut self) -> PResult<Expr> {
        let span = self.expect(Tok::If, "`if`")?;
        let cond = self.expr_no_struct()?;
        let then = self.block()?;
        let els = if self.eat(&Tok::Else) {
            if *self.peek() == Tok::If {
                let e = self.if_expr()?;
                let sp = e.span;
                Some(Block { stmts: vec![], tail: Some(Box::new(e)), span: sp })
            } else { Some(self.block()?) }
        } else { None };
        Ok(Expr { kind: ExprKind::If(Box::new(cond), then, els), span })
    }

    fn match_expr(&mut self) -> PResult<Expr> {
        let span = self.expect(Tok::Match, "`match`")?;
        let scrut = self.expr_no_struct()?;
        self.expect(Tok::LBrace, "`{`")?;
        let saved = std::mem::replace(&mut self.no_struct, false);
        let mut arms = Vec::new();
        while *self.peek() != Tok::RBrace {
            let pat = self.pattern()?;
            self.expect(Tok::FatArrow, "`=>`")?;
            let body = self.expr()?;
            let block_like = matches!(body.kind, ExprKind::Block(_) | ExprKind::If(..) | ExprKind::Match(..) | ExprKind::Unsafe(_));
            arms.push(Arm { pat, body });
            if !self.eat(&Tok::Comma) && !block_like && *self.peek() != Tok::RBrace {
                return Err(Diag::new(self.span(), format!("expected `,` or `}}` after match arm, found {}", describe(self.peek()))));
            }
        }
        self.no_struct = saved;
        self.expect(Tok::RBrace, "`}`")?;
        Ok(Expr { kind: ExprKind::Match(Box::new(scrut), arms), span })
    }

    fn pattern(&mut self) -> PResult<Pattern> {
        let span = self.span();
        let kind = match self.peek().clone() {
            Tok::Int(v) => { self.bump(); PatKind::Int(v as i128) }
            Tok::Minus => {
                self.bump();
                match self.peek().clone() {
                    Tok::Int(v) => { self.bump(); PatKind::Int(-(v as i128)) }
                    o => return Err(Diag::new(self.span(), format!("expected integer after `-` in pattern, found {}", describe(&o)))),
                }
            }
            Tok::True => { self.bump(); PatKind::Bool(true) }
            Tok::False => { self.bump(); PatKind::Bool(false) }
            Tok::Str(s) => { self.bump(); PatKind::Str(s) }
            Tok::Ident(n) if n == "_" => { self.bump(); PatKind::Wild }
            Tok::Ident(_) => {
                let path = self.path("pattern")?;
                if self.eat(&Tok::LParen) {
                    let mut subs = Vec::new();
                    if *self.peek() != Tok::RParen {
                        loop {
                            subs.push(self.pattern()?);
                            if !self.eat(&Tok::Comma) { break; }
                        }
                    }
                    self.expect(Tok::RParen, "`)`")?;
                    PatKind::Variant(path, subs)
                } else if path.segs.len() == 1 {
                    PatKind::Bind(path.segs[0].clone())
                } else {
                    PatKind::Variant(path, vec![])
                }
            }
            o => return Err(Diag::new(span, format!("expected a pattern, found {}", describe(&o)))),
        };
        Ok(Pattern { kind, span })
    }
}

fn describe(t: &Tok) -> String {
    match t {
        Tok::Eof => "end of file".into(),
        Tok::Ident(s) => format!("identifier `{}`", s),
        Tok::Int(v) => format!("`{}`", v),
        Tok::Float(v) => format!("`{:?}`", v),
        Tok::Str(_) => "string literal".into(),
        other => format!("`{}`", sym(other)),
    }
}

fn sym(t: &Tok) -> &'static str {
    match t {
        Tok::Fn => "fn", Tok::Let => "let", Tok::Mut => "mut", Tok::If => "if", Tok::Else => "else",
        Tok::While => "while", Tok::For => "for", Tok::Use => "use", Tok::Impl => "impl", Tok::Break => "break", Tok::Continue => "continue", Tok::In => "in", Tok::DotDot => "..", Tok::Return => "return", Tok::True => "true", Tok::False => "false",
        Tok::Unsafe => "unsafe", Tok::As => "as", Tok::Struct => "struct", Tok::Enum => "enum", Tok::Match => "match",
        Tok::Mod => "mod", Tok::Pub => "pub", Tok::At => "@", Tok::LParen => "(", Tok::RParen => ")",
        Tok::LBrace => "{", Tok::RBrace => "}", Tok::LBracket => "[", Tok::RBracket => "]", Tok::Comma => ",",
        Tok::Colon => ":", Tok::ColonColon => "::", Tok::Semi => ";", Tok::Arrow => "->", Tok::FatArrow => "=>",
        Tok::Dot => ".", Tok::Plus => "+", Tok::Minus => "-", Tok::Star => "*", Tok::Slash => "/",
        Tok::Percent => "%", Tok::Assign => "=", Tok::EqEq => "==", Tok::Ne => "!=", Tok::Lt => "<",
        Tok::Le => "<=", Tok::Gt => ">", Tok::Ge => ">=", Tok::AndAnd => "&&", Tok::OrOr => "||", Tok::Bang => "!",
        Tok::Amp => "&", Tok::Pipe => "|", Tok::Caret => "^", Tok::Shl => "<<", Tok::Shr => ">>",
        _ => "?",
    }
}
