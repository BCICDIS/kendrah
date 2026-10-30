//! Name resolution, type checking (with integer-literal inference), `@layer` rule enforcement,
//! and lowering of the AST to typed HIR (`crate::hir`).
//!
//! Type system (M1): monomorphic; sized integer types; no implicit conversions; integer literals get an
//! inference variable that is unified with their context and defaults to `i64`; `let` bindings are inferred
//! from their initializer; function signatures, struct fields and enum payloads are explicit.

use crate::ast::*;
use crate::diag::{Diag, Span};
use crate::hir::*;
use crate::ty::*;
use std::collections::{HashMap, HashSet};

pub const BUILTINS: [&str; 21] = ["print", "peek", "poke", "len", "string_from", "string_concat", "string_push", "string_len", "string_clone", "string_eq",
    "vec_new", "vec_push", "vec_len", "vec_get", "vec_set", "vec_pop", "vec_clone",
    "box_new", "box_into", "box_get", "box_set"];
const MAX_ARRAY_LEN: u64 = 1 << 20;
fn owned_in_agg(t: &str) -> String { format!("`{}` is an owned value and cannot be stored in arrays or `Vec`s in this version (it can be a local, a parameter, a return value, a struct field or an enum payload; see docs/MEMORY.md section 3)", t) }

#[derive(Clone, Copy, PartialEq, Debug)]
enum Sym { Fn(usize), Struct(usize), Enum(usize), Mod }

enum Look { Found(Sym), NotFound, Reported }
enum VarRes { Found(usize, usize), NotVariant, Reported }

struct FnInfo { params: Vec<Ty>, ret: Ty, layer: Layer }
struct Local { slot: usize, ty: Ty, mutable: bool }

/// A resolved place: `via_ref` is `Some(mutable)` when the path goes through a reference.
struct PlaceInfo { place: HPlace, ty: Ty, root: String, mutable: bool, via_ref: Option<bool> }

struct Checker<'a> {
    /// Type-parameter bindings of the generic instantiation being checked.
    tenv: HashMap<String, Ty>,
    /// Set by `expr_base` so the expression is evaluated as the base of a field projection (no move out of it).
    base_ok_flag: bool,
    pending: Vec<(usize, Vec<Ty>, Span)>,
    instances: Vec<(usize, Vec<Ty>, usize)>,
    /// Generic struct/enum instantiations: (is_enum, template id, type args, instance id).
    agg_insts: Vec<(bool, usize, Vec<Ty>, usize)>,
    inst_of: HashMap<(bool, usize), (usize, Vec<Ty>)>,
    bad_templates: HashSet<(bool, usize)>,
    uses: HashMap<(String, String), (Vec<String>, Span)>,
    /// Associated functions and methods: (is_enum, type id, name) -> function id.
    assoc: HashMap<(bool, usize, String), usize>,
    assoc_pending: Vec<usize>,
    use_depth: u32,
    syms: HashMap<String, (Sym, bool)>,
    fn_asts: Vec<(&'a FnDecl, String)>,
    struct_asts: Vec<(&'a StructDecl, String)>,
    enum_asts: Vec<(&'a EnumDecl, String)>,
    fns: Vec<FnInfo>,
    structs: Vec<StructDef>,
    enums: Vec<EnumDef>,
    vars: Vec<Option<Ty>>,
    // per-function state
    module: String,
    scopes: Vec<HashMap<String, Local>>,
    nslots: usize,
    slot_tys: Vec<Ty>,
    slot_names: Vec<String>,
    layer: Layer,
    c_names: HashSet<String>,
    unsafe_depth: u32,
    loop_depth: u32,
    ret: Ty,
    fn_name: String,
    diags: Vec<Diag>,
}

fn join_path(m: &str, n: &str) -> String { if m.is_empty() { n.to_string() } else { format!("{}::{}", m, n) } }
fn parent_of(m: &str) -> String { m.rsplit_once("::").map(|x| x.0.to_string()).unwrap_or_default() }
fn within(cur: &str, base: &str) -> bool { base.is_empty() || cur == base || cur.starts_with(&format!("{}::", base)) }

fn opsym(op: BinOp) -> &'static str {
    use BinOp::*;
    match op {
        Add => "+", Sub => "-", Mul => "*", Div => "/", Rem => "%", Eq => "==", Ne => "!=", Lt => "<", Le => "<=",
        Gt => ">", Ge => ">=", And => "&&", Or => "||", BitAnd => "&", BitOr => "|", BitXor => "^", Shl => "<<", Shr => ">>",
    }
}

fn describe(e: &Expr) -> String {
    match &e.kind {
        ExprKind::Path(p) => p.text(),
        ExprKind::Field(b, f) => format!("{}.{}", describe(b), f),
        ExprKind::Index(b, _) => format!("{}[..]", describe(b)),
        _ => "<expression>".into(),
    }
}

pub fn check(p: &Program) -> Result<HProgram, Vec<Diag>> {
    let mut c = Checker {
        tenv: HashMap::new(), c_names: HashSet::new(), base_ok_flag: false, pending: vec![], instances: vec![], agg_insts: vec![], inst_of: HashMap::new(), bad_templates: HashSet::new(),
        uses: HashMap::new(), assoc: HashMap::new(), assoc_pending: vec![], use_depth: 0, syms: HashMap::new(), fn_asts: vec![], struct_asts: vec![], enum_asts: vec![],
        fns: vec![], structs: vec![], enums: vec![], vars: vec![],
        module: String::new(), scopes: vec![], nslots: 0, slot_tys: vec![], slot_names: vec![], layer: Layer::Application, unsafe_depth: 0, loop_depth: 0,
        ret: Ty::Unit, fn_name: String::new(), diags: vec![],
    };
    c.collect(&p.items, "");
    c.validate_uses();
    c.register_assoc();
    c.resolve_signatures();
    c.check_aggregate_ownership();
    c.check_type_cycles(0, 0);
    let (cyc_s, cyc_e) = (c.structs.len(), c.enums.len());
    let mut hfns = Vec::new();
    let fn_asts = c.fn_asts.clone();
    for (id, (f, m)) in fn_asts.iter().enumerate() {
        if !f.tparams.is_empty() {
            // generic templates are checked per instantiation; keep ids aligned with a placeholder
            if f.ext != Ext::None { c.check_ffi(f, id); }
            hfns.push(HFn { name: format!("{}<..>", f.name), layer: f.layer, ext: f.ext, nparams: 0, nslots: 0, slot_tys: vec![], slot_names: vec![], params: vec![], ret: Ty::Unit, body: HBlock { stmts: vec![], tail: None } });
            continue;
        }
        if f.ext == Ext::Import {
            // a C declaration: only the signature exists; there is no body to check or lower
            c.check_ffi(f, id);
            hfns.push(HFn { name: f.name.clone(), layer: f.layer, ext: f.ext, nparams: f.params.len(), nslots: f.params.len(), slot_tys: c.fns[id].params.clone(),
                slot_names: f.params.iter().map(|p| p.name.clone()).collect(), params: c.fns[id].params.clone(), ret: c.fns[id].ret.clone(), body: HBlock { stmts: vec![], tail: None } });
            continue;
        }
        if f.ext == Ext::Export { c.check_ffi(f, id); }
        let mut h = c.check_fn(f, id, m);
        c.zonk_fn(&mut h);
        hfns.push(h);
    }
    c.instantiate_all(&mut hfns);
    c.check_type_cycles(cyc_s, cyc_e);
    let main = match c.syms.get("main") {
        Some((Sym::Fn(id), _)) => {
            let id = *id;
            if !c.fns[id].params.is_empty() || c.fns[id].ret != Ty::Unit {
                c.err(c.fn_asts[id].0.span, "`main` must take no parameters and return nothing");
            }
            Some(id)
        }
        _ => None,
    };
    if !c.diags.is_empty() {
        let mut d = c.diags;
        d.sort_by_key(|d| (d.span.line, d.span.col));
        d.dedup();
        return Err(d);
    }
    let prog = HProgram { fns: hfns, structs: c.structs, enums: c.enums, main };
    let mut bd = crate::borrow::check(&prog);
    bd.extend(crate::moves::check(&prog));
    if !bd.is_empty() {
        bd.sort_by_key(|d| (d.span.line, d.span.col));
        bd.dedup();
        return Err(bd);
    }
    let mut prog = prog;
    crate::drops::elaborate(&mut prog);
    Ok(prog)
}

impl<'a> Checker<'a> {
    fn err(&mut self, span: Span, msg: impl Into<String>) { self.diags.push(Diag::new(span, msg)); }

    // ---------- items ----------

    fn collect(&mut self, items: &'a [Item], module: &str) {
        for it in items {
            if let Item::Use(u) = it {
                let key = (module.to_string(), u.alias.clone());
                if self.uses.contains_key(&key) || self.syms.contains_key(&join_path(module, &u.alias)) {
                    self.err(u.span, format!("`{}` is defined more than once in this module", u.alias));
                } else {
                    self.uses.insert(key, (u.path.segs.clone(), u.span));
                }
                continue;
            }
            if let Item::Fn(f) = it {
                if f.assoc.is_some() {
                    self.assoc_pending.push(self.fn_asts.len());
                    self.fn_asts.push((f, module.to_string()));
                    continue;
                }
            }
            let (name, public, span, kind) = match it {
                Item::Fn(f) => (&f.name, f.public, f.span, 0),
                Item::Struct(s) => (&s.name, s.public, s.span, 1),
                Item::Enum(e) => (&e.name, e.public, e.span, 2),
                Item::Mod(m) => (&m.name, m.public, m.span, 3),
                Item::Use(_) => unreachable!(),
            };
            let full = join_path(module, name);
            if kind == 0 && BUILTINS.contains(&name.as_str()) {
                self.err(span, format!("`{}` is a builtin and cannot be redefined", name));
                continue;
            }
            if self.syms.contains_key(&full) || self.uses.contains_key(&(module.to_string(), name.clone())) {
                self.err(span, format!("`{}` is defined more than once", full));
                continue;
            }
            match it {
                Item::Fn(f) => {
                    self.syms.insert(full, (Sym::Fn(self.fn_asts.len()), public));
                    self.fn_asts.push((f, module.to_string()));
                }
                Item::Struct(s) => {
                    self.syms.insert(full.clone(), (Sym::Struct(self.struct_asts.len()), public));
                    self.struct_asts.push((s, module.to_string()));
                    self.structs.push(StructDef { name: full, fields: vec![] });
                }
                Item::Enum(e) => {
                    self.syms.insert(full.clone(), (Sym::Enum(self.enum_asts.len()), public));
                    self.enum_asts.push((e, module.to_string()));
                    self.enums.push(EnumDef { name: full, variants: vec![] });
                }
                Item::Use(_) => unreachable!(),
                Item::Mod(m) => {
                    self.syms.insert(full.clone(), (Sym::Mod, public));
                    self.collect(&m.items, &full);
                }
            }
        }
    }

    fn resolve_signatures(&mut self) {
        // pass 1: validate generic templates once (type parameters stand for the error type, so only
        // errors that do not depend on the arguments are reported)
        for (id, (d, m)) in self.struct_asts.clone().into_iter().enumerate() {
            if d.tparams.is_empty() { continue; }
            let saved = std::mem::replace(&mut self.tenv, d.tparams.iter().map(|t| (t.clone(), Ty::Error)).collect());
            let nd = self.diags.len();
            let mut seen = HashSet::new();
            for (n, t, sp) in &d.fields {
                if !seen.insert(n.clone()) { self.err(*sp, format!("duplicate field `{}` in struct `{}`", n, d.name)); }
                self.resolve_ty(t, &m);
            }
            if self.diags.len() > nd { self.bad_templates.insert((false, id)); }
            self.tenv = saved;
        }
        for (id, (d, m)) in self.enum_asts.clone().into_iter().enumerate() {
            if d.tparams.is_empty() { continue; }
            let saved = std::mem::replace(&mut self.tenv, d.tparams.iter().map(|t| (t.clone(), Ty::Error)).collect());
            let nd = self.diags.len();
            let mut seen = HashSet::new();
            for (n, ts, sp) in &d.variants {
                if !seen.insert(n.clone()) { self.err(*sp, format!("duplicate variant `{}` in enum `{}`", n, d.name)); }
                for t in ts { self.resolve_ty(t, &m); }
            }
            if self.diags.len() > nd { self.bad_templates.insert((true, id)); }
            self.tenv = saved;
        }
        for (id, (d, m)) in self.struct_asts.clone().into_iter().enumerate() {
            if !d.tparams.is_empty() { continue; }
            let mut seen = HashSet::new();
            let mut fields = Vec::new();
            for (n, t, sp) in &d.fields {
                if !seen.insert(n.clone()) { self.err(*sp, format!("duplicate field `{}` in struct `{}`", n, d.name)); }
                let ft = self.resolve_ty(t, &m);
                fields.push((n.clone(), ft));
            }
            self.structs[id].fields = fields;
        }
        for (id, (d, m)) in self.enum_asts.clone().into_iter().enumerate() {
            if !d.tparams.is_empty() { continue; }
            let mut seen = HashSet::new();
            let mut variants = Vec::new();
            for (n, ts, sp) in &d.variants {
                if !seen.insert(n.clone()) { self.err(*sp, format!("duplicate variant `{}` in enum `{}`", n, d.name)); }
                let tys: Vec<Ty> = ts.iter().map(|t| self.resolve_ty(t, &m)).collect();
                variants.push((n.clone(), tys));
            }
            self.enums[id].variants = variants;
        }
        for (f, m) in self.fn_asts.clone() {
            if !f.tparams.is_empty() {
                let mut used = HashSet::new();
                for p in &f.params { Self::tparams_in(&p.ty, &mut used); }
                if let Some(r) = &f.ret { Self::tparams_in(r, &mut used); }
                for t in &f.tparams {
                    if !used.contains(t) { self.err(f.span, format!("type parameter `{}` of `{}` does not appear in a parameter or return type, so it cannot be inferred", t, f.name)); }
                }
                self.fns.push(FnInfo { params: vec![], ret: Ty::Unit, layer: f.layer });
                continue;
            }
            let params = f.params.iter().map(|p| self.resolve_ty_ref(&p.ty, &m)).collect();
            let ret = match &f.ret { Some(t) => self.resolve_ty(t, &m), None => Ty::Unit };
            self.fns.push(FnInfo { params, ret, layer: f.layer });
        }
    }

    /// After all struct/enum fields are known: owned aggregates may not be enum payloads or array elements.
    fn check_aggregate_ownership(&mut self) {
        fn arrays(t: &Ty, out: &mut Vec<Ty>) {
            if let Ty::Array(e, _) = t { out.push((**e).clone()); arrays(e, out); }
        }
        let mut errs: Vec<(Span, String)> = Vec::new();
        for (id, (d, _)) in self.struct_asts.clone().iter().enumerate() {
            if !d.tparams.is_empty() { continue; }
            for (fi, (_, t)) in self.structs[id].fields.iter().enumerate() {
                let mut els = Vec::new();
                arrays(t, &mut els);
                if let Some(e) = els.iter().find(|e| owned_ty(e, &self.structs, &self.enums)) { errs.push((d.fields[fi].2, owned_in_agg(&self.tname(e)))); }
            }
        }
        for (id, (d, _)) in self.enum_asts.clone().iter().enumerate() {
            if !d.tparams.is_empty() { continue; }
            for (vi, (_, ts)) in self.enums[id].variants.iter().enumerate() {
                for t in ts {
                    let mut els = vec![];
                    arrays(t, &mut els);
                    if let Some(e) = els.iter().find(|e| owned_ty(e, &self.structs, &self.enums)) { errs.push((d.variants[vi].2, owned_in_agg(&self.tname(e)))); break; }
                }
            }
        }
        for (sp, m) in errs { self.err(sp, m); }
    }

    fn deps(t: &Ty, out: &mut Vec<(bool, usize)>) {
        match t {
            Ty::Struct(i) => out.push((false, *i)),
            Ty::Enum(i) => out.push((true, *i)),
            Ty::Array(e, _) => Self::deps(e, out),
            _ => {}
        }
    }

    /// Reject types that contain themselves by value (infinite size).
    fn check_type_cycles(&mut self, s0: usize, e0: usize) {
        // state: 0 = unvisited, 1 = in progress, 2 = done; keyed by (is_enum, id)
        let mut state: HashMap<(bool, usize), u8> = HashMap::new();
        let mut errs = Vec::new();
        fn visit(c: &Checker, n: (bool, usize), state: &mut HashMap<(bool, usize), u8>, errs: &mut Vec<(Span, String)>) {
            match state.get(&n) {
                Some(1) => {
                    let (span, name) = if n.0 { (c.enum_asts[n.1].0.span, c.enums[n.1].name.clone()) } else { (c.struct_asts[n.1].0.span, c.structs[n.1].name.clone()) };
                    errs.push((span, format!("recursive type `{}` has infinite size", name)));
                    state.insert(n, 2);
                    return;
                }
                Some(2) => return,
                _ => {}
            }
            state.insert(n, 1);
            let mut ds = Vec::new();
            if n.0 { for (_, ts) in &c.enums[n.1].variants { for t in ts { Checker::deps(t, &mut ds); } } }
            else { for (_, t) in &c.structs[n.1].fields { Checker::deps(t, &mut ds); } }
            for d in ds { visit(c, d, state, errs); }
            if state.get(&n) == Some(&1) { state.insert(n, 2); }
        }
        for i in s0..self.structs.len() { visit(self, (false, i), &mut state, &mut errs); }
        for i in e0..self.enums.len() { visit(self, (true, i), &mut state, &mut errs); }
        for (s, m) in errs { self.err(s, m); }
    }

    /// Every `use` must name an existing, visible item.
    fn validate_uses(&mut self) {
        let mut us: Vec<((String, String), (Vec<String>, Span))> = self.uses.iter().map(|(k, v)| (k.clone(), v.clone())).collect();
        us.sort_by_key(|(_, (_, s))| (s.line, s.col));
        for ((m, name), (segs, span)) in us {
            // resolve the target without going through this very alias
            self.uses.remove(&(m.clone(), name.clone()));
            let r = self.lookup(&m, &segs, span);
            self.uses.insert((m.clone(), name.clone()), (segs.clone(), span));
            if let Look::NotFound = r { self.err(span, format!("unresolved import `{}`", segs.join("::"))); }
        }
    }

    // ---------- name lookup ----------

    fn lookup(&mut self, module: &str, segs: &[String], span: Span) -> Look {
        // `use` aliases: a first segment that names an import (and no local item) is replaced by the import's path.
        if !matches!(segs[0].as_str(), "crate" | "super") && !self.syms.contains_key(&join_path(module, &segs[0])) {
            if let Some((target, _)) = self.uses.get(&(module.to_string(), segs[0].clone())).cloned() {
                if self.use_depth > 16 { self.err(span, format!("import cycle through `{}`", segs[0])); return Look::Reported; }
                let mut full = target;
                full.extend_from_slice(&segs[1..]);
                self.use_depth += 1;
                let r = self.lookup(module, &full, span);
                self.use_depth -= 1;
                return r;
            }
        }
        let mut idx = 0;
        let mut base;
        match segs[0].as_str() {
            "crate" => { base = String::new(); idx = 1; }
            "super" => {
                base = module.to_string();
                while idx < segs.len() && segs[idx] == "super" {
                    if base.is_empty() { self.err(span, "`super` used at the crate root"); return Look::Reported; }
                    base = parent_of(&base);
                    idx += 1;
                }
            }
            _ => base = module.to_string(),
        }
        if idx >= segs.len() { return Look::Found(Sym::Mod); } // `crate` / `super` alone name a module
        for i in idx..segs.len() {
            let full = join_path(&base, &segs[i]);
            let (sym, public) = match self.syms.get(&full) { Some(x) => *x, None => return Look::NotFound };
            if !public && !within(module, &base) {
                self.err(span, format!("`{}` is private (add `pub` to expose it outside module `{}`)", full, base));
                return Look::Reported;
            }
            if i == segs.len() - 1 { return Look::Found(sym); }
            if sym != Sym::Mod { return Look::NotFound; }
            base = full;
        }
        Look::NotFound
    }

    fn resolve_ty(&mut self, t: &TyExpr, module: &str) -> Ty {
        match t {
            TyExpr::Named(p) => {
                if p.segs.len() == 1 {
                    let n = p.segs[0].as_str();
                    if let Some(t) = self.tenv.get(n) { return t.clone(); }
                    if let Some(i) = IntTy::from_name(n) { return Ty::Int(i); }
                    match n { "f64" => return Ty::Float, "bool" => return Ty::Bool, "str" => return Ty::Str, "String" => return Ty::String, _ => {} }
                }
                match self.lookup(module, &p.segs, p.span) {
                    Look::Found(Sym::Struct(i)) => {
                        let k = self.struct_asts[i].0.tparams.len();
                        if k == 0 { Ty::Struct(i) } else { self.err(p.span, format!("`{}` is generic; write it with {} type argument(s), e.g. `{}<..>`", p.text(), k, p.text())); Ty::Error }
                    }
                    Look::Found(Sym::Enum(i)) => {
                        let k = self.enum_asts[i].0.tparams.len();
                        if k == 0 { Ty::Enum(i) } else { self.err(p.span, format!("`{}` is generic; write it with {} type argument(s), e.g. `{}<..>`", p.text(), k, p.text())); Ty::Error }
                    }
                    Look::Found(_) => { self.err(p.span, format!("`{}` is not a type", p.text())); Ty::Error }
                    Look::NotFound => {
                        if p.segs.len() == 1 && p.segs[0] == "Vec" { self.err(p.span, "`Vec` needs an element type, e.g. `Vec<i64>`"); }
                        else { self.err(p.span, format!("unknown type `{}`", p.text())); }
                        Ty::Error
                    }
                    Look::Reported => Ty::Error,
                }
            }
            TyExpr::Generic(p, targs) => {
                let lk = self.lookup(module, &p.segs, p.span);
                if matches!(lk, Look::NotFound) && p.segs.len() == 1 && p.segs[0] == "Vec" {
                    if targs.len() != 1 { self.err(p.span, format!("`Vec` takes 1 type argument but {} were supplied", targs.len())); return Ty::Error; }
                    let e = self.resolve_ty(&targs[0], module);
                    return match self.resolve(&e) {
                        Ty::Error => Ty::Error,
                        Ty::Int(_) | Ty::Float | Ty::Bool => Ty::Vec(Box::new(e)),
                        o => { let m = format!("`Vec` elements must be integers, `f64` or `bool` in this version, found {} (aggregate and owned elements need drop glue; see docs/MEMORY.md section 3b)", self.tname(&o)); self.err(p.span, m); Ty::Error }
                    };
                }
                if matches!(lk, Look::NotFound) && p.segs.len() == 1 && p.segs[0] == "Box" {
                    if targs.len() != 1 { self.err(p.span, format!("`Box` takes 1 type argument but {} were supplied", targs.len())); return Ty::Error; }
                    let e = self.resolve_ty(&targs[0], module);
                    return match self.resolve(&e) {
                        Ty::Error => Ty::Error,
                        Ty::Ref(..) | Ty::Unit | Ty::Never => { let m = format!("`Box` cannot hold {} (references are second-class and `()`/`!` have no value to store)", self.tname(&e)); self.err(p.span, m); Ty::Error }
                        _ => Ty::Box(Box::new(e)),
                    };
                }
                let (is_enum, id) = match lk {
                    Look::Found(Sym::Struct(i)) => (false, i),
                    Look::Found(Sym::Enum(i)) => (true, i),
                    Look::Found(_) => { self.err(p.span, format!("`{}` is not a type", p.text())); return Ty::Error; }
                    Look::NotFound => { self.err(p.span, format!("unknown type `{}`", p.text())); return Ty::Error; }
                    Look::Reported => return Ty::Error,
                };
                let k = if is_enum { self.enum_asts[id].0.tparams.len() } else { self.struct_asts[id].0.tparams.len() };
                if k == 0 { self.err(p.span, format!("`{}` is not generic", p.text())); return Ty::Error; }
                if k != targs.len() { self.err(p.span, format!("`{}` takes {} type argument(s) but {} were supplied", p.text(), k, targs.len())); return Ty::Error; }
                let args: Vec<Ty> = targs.iter().map(|t| self.resolve_ty(t, module)).collect();
                self.instantiate_agg(is_enum, id, args, p.span)
            }
            TyExpr::Ref(_, _, sp) => {
                self.err(*sp, "references are only allowed as function parameter types and `let` annotations; they cannot be returned, nested or stored in structs, enums or arrays (see docs/MEMORY.md)");
                Ty::Error
            }
            TyExpr::Array(e, n, sp) => {
                let et = self.resolve_ty(e, module);
                if self.owned(&et) { let m = owned_in_agg(&self.tname(&et)); self.err(*sp, m); return Ty::Error; }
                if *n > MAX_ARRAY_LEN { self.err(*sp, format!("array length {} exceeds the M1 maximum of {}", n, MAX_ARRAY_LEN)); return Ty::Error; }
                Ty::Array(Box::new(et), *n as usize)
            }
        }
    }

    /// Instantiate generic struct/enum `tid` with concrete type arguments (monomorphization; one definition per
    /// distinct argument list, created on first use).
    fn instantiate_agg(&mut self, is_enum: bool, tid: usize, args: Vec<Ty>, span: Span) -> Ty {
        if args.iter().any(|a| matches!(self.resolve(a), Ty::Error)) { return Ty::Error; }
        let args: Vec<Ty> = args.iter().map(|a| self.fin(a)).collect();
        if let Some((_, _, _, id)) = self.agg_insts.iter().find(|(e, t, a, _)| *e == is_enum && *t == tid && *a == args) {
            return if is_enum { Ty::Enum(*id) } else { Ty::Struct(*id) };
        }
        if self.agg_insts.len() >= MAX_INSTANCES {
            self.err(span, format!("too many generic type instantiations (limit {}); possible polymorphic recursion", MAX_INSTANCES));
            return Ty::Error;
        }
        let base = if is_enum { self.enums[tid].name.clone() } else { self.structs[tid].name.clone() };
        let name = format!("{}<{}>", base, args.iter().map(|t| self.tname(t)).collect::<Vec<_>>().join(", "));
        let id;
        if is_enum {
            let (d, m) = self.enum_asts[tid].clone();
            id = self.enums.len();
            self.enums.push(EnumDef { name: name.clone(), variants: vec![] });
            self.enum_asts.push((d, m));
        } else {
            let (d, m) = self.struct_asts[tid].clone();
            id = self.structs.len();
            self.structs.push(StructDef { name: name.clone(), fields: vec![] });
            self.struct_asts.push((d, m));
        }
        self.agg_insts.push((is_enum, tid, args.clone(), id));
        self.inst_of.insert((is_enum, id), (tid, args.clone()));
        let nd = self.diags.len();
        if is_enum {
            let (d, m) = self.enum_asts[tid].clone();
            let saved = std::mem::replace(&mut self.tenv, d.tparams.iter().cloned().zip(args.iter().cloned()).collect());
            let mut variants = Vec::new();
            for (n, ts, _) in &d.variants {
                let tys: Vec<Ty> = ts.iter().map(|t| self.resolve_ty(t, &m)).collect();
                variants.push((n.clone(), tys));
            }
            self.tenv = saved;
            self.enums[id].variants = variants;
        } else {
            let (d, m) = self.struct_asts[tid].clone();
            let saved = std::mem::replace(&mut self.tenv, d.tparams.iter().cloned().zip(args.iter().cloned()).collect());
            let mut fields = Vec::new();
            for (n, t, _) in &d.fields {
                let ft = self.resolve_ty(t, &m);
                fields.push((n.clone(), ft));
            }
            self.tenv = saved;
            self.structs[id].fields = fields;
        }
        if self.bad_templates.contains(&(is_enum, tid)) { self.diags.truncate(nd); }
        if is_enum { Ty::Enum(id) } else { Ty::Struct(id) }
    }

    /// The instance of generic aggregate `tid` named by an expected type, if any.
    fn hinted_inst(&mut self, is_enum: bool, tid: usize, hint: &Option<Ty>) -> Option<usize> {
        let h = self.resolve(hint.as_ref()?);
        let id = match (is_enum, h) { (false, Ty::Struct(i)) | (true, Ty::Enum(i)) => i, _ => return None };
        match self.inst_of.get(&(is_enum, id)) { Some((t, _)) if *t == tid => Some(id), _ => None }
    }

    /// Infer the type arguments of generic aggregate `tid` from checked constructor operands.
    fn infer_inst(&mut self, is_enum: bool, tid: usize, pairs: &[(&TyExpr, Ty, Span)], what: &str, span: Span) -> Option<usize> {
        let (tps, gm, aname) = if is_enum {
            (self.enum_asts[tid].0.tparams.clone(), self.enum_asts[tid].1.clone(), self.enums[tid].name.clone())
        } else {
            (self.struct_asts[tid].0.tparams.clone(), self.struct_asts[tid].1.clone(), self.structs[tid].name.clone())
        };
        let mut bind: Vec<Option<Ty>> = vec![None; tps.len()];
        let errs = self.diags.len();
        for (te, ty, sp) in pairs { self.match_ty(te, ty, &tps, &mut bind, &gm, *sp); }
        if self.diags.len() > errs { return None; }
        if let Some(i) = bind.iter().position(|b| b.is_none()) {
            self.err(span, format!("cannot infer type parameter `{}` of `{}`; add a type annotation such as `let x: {}<..> = ...`", tps[i], what, aname));
            return None;
        }
        let args: Vec<Ty> = bind.into_iter().map(|b| b.unwrap()).collect();
        match self.instantiate_agg(is_enum, tid, args, span) {
            Ty::Struct(i) | Ty::Enum(i) => Some(i),
            _ => None,
        }
    }

    /// Like `resolve_ty` but also accepts a top-level reference type (parameters and `let` annotations).
    fn resolve_ty_ref(&mut self, t: &TyExpr, module: &str) -> Ty {
        match t {
            TyExpr::Ref(inner, m, _) => {
                let it = self.resolve_ty(inner, module);
                if it == Ty::Error { Ty::Error } else { Ty::Ref(Box::new(it), *m) }
            }
            _ => self.resolve_ty(t, module),
        }
    }

    fn resolve_variant(&mut self, p: &Path) -> VarRes {
        let n = p.segs.len();
        if n < 2 { return VarRes::NotVariant; }
        let m = self.module.clone();
        match self.lookup(&m, &p.segs[..n - 1], p.span) {
            Look::Found(Sym::Enum(id)) => {
                match self.enum_asts[id].0.variants.iter().position(|(vn, _, _)| *vn == p.segs[n - 1]) {
                    Some(i) => VarRes::Found(id, i),
                    None => {
                        let m = format!("enum `{}` has no variant `{}`", self.enums[id].name, p.segs[n - 1]);
                        self.err(p.span, m);
                        VarRes::Reported
                    }
                }
            }
            Look::Reported => VarRes::Reported,
            _ => VarRes::NotVariant,
        }
    }

    // ---------- types ----------

    fn new_var(&mut self) -> Ty { self.vars.push(None); Ty::Var((self.vars.len() - 1) as u32) }

    fn resolve(&self, t: &Ty) -> Ty {
        let mut cur = t.clone();
        while let Ty::Var(v) = cur {
            match &self.vars[v as usize] { Some(n) => cur = n.clone(), None => break }
        }
        cur
    }

    fn tname(&self, t: &Ty) -> String {
        match self.resolve(t) {
            Ty::Int(i) => i.name().into(),
            Ty::Float => "f64".into(), Ty::Bool => "bool".into(), Ty::Str => "str".into(),
            Ty::Unit => "()".into(), Ty::Never => "!".into(), Ty::Error => "<error>".into(),
            Ty::Var(_) => "i64".into(),
            Ty::Struct(i) => self.structs[i].name.clone(),
            Ty::Enum(i) => self.enums[i].name.clone(),
            Ty::Array(e, n) => format!("[{}; {}]", self.tname(&e), n),
            Ty::Ref(t, m) => format!("&{}{}", if m { "mut " } else { "" }, self.tname(&t)),
            Ty::String => "String".into(),
            Ty::Vec(e) => format!("Vec<{}>", self.tname(&e)),
            Ty::Box(e) => format!("Box<{}>", self.tname(&e)),
        }
    }

    fn unify(&mut self, a: &Ty, b: &Ty) -> bool {
        let (a, b) = (self.resolve(a), self.resolve(b));
        match (a, b) {
            (Ty::Var(x), Ty::Var(y)) => { if x != y { self.vars[x as usize] = Some(Ty::Var(y)); } true }
            (Ty::Var(x), Ty::Int(k)) | (Ty::Int(k), Ty::Var(x)) => { self.vars[x as usize] = Some(Ty::Int(k)); true }
            (Ty::Var(_), _) | (_, Ty::Var(_)) => false,
            (Ty::Array(t1, n1), Ty::Array(t2, n2)) => n1 == n2 && self.unify(&t1, &t2),
            (Ty::Ref(t1, m1), Ty::Ref(t2, m2)) => m1 == m2 && self.unify(&t1, &t2),
            (Ty::Vec(t1), Ty::Vec(t2)) | (Ty::Box(t1), Ty::Box(t2)) => self.unify(&t1, &t2),
            (a, b) => a == b,
        }
    }

    /// Unify, treating `!` and the error type as compatible with everything.
    fn compat(&mut self, a: &Ty, b: &Ty) -> bool {
        let (ra, rb) = (self.resolve(a), self.resolve(b));
        if matches!(ra, Ty::Never | Ty::Error) || matches!(rb, Ty::Never | Ty::Error) { return true; }
        self.unify(&ra, &rb)
    }

    fn owned(&self, t: &Ty) -> bool { owned_ty(&self.resolve(t), &self.structs, &self.enums) }

    /// Evaluate `e` as the base of a field projection: an owned local is read in place, not moved.
    fn expr_base(&mut self, e: &Expr) -> HExpr { self.base_ok_flag = true; self.expr_any(e) }

    fn place_like(h: &HExpr) -> bool {
        match &h.kind { HKind::Local(_) | HKind::Move(_) => true, HKind::Field(b, _) | HKind::Deref(b) => Self::place_like(b), _ => false }
    }

    fn is_int(&self, t: &Ty) -> bool { matches!(self.resolve(t), Ty::Int(_) | Ty::Var(_)) }
    fn is_num(&self, t: &Ty) -> bool { matches!(self.resolve(t), Ty::Int(_) | Ty::Var(_) | Ty::Float) }
    fn is_scalar(&self, t: &Ty) -> bool { matches!(self.resolve(t), Ty::Int(_) | Ty::Var(_) | Ty::Float | Ty::Bool | Ty::Str) }
    fn is_bad(&self, t: &Ty) -> bool { matches!(self.resolve(t), Ty::Error) }

    // ---------- functions and blocks ----------

    fn lookup_local(&self, n: &str) -> Option<(usize, Ty, bool)> {
        self.scopes.iter().rev().find_map(|s| s.get(n)).map(|l| (l.slot, l.ty.clone(), l.mutable))
    }

    fn declare(&mut self, name: &str, ty: Ty, mutable: bool) -> usize {
        let slot = self.nslots;
        self.nslots += 1;
        self.slot_tys.push(ty.clone());
        self.slot_names.push(name.to_string());
        self.scopes.last_mut().unwrap().insert(name.to_string(), Local { slot, ty, mutable });
        slot
    }

    fn check_fn(&mut self, f: &FnDecl, id: usize, module: &str) -> HFn {
        self.module = module.to_string();
        self.layer = f.layer;
        self.unsafe_depth = 0;
        self.ret = self.fns[id].ret.clone();
        self.fn_name = f.name.clone();
        self.nslots = 0;
        self.slot_tys.clear();
        self.slot_names.clear();
        self.scopes = vec![HashMap::new()];
        let mut seen = HashSet::new();
        for (i, p) in f.params.iter().enumerate() {
            if !seen.insert(p.name.clone()) { self.err(p.span, format!("duplicate parameter `{}`", p.name)); }
            let t = self.fns[id].params[i].clone();
            self.declare(&p.name, t, false);
        }
        let ret = self.ret.clone();
        let (body, t) = self.block_h(&f.body, Some(ret.clone()));
        if !self.compat(&t, &ret) {
            let m = format!("function `{}` must evaluate to {} but its body evaluates to {}", f.name, self.tname(&ret), self.tname(&t));
            self.err(f.body.span, m);
        }
        self.scopes.clear();
        HFn { name: f.name.clone(), layer: f.layer, ext: f.ext, nparams: f.params.len(), nslots: self.nslots, slot_tys: self.slot_tys.clone(), slot_names: self.slot_names.clone(), params: self.fns[id].params.clone(), ret: self.fns[id].ret.clone(), body }
    }

    fn block(&mut self, b: &Block) -> (HBlock, Ty) { self.block_h(b, None) }

    fn block_h(&mut self, b: &Block, hint: Option<Ty>) -> (HBlock, Ty) {
        self.scopes.push(HashMap::new());
        let mut stmts = Vec::new();
        let mut diverges = false;
        for s in &b.stmts {
            let (hs, d) = self.stmt(s);
            if d { diverges = true; }
            stmts.extend(hs);
        }
        let (tail, t) = match &b.tail {
            Some(e) => { let h = self.expr_h(e, hint); let t = h.ty.clone(); (Some(Box::new(h)), t) }
            None if diverges => (None, Ty::Never),
            None => (None, Ty::Unit),
        };
        self.scopes.pop();
        (HBlock { stmts, tail }, t)
    }

    fn require_not_declarative(&mut self, span: Span, what: &str) {
        if self.layer == Layer::Declarative {
            self.err(span, format!("{} is not permitted in @layer(declarative)", what));
        }
    }

    /// Returns the lowered statement(s) and whether the statement diverges.
    fn stmt(&mut self, s: &Stmt) -> (Vec<HStmt>, bool) {
        match s {
            Stmt::Let { name, mutable, ty, init, span } => {
                if *mutable { self.require_not_declarative(*span, "mutable binding"); }
                let m = self.module.clone();
                let declared = ty.as_ref().map(|t| self.resolve_ty_ref(t, &m));
                let mut h = self.expr_any_h(init, declared.clone());
                let t = self.resolve(&h.ty);
                if let Ty::Ref(..) = t {
                    if *mutable { self.err(*span, format!("reference binding `{}` cannot be `mut` (references are bound once; write through them with `*{} = ...`)", name, name)); }
                    if !matches!(h.kind, HKind::AddrOf(..)) {
                        self.err(init.span, "a reference variable must be initialised with `&place` or `&mut place` (to re-borrow another reference write `&*r` or `&mut *r`)");
                    }
                }
                let vt = match declared {
                    Some(a) => {
                        self.coerce_ref(&mut h, &a);
                        if !self.compat(&h.ty, &a) {
                            let msg = format!("mismatched types: `{}` is declared {} but initializer is {}", name, self.tname(&a), self.tname(&h.ty));
                            self.err(init.span, msg);
                        }
                        a
                    }
                    None => match t {
                        Ty::Unit => { self.err(init.span, format!("cannot bind `{}` to a value of type ()", name)); Ty::Error }
                        Ty::Never => { self.err(init.span, format!("cannot bind `{}` to a diverging expression", name)); Ty::Error }
                        _ => h.ty.clone(),
                    },
                };
                let div = t == Ty::Never;
                let slot = self.declare(name, vt, *mutable);
                (vec![HStmt::Let(slot, h)], div)
            }
            Stmt::Assign { target, value, span } => {
                self.require_not_declarative(*span, "assignment");
                if let ExprKind::Index(b, i) = &target.kind {
                    if let Some(a) = self.vec_operand(b, true) {
                        let a = match a { Some(a) => a, None => { self.expr(i); self.expr(value); return (vec![], false); } };
                        let elem = match self.resolve(&a.ty) { Ty::Ref(inner, _) => match *inner { Ty::Vec(e) => Some(*e), _ => None }, _ => None };
                        let ih = self.expr(i);
                        let vh = self.expr_h(value, elem);
                        // evaluate index and value into hidden locals first so `v[0] = v[1] + 1` does not read `v`
                        // while the `&mut v` operand of the builtin is live
                        self.scopes.push(HashMap::new());
                        let (it, vt, ispan, vspan) = (ih.ty.clone(), vh.ty.clone(), ih.span, vh.span);
                        let (si, sv) = (self.declare("$vi", it.clone(), false), self.declare("$vv", vt.clone(), false));
                        let call = self.builtin("vec_set", vec![a, Self::h(HKind::Local(si), it, ispan), Self::h(HKind::Local(sv), vt, vspan)], *span, &None);
                        self.scopes.pop();
                        let div = self.resolve(&call.ty) == Ty::Never;
                        let inner = HBlock { stmts: vec![HStmt::Let(si, ih), HStmt::Let(sv, vh), HStmt::Expr(call)], tail: None };
                        return (vec![HStmt::Expr(Self::h(HKind::Block(inner), Ty::Unit, *span))], div);
                    }
                }
                let pl = self.place(target);
                let vh = self.expr_h(value, pl.as_ref().map(|x| x.ty.clone()));
                let div = self.resolve(&vh.ty) == Ty::Never;
                if let Some(PlaceInfo { place, ty: pty, root, mutable: root_mut, via_ref }) = pl {
                    if matches!(self.resolve(&pty), Ty::Ref(..)) {
                        self.err(*span, format!("cannot assign to the reference binding `{}` (reference bindings are fixed; write through it with `*{} = ...`)", root, root));
                    } else if !root_mut {
                        if via_ref == Some(false) {
                            self.err(*span, format!("cannot assign through the shared reference `{}` (use a `&mut` reference)", root));
                        } else if place.proj.is_empty() {
                            self.err(*span, format!("cannot assign twice to immutable variable `{}` (declare it with `let mut`)", root));
                        } else {
                            self.err(*span, format!("cannot assign through immutable variable `{}` (declare it with `let mut`)", root));
                        }
                    }
                    if !self.compat(&vh.ty, &pty) {
                        let m = format!("mismatched types: `{}` is {} but assigned {}", describe(target), self.tname(&pty), self.tname(&vh.ty));
                        self.err(value.span, m);
                    }
                    (vec![HStmt::Assign(place, vh)], div)
                } else {
                    (vec![], div)
                }
            }
            Stmt::Expr(e) => { let h = self.expr(e); let d = self.resolve(&h.ty) == Ty::Never; (vec![HStmt::Expr(h)], d) }
            Stmt::While { cond, body, span } => {
                self.require_not_declarative(*span, "`while` loop");
                let c = self.expr(cond);
                if !self.compat(&c.ty, &Ty::Bool) {
                    let m = format!("`while` condition must be bool, found {}", self.tname(&c.ty));
                    self.err(cond.span, m);
                }
                self.loop_depth += 1;
                let (b, _) = self.block(body);
                self.loop_depth -= 1;
                (vec![HStmt::While(c, b)], false)
            }
            Stmt::Break { span } | Stmt::Continue { span } => {
                let is_break = matches!(s, Stmt::Break { .. });
                if self.loop_depth == 0 {
                    self.err(*span, format!("`{}` outside of a loop", if is_break { "break" } else { "continue" }));
                }
                (vec![if is_break { HStmt::Break } else { HStmt::Continue }], true)
            }
            Stmt::Return { value, span } => {
                let rh = Some(self.ret.clone());
                let h = value.as_ref().map(|e| self.expr_h(e, rh));
                let t = h.as_ref().map(|h| h.ty.clone()).unwrap_or(Ty::Unit);
                let ret = self.ret.clone();
                if !self.compat(&t, &ret) {
                    let m = format!("mismatched types: `{}` returns {} but this returns {}", self.fn_name, self.tname(&ret), self.tname(&t));
                    self.err(value.as_ref().map(|e| e.span).unwrap_or(*span), m);
                }
                (vec![HStmt::Return(h)], true)
            }
        }
    }

    /// Resolve a place expression (assignment target or borrow operand).
    /// `v[i]` sugar on a `Vec` variable (or a reference to one): the `&Vec` / `&mut Vec` operand for the builtin.
    /// Outer `None`: the base is not a Vec variable (ordinary indexing). `Some(None)`: error already reported.
    fn vec_operand(&mut self, b: &Expr, mutable: bool) -> Option<Option<HExpr>> {
        if let ExprKind::Field(..) = &b.kind {
            // a field of a struct (possibly through a reference): borrow the field place
            let n0 = self.diags.len();
            let pi = self.place(b)?;
            let ty = self.resolve(&pi.ty);
            if !matches!(ty, Ty::Vec(_)) { self.diags.truncate(n0); return None; }
            if mutable && !pi.mutable {
                if pi.via_ref == Some(false) { self.err(b.span, format!("cannot assign through the shared reference `{}` (use a `&mut` reference)", pi.root)); }
                else { self.err(b.span, format!("cannot borrow `{}` as mutable (declare it with `let mut`)", pi.root)); }
                return Some(None);
            }
            return Some(Some(Self::h(HKind::AddrOf(pi.place, mutable), Ty::Ref(Box::new(ty), mutable), b.span)));
        }
        let name = match &b.kind { ExprKind::Path(p) if p.segs.len() == 1 => p.segs[0].clone(), _ => return None };
        let (slot, ty, is_mut) = self.lookup_local(&name)?;
        let ty = self.resolve(&ty);
        match &ty {
            Ty::Vec(_) => {
                if mutable && !is_mut {
                    self.err(b.span, format!("cannot borrow `{}` as mutable (declare it with `let mut`)", name));
                    return Some(None);
                }
                let place = HPlace { root: slot, proj: vec![] };
                Some(Some(Self::h(HKind::AddrOf(place, mutable), Ty::Ref(Box::new(ty.clone()), mutable), b.span)))
            }
            Ty::Ref(inner, m) if matches!(**inner, Ty::Vec(_)) => {
                if mutable && !*m {
                    self.err(b.span, format!("cannot assign through the shared reference `{}` (use a `&mut` reference)", name));
                    return Some(None);
                }
                Some(Some(Self::h(HKind::Local(slot), ty.clone(), b.span)))
            }
            _ => None,
        }
    }

    fn place(&mut self, e: &Expr) -> Option<PlaceInfo> {
        match &e.kind {
            ExprKind::Path(p) if p.segs.len() == 1 => match self.lookup_local(&p.segs[0]) {
                Some((slot, ty, m)) => Some(PlaceInfo { place: HPlace { root: slot, proj: vec![] }, ty, root: p.segs[0].clone(), mutable: m, via_ref: None }),
                None => { self.err(e.span, format!("cannot assign to undefined variable `{}`", p.segs[0])); None }
            },
            ExprKind::Deref(inner) => {
                let mut pi = self.place(inner)?;
                match self.resolve(&pi.ty) {
                    Ty::Ref(t, m) if pi.place.proj.is_empty() => {
                        pi.place.proj.push(Proj::Deref);
                        pi.ty = *t; pi.mutable = m; pi.via_ref = Some(m);
                        Some(pi)
                    }
                    Ty::Error => None,
                    t => { let msg = format!("cannot dereference a value of type {}", self.tname(&t)); self.err(e.span, msg); None }
                }
            }
            ExprKind::Field(base, f) => {
                let mut pi = self.place(base)?;
                self.auto_deref_place(&mut pi);
                match self.resolve(&pi.ty) {
                    Ty::Struct(id) => match self.structs[id].fields.iter().position(|(n, _)| n == f) {
                        Some(i) => { pi.ty = self.structs[id].fields[i].1.clone(); pi.place.proj.push(Proj::Field(i)); Some(pi) }
                        None => { let msg = format!("no field `{}` on type `{}`", f, self.structs[id].name); self.err(e.span, msg); None }
                    },
                    Ty::Error => None,
                    _ => { let msg = format!("type {} has no fields", self.tname(&pi.ty)); self.err(e.span, msg); None }
                }
            }
            ExprKind::Index(base, idx) => {
                let mut pi = self.place(base)?;
                self.auto_deref_place(&mut pi);
                let ih = self.expr(idx);
                match self.resolve(&pi.ty) {
                    Ty::Array(et, n) => {
                        self.check_index(&ih, n);
                        pi.place.proj.push(Proj::Index(ih));
                        pi.ty = *et;
                        Some(pi)
                    }
                    Ty::Error => None,
                    _ => { let msg = format!("cannot index into a value of type {}", self.tname(&pi.ty)); self.err(e.span, msg); None }
                }
            }
            _ => { self.err(e.span, "invalid assignment target"); None }
        }
    }

    /// `r.f` / `r[i]` where `r` is a reference local: continue through its referent.
    fn auto_deref_place(&mut self, pi: &mut PlaceInfo) {
        if let Ty::Ref(t, m) = self.resolve(&pi.ty) {
            if pi.place.proj.is_empty() {
                pi.place.proj.push(Proj::Deref);
                pi.ty = *t; pi.mutable = m; pi.via_ref = Some(m);
            }
        }
    }

    /// Value-level auto-deref for field/index/`len` bases: a reference local becomes `*local`.
    fn autoderef(&mut self, h: HExpr, span: Span) -> HExpr {
        match self.resolve(&h.ty) {
            Ty::Ref(inner, _) => {
                if matches!(h.kind, HKind::Local(_)) {
                    HExpr { kind: HKind::Deref(Box::new(h)), ty: *inner, span }
                } else {
                    self.err(span, "only a reference variable can be dereferenced implicitly (write `*r` or bind the reference to a variable)");
                    Self::bad(span)
                }
            }
            _ => h,
        }
    }

    /// `&mut T` may be used where `&T` is expected: retag the expression (the runtime representation is identical).
    fn coerce_ref(&mut self, h: &mut HExpr, want: &Ty) {
        if let (Ty::Ref(g, true), Ty::Ref(w, false)) = (self.resolve(&h.ty), self.resolve(want)) {
            if self.unify(&g, &w) { h.ty = want.clone(); }
        }
    }

    fn check_index(&mut self, idx: &HExpr, len: usize) {
        if !self.is_int(&idx.ty) && !matches!(self.resolve(&idx.ty), Ty::Error | Ty::Never) {
            let m = format!("array index must be an integer, found {}", self.tname(&idx.ty));
            self.err(idx.span, m);
        }
        if let HKind::Lit(Value::Int(v)) = &idx.kind {
            if *v < 0 || *v >= len as i128 {
                self.err(idx.span, format!("index {} is out of bounds for an array of length {}", v, len));
            }
        }
    }

    // ---------- expressions ----------

    /// A local variable or a field chain of one: evaluating it has no effect and cannot fail.
    fn pure_place(e: &HExpr) -> bool {
        match &e.kind { HKind::Local(_) => true, HKind::Field(b, _) | HKind::Deref(b) => Self::pure_place(b), _ => false }
    }

    fn h(kind: HKind, ty: Ty, span: Span) -> HExpr { HExpr { kind, ty, span } }
    fn bad(span: Span) -> HExpr { HExpr { kind: HKind::Lit(Value::Unit), ty: Ty::Error, span } }

    fn join(&mut self, a: Ty, b: Ty, span: Span, what: &str) -> Ty {
        let (ra, rb) = (self.resolve(&a), self.resolve(&b));
        match (ra, rb) {
            (Ty::Never, x) | (x, Ty::Never) => x,
            (Ty::Error, _) | (_, Ty::Error) => Ty::Error,
            (x, y) => {
                if self.unify(&x, &y) { x } else {
                    let m = format!("{} have different types: {} and {}", what, self.tname(&x), self.tname(&y));
                    self.err(span, m);
                    Ty::Error
                }
            }
        }
    }

    /// Expression in *value* context: references may not appear here (they are second-class).
    fn expr(&mut self, e: &Expr) -> HExpr { self.expr_h(e, None) }

    /// `expr` with an expected type, used only to pick the instance of a generic struct/enum constructor.
    fn expr_h(&mut self, e: &Expr, hint: Option<Ty>) -> HExpr {
        let h = self.expr_any_h(e, hint);
        if matches!(self.resolve(&h.ty), Ty::Ref(..)) {
            self.err(e.span, "a reference cannot be used as a value here; dereference it with `*` (references can only be passed as call arguments, bound with `let`, or auto-dereferenced by `.`, `[]` and `len`)");
            return Self::bad(e.span);
        }
        h
    }

    /// Expression where a reference-typed result is permitted (call arguments, `let` initialisers, deref/projection bases).
    fn expr_any(&mut self, e: &Expr) -> HExpr { self.expr_any_h(e, None) }

    fn expr_any_h(&mut self, e: &Expr, hint: Option<Ty>) -> HExpr {
        let base_ok = std::mem::take(&mut self.base_ok_flag);
        let span = e.span;
        match &e.kind {
            ExprKind::Int(v) => { let t = self.new_var(); Self::h(HKind::Lit(Value::Int(*v as i128)), t, span) }
            ExprKind::Float(v) => Self::h(HKind::Lit(Value::Float(*v)), Ty::Float, span),
            ExprKind::Bool(v) => Self::h(HKind::Lit(Value::Bool(*v)), Ty::Bool, span),
            ExprKind::Str(s) => Self::h(HKind::Lit(Value::Str(s.clone())), Ty::Str, span),
            ExprKind::Path(p) => {
                if p.segs.len() == 1 {
                    if let Some((slot, ty, _)) = self.lookup_local(&p.segs[0]) {
                        if self.owned(&ty) && !base_ok { return Self::h(HKind::Move(slot), ty, span); }
                        return Self::h(HKind::Local(slot), ty, span);
                    }
                }
                match self.resolve_variant(p) {
                    VarRes::Found(eid, vi) => {
                        let n = self.enum_asts[eid].0.variants[vi].1.len();
                        if n != 0 {
                            self.err(span, format!("variant `{}` takes {} field(s); construct it like a function call", p.text(), n));
                            return Self::bad(span);
                        }
                        let mut eid = eid;
                        if !self.enum_asts[eid].0.tparams.is_empty() {
                            eid = match self.hinted_inst(true, eid, &hint) {
                                Some(i) => i,
                                None => match self.infer_inst(true, eid, &[], &p.text(), span) { Some(i) => i, None => return Self::bad(span) },
                            };
                        }
                        Self::h(HKind::Variant(vi as u32, vec![]), Ty::Enum(eid), span)
                    }
                    VarRes::Reported => Self::bad(span),
                    VarRes::NotVariant => {
                        if p.segs.len() == 1 { self.err(span, format!("undefined variable `{}`", p.segs[0])); }
                        else { self.err(span, format!("undefined name `{}`", p.text())); }
                        Self::bad(span)
                    }
                }
            }
            ExprKind::Unary(op, x) => {
                if let (UnOp::Neg, ExprKind::Int(v)) = (op, &x.kind) {
                    let t = self.new_var();
                    return Self::h(HKind::Lit(Value::Int(-(*v as i128))), t, span);
                }
                let h = self.expr(x);
                let t = self.resolve(&h.ty);
                let rt = match (op, &t) {
                    (_, Ty::Error) => Ty::Error,
                    (UnOp::Neg, Ty::Float) => Ty::Float,
                    (UnOp::Neg, Ty::Var(_)) => t.clone(),
                    (UnOp::Neg, Ty::Int(k)) if k.signed() => t.clone(),
                    (UnOp::Not, Ty::Bool) => Ty::Bool,
                    (UnOp::Neg, _) => { let m = format!("cannot negate {}", self.tname(&t)); self.err(span, m); Ty::Error }
                    (UnOp::Not, _) => { let m = format!("`!` requires bool, found {}", self.tname(&t)); self.err(span, m); Ty::Error }
                };
                Self::h(HKind::Unary(*op, Box::new(h)), rt, span)
            }
            ExprKind::Binary(op, l, r) => self.binary(*op, l, r, span),
            ExprKind::Call(p, args) => self.call(p, args, span, hint),
            ExprKind::MethodCall(r, name, args) => self.method_call(r, name, args, span, hint),
            ExprKind::If(c, then, els) => {
                let ch = self.expr(c);
                if !self.compat(&ch.ty, &Ty::Bool) {
                    let m = format!("`if` condition must be bool, found {}", self.tname(&ch.ty));
                    self.err(c.span, m);
                }
                let (tb, tt) = self.block_h(then, hint.clone());
                match els {
                    Some(b) => {
                        let (eb, et) = self.block_h(b, hint.clone());
                        let t = self.join(tt, et, span, "`if` branches");
                        Self::h(HKind::If(Box::new(ch), tb, Some(eb)), t, span)
                    }
                    None => {
                        if !self.compat(&tt, &Ty::Unit) {
                            let m = format!("`if` without `else` must evaluate to (), but its body evaluates to {}", self.tname(&tt));
                            self.err(span, m);
                        }
                        Self::h(HKind::If(Box::new(ch), tb, None), Ty::Unit, span)
                    }
                }
            }
            ExprKind::Block(b) => { let (hb, t) = self.block_h(b, hint.clone()); Self::h(HKind::Block(hb), t, span) }
            ExprKind::Unsafe(b) => {
                if self.layer != Layer::Hardware {
                    self.err(span, format!("`unsafe` blocks are only permitted in @layer(hardware) (this function is in @layer({}))", self.layer.name()));
                }
                self.unsafe_depth += 1;
                let (hb, t) = self.block(b);
                self.unsafe_depth -= 1;
                Self::h(HKind::Block(hb), t, span)
            }
            ExprKind::Cast(x, te) => {
                let h = self.expr(x);
                let m = self.module.clone();
                let to = self.resolve_ty(te, &m);
                let from = self.resolve(&h.ty);
                let ok = match (&from, &to) {
                    (Ty::Error, _) | (_, Ty::Error) => true,
                    (f, t) if self.is_num(f) && self.is_num(t) => true,
                    (Ty::Bool, t) if self.is_int(t) => true,
                    _ => false,
                };
                if !ok {
                    let msg = format!("cannot cast {} to {}", self.tname(&from), self.tname(&to));
                    self.err(span, msg);
                }
                Self::h(HKind::Cast(Box::new(h)), to, span)
            }
            ExprKind::StructLit(p, fields) => self.struct_lit(p, fields, span, hint),
            ExprKind::Field(b, f) => {
                let bh0 = self.expr_base(b);
                let bh = self.autoderef(bh0, b.span);
                if self.owned(&bh.ty) && !Self::place_like(&bh) {
                    self.err(b.span, "cannot read a field of a temporary owned value (its other fields would never be dropped); bind it with `let` first");
                    return Self::bad(span);
                }
                match self.resolve(&bh.ty) {
                    Ty::Struct(id) => match self.structs[id].fields.iter().position(|(n, _)| n == f) {
                        Some(i) => {
                            let ft = self.structs[id].fields[i].1.clone();
                            if !base_ok && self.owned(&ft) {
                                self.err(span, format!("cannot move the owned field `{}` out of its struct; borrow it (`&{}`) or copy it with `{}_clone(&{})`", f, describe(e), if self.resolve(&ft) == Ty::String { "string" } else { "vec" }, describe(e)));
                                return Self::bad(span);
                            }
                            Self::h(HKind::Field(Box::new(bh), i), ft, span)
                        }
                        None => { let m = format!("no field `{}` on type `{}`", f, self.structs[id].name); self.err(span, m); Self::bad(span) }
                    },
                    Ty::Error => Self::bad(span),
                    t => { let m = format!("type {} has no fields", self.tname(&t)); self.err(span, m); Self::bad(span) }
                }
            }
            ExprKind::Index(b, i) => {
                if let Some(a) = self.vec_operand(b, false) {
                    let a = match a { Some(a) => a, None => { self.expr(i); return Self::bad(span); } };
                    let ih = self.expr(i);
                    return self.builtin("vec_get", vec![a, ih], span, &None);
                }
                let bh0 = self.expr_any(b);
                let bh = self.autoderef(bh0, b.span);
                let ih = self.expr(i);
                match self.resolve(&bh.ty) {
                    Ty::Array(et, n) => {
                        self.check_index(&ih, n);
                        Self::h(HKind::Index(Box::new(bh), Box::new(ih)), *et, span)
                    }
                    Ty::Error => Self::bad(span),
                    t => { let m = format!("cannot index into a value of type {}", self.tname(&t)); self.err(span, m); Self::bad(span) }
                }
            }
            ExprKind::Array(elems) => {
                if elems.is_empty() {
                    self.err(span, "cannot infer the element type of an empty array literal");
                    return Self::bad(span);
                }
                let hs: Vec<HExpr> = elems.iter().map(|x| self.expr(x)).collect();
                let r0 = self.resolve(&hs[0].ty);
                if self.owned(&r0) { let m = owned_in_agg(&self.tname(&r0)); self.err(span, m); return Self::bad(span); }
                let et = hs[0].ty.clone();
                for h in &hs[1..] {
                    if !self.compat(&et, &h.ty) {
                        let m = format!("array elements have different types: {} and {}", self.tname(&et), self.tname(&h.ty));
                        self.err(h.span, m);
                    }
                }
                let n = hs.len();
                Self::h(HKind::Array(hs), Ty::Array(Box::new(et), n), span)
            }
            ExprKind::Repeat(x, n) => {
                let h = self.expr(x);
                let r0 = self.resolve(&h.ty);
                if self.owned(&r0) { let m = owned_in_agg(&self.tname(&r0)); self.err(span, m); return Self::bad(span); }
                if *n > MAX_ARRAY_LEN {
                    self.err(span, format!("array length {} exceeds the M1 maximum of {}", n, MAX_ARRAY_LEN));
                    return Self::bad(span);
                }
                let t = h.ty.clone();
                Self::h(HKind::Repeat(Box::new(h), *n as usize), Ty::Array(Box::new(t), *n as usize), span)
            }
            ExprKind::Match(s, arms) => self.match_expr(s, arms, span, hint),
            ExprKind::Deref(x) => {
                let xh = self.expr_any(x);
                match self.resolve(&xh.ty) {
                    Ty::Ref(inner, _) if self.owned(&inner) => {
                        let m = format!("cannot move an owned `{}` out of a reference; borrow it (`r`) or copy it with `{}_clone(r)`", self.tname(&inner), if *inner == Ty::String { "string" } else { "vec" });
                        self.err(span, m);
                        Self::bad(span)
                    }
                    Ty::Ref(inner, _) if matches!(xh.kind, HKind::Local(_)) => Self::h(HKind::Deref(Box::new(xh)), *inner, span),
                    Ty::Ref(..) => { self.err(span, "only a reference variable can be dereferenced (bind the reference to a variable first)"); Self::bad(span) }
                    Ty::Error => Self::bad(span),
                    t => { let m = format!("cannot dereference a value of type {}", self.tname(&t)); self.err(span, m); Self::bad(span) }
                }
            }
            ExprKind::AddrOf(x, m) => {
                if *m { self.require_not_declarative(span, "mutable borrow `&mut`"); }
                fn is_place(e: &Expr) -> bool {
                    match &e.kind {
                        ExprKind::Path(p) => p.segs.len() == 1,
                        ExprKind::Field(b, _) | ExprKind::Index(b, _) => is_place(b),
                        ExprKind::Deref(b) => is_place(b),
                        _ => false,
                    }
                }
                if !is_place(x) {
                    self.err(span, "only a variable, field, element or `*reference` can be borrowed (not a temporary value)");
                    return Self::bad(span);
                }
                let pi = match self.place(x) { Some(p) => p, None => return Self::bad(span) };
                if matches!(self.resolve(&pi.ty), Ty::Ref(..)) {
                    self.err(span, format!("cannot borrow the reference `{}`; re-borrow its referent with `&*{}` or `&mut *{}`", pi.root, pi.root, pi.root));
                    return Self::bad(span);
                }
                if *m && !pi.mutable {
                    if pi.via_ref == Some(false) { self.err(span, format!("cannot borrow `*{}` as mutable because `{}` is a shared reference", pi.root, pi.root)); }
                    else { self.err(span, format!("cannot borrow `{}` as mutable (declare it with `let mut`)", pi.root)); }
                }
                Self::h(HKind::AddrOf(pi.place, *m), Ty::Ref(Box::new(pi.ty), *m), span)
            }
        }
    }

    fn binary(&mut self, op: BinOp, l: &Expr, r: &Expr, span: Span) -> HExpr {
        use BinOp::*;
        let lh = self.expr(l);
        let rh = self.expr(r);
        let (lt, rt) = (self.resolve(&lh.ty), self.resolve(&rh.ty));
        let is_cmp = matches!(op, Eq | Ne | Lt | Le | Gt | Ge);
        let rty = if self.is_bad(&lt) || self.is_bad(&rt) {
            if is_cmp || matches!(op, And | Or) { Ty::Bool } else { Ty::Error }
        } else {
            let ok_and_ty: Option<Ty> = match op {
                And | Or => if self.compat(&lt, &Ty::Bool) && self.compat(&rt, &Ty::Bool) { Some(Ty::Bool) } else { None },
                Eq | Ne => if self.is_scalar(&lt) && self.unify(&lt, &rt) { Some(Ty::Bool) } else { None },
                Lt | Le | Gt | Ge => if self.is_num(&lt) && self.unify(&lt, &rt) { Some(Ty::Bool) } else { None },
                Add if lt == Ty::Str && rt == Ty::Str => Some(Ty::Str),
                Add | Sub | Mul | Div | Rem => if self.is_num(&lt) && self.unify(&lt, &rt) { Some(lt.clone()) } else { None },
                BitAnd | BitOr | BitXor => if self.is_int(&lt) && self.unify(&lt, &rt) { Some(lt.clone()) } else { None },
                Shl | Shr => if self.is_int(&lt) && self.is_int(&rt) { Some(lt.clone()) } else { None },
            };
            match ok_and_ty {
                Some(t) => t,
                None => {
                    let m = format!("operator `{}` cannot be applied to {} and {}", opsym(op), self.tname(&lt), self.tname(&rt));
                    self.err(span, m);
                    if is_cmp || matches!(op, And | Or) { Ty::Bool } else { Ty::Error }
                }
            }
        };
        Self::h(HKind::Binary(op, Box::new(lh), Box::new(rh)), rty, span)
    }

    fn check_args(&mut self, name: &str, want: &[Ty], got: &mut [HExpr], span: Span) {
        if want.len() != got.len() {
            self.err(span, format!("`{}` takes {} argument(s) but {} were supplied", name, want.len(), got.len()));
            return;
        }
        for (i, (w, g)) in want.iter().zip(got.iter_mut()).enumerate() {
            self.coerce_ref(g, w);
            if !self.compat(&g.ty, w) {
                let m = format!("mismatched types in argument {} of `{}`: expected {}, found {}", i + 1, name, self.tname(w), self.tname(&g.ty));
                self.err(g.span, m);
            }
        }
    }

    fn call(&mut self, p: &Path, args: &[Expr], span: Span, hint: Option<Ty>) -> HExpr {
        if p.segs.len() == 1 && BUILTINS.contains(&p.segs[0].as_str()) {
            let name = p.segs[0].as_str();
            let hs: Vec<HExpr> = args.iter().map(|a| {
                if name == "len" { let h = self.expr_any(a); self.autoderef(h, a.span) }
                else if name == "box_new" {
                    let inner = match hint.as_ref().map(|t| self.resolve(t)) { Some(Ty::Box(e)) => Some(*e), _ => None };
                    self.expr_h(a, inner)
                }
                else if name == "print" || name.starts_with("string_") || name.starts_with("vec_") || name == "box_get" || name == "box_set" {
                    let h = self.expr_any(a);
                    // only `&String` / `&mut String` references may reach a builtin
                    if let Ty::Ref(inner, _) = self.resolve(&h.ty) {
                        if !inner.is_owned() {
                            self.err(a.span, "a reference cannot be used as a value here; dereference it with `*` (references can only be passed as call arguments, bound with `let`, or auto-dereferenced by `.`, `[]` and `len`)");
                            return Self::bad(a.span);
                        }
                    }
                    h
                } else { self.expr(a) }
            }).collect();
            return self.builtin(name, hs, span, &hint);
        }
        if p.segs.len() >= 2 {
            if let Some(fid) = self.resolve_assoc(p) { return self.call_fn(fid, &p.text(), args, span, &hint); }
        }
        match self.resolve_variant(p) {
            VarRes::Found(eid0, vi) => {
                let mut eid = eid0;
                let mut hs: Vec<HExpr>;
                if !self.enum_asts[eid0].0.tparams.is_empty() {
                    if let Some(i) = self.hinted_inst(true, eid0, &hint) {
                        eid = i;
                        let want = self.enums[eid].variants[vi].1.clone();
                        hs = args.iter().enumerate().map(|(k, a)| self.expr_h(a, want.get(k).cloned())).collect();
                    } else {
                        hs = args.iter().map(|a| self.expr(a)).collect();
                        let d = self.enum_asts[eid0].0;
                        let pairs: Vec<(&TyExpr, Ty, Span)> = d.variants[vi].1.iter().zip(hs.iter()).map(|(te, h)| (te, h.ty.clone(), h.span)).collect();
                        eid = match self.infer_inst(true, eid0, &pairs, &p.text(), span) { Some(i) => i, None => return Self::bad(span) };
                    }
                } else {
                    let want = self.enums[eid].variants[vi].1.clone();
                    hs = args.iter().enumerate().map(|(k, a)| self.expr_h(a, want.get(k).cloned())).collect();
                }
                let payload = self.enums[eid].variants[vi].1.clone();
                self.check_args(&p.text(), &payload, &mut hs, span);
                return Self::h(HKind::Variant(vi as u32, hs), Ty::Enum(eid), span);
            }
            VarRes::Reported => { for a in args { self.expr(a); } return Self::bad(span); }
            VarRes::NotVariant => {}
        }
        let m = self.module.clone();
        match self.lookup(&m, &p.segs, p.span) {
            Look::Found(Sym::Fn(id)) => self.call_fn(id, &p.text(), args, span, &hint),
            Look::Found(_) => { for a in args { self.expr(a); } self.err(span, format!("`{}` is not a function", p.text())); Self::bad(span) }
            Look::NotFound => { for a in args { self.expr(a); } self.err(span, format!("undefined function `{}`", p.text())); Self::bad(span) }
            Look::Reported => { for a in args { self.expr(a); } Self::bad(span) }
        }
    }

    fn tparams_in(t: &TyExpr, out: &mut HashSet<String>) {
        match t {
            TyExpr::Named(p) if p.segs.len() == 1 => { out.insert(p.segs[0].clone()); }
            TyExpr::Named(_) => {}
            TyExpr::Generic(_, args) => for a in args { Self::tparams_in(a, out); },
            TyExpr::Array(e, _, _) | TyExpr::Ref(e, _, _) => Self::tparams_in(e, out),
        }
    }

    /// One-way matching of a declared parameter type against an argument type, binding type parameters.
    fn match_ty(&mut self, te: &TyExpr, ty: &Ty, tps: &[String], bind: &mut Vec<Option<Ty>>, module: &str, span: Span) {
        let ty = self.resolve(ty);
        match te {
            TyExpr::Named(p) if p.segs.len() == 1 && tps.contains(&p.segs[0]) => {
                let i = tps.iter().position(|t| *t == p.segs[0]).unwrap();
                match &ty {
                    Ty::Error | Ty::Never => {}
                    Ty::Ref(..) => self.err(span, format!("type parameter `{}` cannot be a reference type (declare the parameter as `&{}` to borrow)", tps[i], tps[i])),
                    _ => match bind[i].clone() {
                        None => bind[i] = Some(ty),
                        Some(b) => if !self.compat(&b, &ty) {
                            let m = format!("conflicting types for type parameter `{}`: {} and {}", tps[i], self.tname(&b), self.tname(&ty));
                            self.err(span, m);
                        },
                    },
                }
            }
            TyExpr::Array(e, n, _) => if let Ty::Array(t, m) = &ty { if *n as usize == *m { self.match_ty(e, t, tps, bind, module, span); } },
            TyExpr::Ref(e, _, _) => if let Ty::Ref(t, _) = &ty { self.match_ty(e, t, tps, bind, module, span); },
            TyExpr::Generic(p, targs) if p.segs.len() == 1 && p.segs[0] == "Vec" && matches!(ty, Ty::Vec(_)) => {
                if let Ty::Vec(e) = &ty { self.match_ty(&targs[0], e, tps, bind, module, span); }
            }
            TyExpr::Generic(p, targs) if p.segs.len() == 1 && p.segs[0] == "Box" && matches!(ty, Ty::Box(_)) => {
                if let Ty::Box(e) = &ty { self.match_ty(&targs[0], e, tps, bind, module, span); }
            }
            TyExpr::Generic(p, targs) => {
                let (is_enum, id) = match &ty { Ty::Struct(i) => (false, *i), Ty::Enum(i) => (true, *i), _ => return };
                let (tid, args) = match self.inst_of.get(&(is_enum, id)).cloned() { Some(x) => x, None => return };
                let target = match self.lookup(module, &p.segs, p.span) {
                    Look::Found(Sym::Struct(t)) if !is_enum => t,
                    Look::Found(Sym::Enum(t)) if is_enum => t,
                    _ => return,
                };
                if target != tid { return; }
                for (te2, a) in targs.iter().zip(args.iter()) { self.match_ty(te2, a, tps, bind, module, span); }
            }
            _ => {}
        }
    }

    /// Call function `id` (plain or generic, free function or associated function).
    /// Validate the signature of an `extern fn` / `export fn` against the C-ABI subset (docs/INTEROP.md).
    fn check_ffi(&mut self, f: &FnDecl, id: usize) {
        let what = if f.ext == Ext::Import { "extern" } else { "export" };
        if f.ext == Ext::Import && f.layer != Layer::Hardware {
            self.err(f.span, format!("`extern fn {}` is only permitted in @layer(hardware) (calling C is an unsafe operation)", f.name));
        }
        if !f.tparams.is_empty() { self.err(f.span, format!("`{} fn {}` cannot be generic (a C symbol has exactly one signature)", what, f.name)); }
        if f.name == "main" || f.name.starts_with("kd_") || f.name.starts_with("llvm.") || f.name.contains("::") {
            self.err(f.span, format!("`{}` cannot be used as a C symbol name (`main`, `kd_*` and `llvm.*` are reserved)", f.name));
        }
        if !self.c_names.insert(f.name.clone()) {
            self.err(f.span, format!("the C symbol `{}` is declared or exported more than once", f.name));
        }
        let (params, ret) = (self.fns[id].params.clone(), self.fns[id].ret.clone());
        for (p, t) in f.params.iter().zip(params.iter()) {
            if !matches!(t, Ty::Int(_) | Ty::Float | Ty::Error) {
                let m = format!("parameter `{}` of `{} fn {}` has type {}, which is not C-ABI safe (allowed: i8..i64, u8..u64, f64)", p.name, what, f.name, self.tname(t));
                self.err(p.span, m);
            }
        }
        if !matches!(ret, Ty::Int(_) | Ty::Float | Ty::Unit | Ty::Error) {
            let m = format!("return type {} of `{} fn {}` is not C-ABI safe (allowed: i8..i64, u8..u64, f64, or no value)", self.tname(&ret), what, f.name);
            self.err(f.span, m);
        }
    }

    fn call_fn(&mut self, id: usize, text: &str, args: &[Expr], span: Span, hint: &Option<Ty>) -> HExpr {
        if self.fn_asts[id].0.ext == Ext::Import && self.unsafe_depth == 0 {
            self.err(span, format!("calling the C function `{}` is unsafe: wrap the call in `unsafe {{ .. }}` (permitted in @layer(hardware))", text));
        }
        if !self.fn_asts[id].0.tparams.is_empty() {
            let hs: Vec<HExpr> = args.iter().map(|a| self.expr_any(a)).collect();
            return self.call_generic(id, text, hs, span, hint);
        }
        let want = self.fns[id].params.clone();
        let mut hs: Vec<HExpr> = args.iter().enumerate().map(|(k, a)| self.expr_any_h(a, want.get(k).cloned())).collect();
        let (params, ret, layer) = (self.fns[id].params.clone(), self.fns[id].ret.clone(), self.fns[id].layer);
        if self.layer == Layer::Declarative && layer != Layer::Declarative {
            self.err(span, format!("@layer(declarative) code may only call declarative functions, but `{}` is @layer({})", text, layer.name()));
        }
        self.check_args(text, &params, &mut hs, span);
        Self::h(HKind::Call(id, hs), ret, span)
    }

    /// Resolve `Type::name` to an associated function, if `Type` is a struct/enum with such a method.
    fn resolve_assoc(&mut self, p: &Path) -> Option<usize> {
        let n = p.segs.len();
        let m = self.module.clone();
        let (is_enum, tid) = match self.lookup(&m, &p.segs[..n - 1], p.span) {
            Look::Found(Sym::Struct(i)) => (false, i),
            Look::Found(Sym::Enum(i)) => (true, i),
            _ => return None,
        };
        let fid = *self.assoc.get(&(is_enum, tid, p.segs[n - 1].clone()))?;
        self.check_method_visible(fid, p.span);
        Some(fid)
    }

    fn check_method_visible(&mut self, fid: usize, span: Span) {
        let (f, fm) = (self.fn_asts[fid].0, self.fn_asts[fid].1.clone());
        if !f.public && !within(&self.module, &fm) { self.err(span, format!("`{}` is private to module `{}`", f.name, if fm.is_empty() { "<root>" } else { &fm })); }
    }

    fn register_assoc(&mut self) {
        for id in std::mem::take(&mut self.assoc_pending) {
            let (f, m) = (self.fn_asts[id].0, self.fn_asts[id].1.clone());
            let a = f.assoc.as_ref().unwrap();
            let (is_enum, tid) = match self.lookup(&m, &a.ty_path.segs, a.ty_path.span) {
                Look::Found(Sym::Struct(i)) => (false, i),
                Look::Found(Sym::Enum(i)) => (true, i),
                Look::Found(_) => { self.err(a.ty_path.span, format!("`{}` is not a struct or enum, so it cannot have an `impl` block", a.ty_path.text())); continue; }
                Look::NotFound => { self.err(a.ty_path.span, format!("unknown type `{}` in `impl`", a.ty_path.text())); continue; }
                Look::Reported => continue,
            };
            let want = if is_enum { self.enum_asts[tid].0.tparams.len() } else { self.struct_asts[tid].0.tparams.len() };
            if a.impl_arity != want {
                self.err(a.ty_path.span, format!("`{}` has {} type parameter(s) but the `impl` names {}", a.ty_path.text(), want, a.impl_arity));
                continue;
            }
            if is_enum && self.enum_asts[tid].0.variants.iter().any(|v| v.0 == a.method) {
                self.err(f.span, format!("method `{}` conflicts with a variant of the same name", a.method));
                continue;
            }
            if self.assoc.insert((is_enum, tid, a.method.clone()), id).is_some() {
                self.err(f.span, format!("`{}` is defined more than once", f.name));
            }
        }
    }

    /// `recv.name(args)`: user methods (via `impl`) and the built-in `Vec` / `String` methods.
    fn method_call(&mut self, recv: &Expr, name: &str, args: &[Expr], span: Span, hint: Option<Ty>) -> HExpr {
        let fail = |this: &mut Self| { for a in args { this.expr(a); } Self::bad(span) };
        let mut rv: Option<HExpr> = None;
        let rty = match &recv.kind {
            ExprKind::Path(p) if p.segs.len() == 1 => self.lookup_local(&p.segs[0]).map(|x| x.1),
            ExprKind::Field(..) | ExprKind::Index(..) | ExprKind::Deref(..) => {
                let n0 = self.diags.len();
                let pi = self.place(recv);
                self.diags.truncate(n0);
                pi.map(|p| p.ty)
            }
            _ => { let h = self.expr_any(recv); let t = h.ty.clone(); rv = Some(h); Some(t) }
        };
        let rty = match rty {
            Some(t) => self.resolve(&t),
            None => { self.expr_any(recv); return fail(self); }
        };
        if self.is_bad(&rty) { return fail(self); }
        let (inner, via_ref) = match &rty { Ty::Ref(i, _) => (self.resolve(i), true), t => (t.clone(), false) };
        // A temporary receiver that must be borrowed is first bound to a hidden local (dropped after the call).
        let mut hidden: Option<(usize, HExpr)> = None;
        let mut recv_e: Expr = recv.clone();
        let mut need_bind = |this: &mut Self, recv_e: &mut Expr, hidden: &mut Option<(usize, HExpr)>| {
            if let Some(h) = rv.take() {
                this.scopes.push(HashMap::new());
                let slot = this.declare("$recv", h.ty.clone(), true);
                *recv_e = Expr { kind: ExprKind::Path(Path { segs: vec!["$recv".to_string()], span: recv.span }), span: recv.span };
                *hidden = Some((slot, h));
            }
        };
        // build the receiver argument for a borrow (`&recv` / `&mut recv`, re-borrowing through a reference variable)
        let borrow = |recv_e: &Expr, m: bool| -> Option<Expr> {
            if via_ref {
                if !matches!(&recv_e.kind, ExprKind::Path(p) if p.segs.len() == 1) { return None; }
                let d = Expr { kind: ExprKind::Deref(Box::new(recv_e.clone())), span: recv_e.span };
                Some(Expr { kind: ExprKind::AddrOf(Box::new(d), m), span: recv_e.span })
            } else {
                Some(Expr { kind: ExprKind::AddrOf(Box::new(recv_e.clone()), m), span: recv_e.span })
            }
        };
        let wrap = |this: &mut Self, hidden: Option<(usize, HExpr)>, call: HExpr, span: Span| -> HExpr {
            match hidden {
                None => call,
                Some((slot, h)) => {
                    this.scopes.pop();
                    let t = call.ty.clone();
                    let b = HBlock { stmts: vec![HStmt::Let(slot, h)], tail: Some(Box::new(call)) };
                    Self::h(HKind::Block(b), t, span)
                }
            }
        };
        match &inner {
            Ty::Vec(_) | Ty::String => {
                let (b, m) = match (&inner, name) {
                    (Ty::Vec(_), "push") => ("vec_push", true), (Ty::Vec(_), "len") => ("vec_len", false), (Ty::Vec(_), "get") => ("vec_get", false),
                    (Ty::Vec(_), "set") => ("vec_set", true), (Ty::Vec(_), "pop") => ("vec_pop", true), (Ty::Vec(_), "clone") => ("vec_clone", false),
                    (Ty::String, "push") => ("string_push", true), (Ty::String, "len") => ("string_len", false), (Ty::String, "clone") => ("string_clone", false),
                    _ => { let m = format!("type {} has no method `{}`", self.tname(&inner), name); self.err(span, m); return fail(self); }
                };
                need_bind(self, &mut recv_e, &mut hidden);
                let first = match borrow(&recv_e, m) { Some(e) => e, None => { self.err(recv.span, "a method receiver that is a reference must be a variable"); return fail(self); } };
                let mut all = vec![first];
                all.extend(args.iter().cloned());
                let p = Path { segs: vec![b.to_string()], span };
                let c = self.call(&p, &all, span, hint);
                wrap(self, hidden, c, span)
            }
            Ty::Struct(id) | Ty::Enum(id) => {
                let is_enum = matches!(inner, Ty::Enum(_));
                let tid = self.inst_of.get(&(is_enum, *id)).map(|x| x.0).unwrap_or(*id);
                let fid = match self.assoc.get(&(is_enum, tid, name.to_string())) {
                    Some(f) => *f,
                    None => { let m = format!("type {} has no method `{}`", self.tname(&inner), name); self.err(span, m); return fail(self); }
                };
                self.check_method_visible(fid, span);
                let sk = self.fn_asts[fid].0.assoc.as_ref().unwrap().self_kind;
                let first = match sk {
                    SelfKind::None => { self.err(span, format!("`{}` is an associated function, not a method; call it as `{}::{}(..)`", name, self.tname(&inner).split('<').next().unwrap_or(""), name)); return fail(self); }
                    SelfKind::Value => {
                        if via_ref {
                            if self.owned(&inner) { self.err(recv.span, "cannot move an owned value out of a reference to call a method that takes `self` by value"); return fail(self); }
                            Expr { kind: ExprKind::Deref(Box::new(recv.clone())), span: recv.span }
                        } else { recv.clone() }
                    }
                    SelfKind::Ref | SelfKind::RefMut => {
                        need_bind(self, &mut recv_e, &mut hidden);
                        match borrow(&recv_e, sk == SelfKind::RefMut) {
                            Some(e) => e,
                            None => { self.err(recv.span, "a method receiver that is a reference must be a variable"); return fail(self); }
                        }
                    }
                };
                let mut all = vec![first];
                all.extend(args.iter().cloned());
                let text = self.fn_asts[fid].0.name.clone();
                let c = self.call_fn(fid, &text, &all, span, &hint);
                wrap(self, hidden, c, span)
            }
            t => { let m = format!("type {} has no methods", self.tname(t)); self.err(span, m); fail(self) }
        }
    }

    fn call_generic(&mut self, id: usize, text: &str, mut hs: Vec<HExpr>, span: Span, hint: &Option<Ty>) -> HExpr {
        let (f, gm) = (self.fn_asts[id].0, self.fn_asts[id].1.clone());
        if hs.len() != f.params.len() {
            self.err(span, format!("`{}` takes {} argument(s) but {} were supplied", text, f.params.len(), hs.len()));
            return Self::bad(span);
        }
        let mut bind: Vec<Option<Ty>> = vec![None; f.tparams.len()];
        let errs = self.diags.len();
        for (pa, h) in f.params.iter().zip(hs.iter()) { let hty = h.ty.clone(); self.match_ty(&pa.ty, &hty, &f.tparams, &mut bind, &gm, h.span); }
        if self.diags.len() > errs { return Self::bad(span); }
        // unbound parameters may still be determined by the expected result type (e.g. `let x: Opt<i64> = Opt::none();`)
        if bind.iter().any(|b| b.is_none()) {
            if let (Some(r), Some(h)) = (&f.ret, hint) {
                let mut b2 = bind.clone();
                let n0 = self.diags.len();
                let hty = self.resolve(h);
                self.match_ty(r, &hty, &f.tparams, &mut b2, &gm, span);
                self.diags.truncate(n0);
                for (slot, cand) in bind.iter_mut().zip(b2) { if slot.is_none() { *slot = cand; } }
            }
        }
        if let Some(i) = bind.iter().position(|b| b.is_none()) {
            self.err(span, format!("cannot infer type parameter `{}` in call to `{}`", f.tparams[i], text));
            return Self::bad(span);
        }
        let targs: Vec<Ty> = bind.into_iter().map(|b| b.unwrap()).collect();
        if self.layer == Layer::Declarative && f.layer != Layer::Declarative {
            self.err(span, format!("@layer(declarative) code may only call declarative functions, but `{}` is @layer({})", text, f.layer.name()));
        }
        let saved = std::mem::replace(&mut self.tenv, f.tparams.iter().cloned().zip(targs.iter().cloned()).collect());
        let params: Vec<Ty> = f.params.iter().map(|q| self.resolve_ty_ref(&q.ty, &gm)).collect();
        let ret = match &f.ret { Some(t) => self.resolve_ty(t, &gm), None => Ty::Unit };
        self.tenv = saved;
        self.check_args(&text, &params, &mut hs, span);
        self.pending.push((id, targs, span));
        Self::h(HKind::Call(GENERIC_BASE + self.pending.len() - 1, hs), ret, span)
    }

    /// Check every requested instantiation (and the ones they request), then patch call sites.
    fn instantiate_all(&mut self, hfns: &mut Vec<HFn>) {
        let mut map: Vec<usize> = vec![];
        let mut k = 0;
        while k < self.pending.len() {
            let (gid, targs, span) = self.pending[k].clone();
            let targs: Vec<Ty> = targs.iter().map(|t| self.fin(t)).collect();
            if let Some((_, _, i)) = self.instances.iter().find(|(g, t, _)| *g == gid && *t == targs) { map.push(*i); k += 1; continue; }
            if self.instances.len() >= MAX_INSTANCES {
                self.err(span, format!("too many generic instantiations (limit {}); possible polymorphic recursion", MAX_INSTANCES));
                map.push(0); k += 1; continue;
            }
            let (f, m) = (self.fn_asts[gid].0, self.fn_asts[gid].1.clone());
            let saved = std::mem::replace(&mut self.tenv, f.tparams.iter().cloned().zip(targs.iter().cloned()).collect());
            let params: Vec<Ty> = f.params.iter().map(|q| self.resolve_ty_ref(&q.ty, &m)).collect();
            let ret = match &f.ret { Some(t) => self.resolve_ty(t, &m), None => Ty::Unit };
            let id = self.fns.len();
            debug_assert_eq!(id, hfns.len());
            self.fns.push(FnInfo { params, ret, layer: f.layer });
            self.instances.push((gid, targs.clone(), id));
            let label = format!("{}<{}>", f.name, targs.iter().map(|t| self.tname(t)).collect::<Vec<_>>().join(", "));
            let nd = self.diags.len();
            let mut h = self.check_fn(f, id, &m);
            h.name = label.clone();
            self.zonk_fn(&mut h);
            for d in &mut self.diags[nd..] { d.message.push_str(&format!(" (in instantiation `{}`)", label)); }
            self.tenv = saved;
            hfns.push(h);
            map.push(id);
            k += 1;
        }
        for h in hfns.iter_mut() { patch_block(&mut h.body, &map); }
    }

    fn builtin(&mut self, name: &str, hs: Vec<HExpr>, span: Span, hint: &Option<Ty>) -> HExpr {
        match name {
            "print" => {
                if self.layer == Layer::Declarative { self.err(span, "`print` has side effects and is not permitted in @layer(declarative)"); }
                if hs.len() != 1 { self.err(span, "`print` takes exactly 1 argument"); }
                else if self.resolve(&hs[0].ty) == Ty::Unit { self.err(hs[0].span, "cannot print a value of type ()"); }
                else if !self.is_scalar(&hs[0].ty) && !matches!(self.resolve(&hs[0].ty), Ty::Error | Ty::Never) && !matches!(self.resolve(&hs[0].ty), Ty::Ref(ref i, _) if **i == Ty::String) {
                    let m = format!("cannot print a value of type {} (M1 can print only integers, f64, bool and str)", self.tname(&hs[0].ty));
                    self.err(hs[0].span, m);
                }
                Self::h(HKind::Builtin(Builtin::Print, hs), Ty::Unit, span)
            }
            "string_from" | "string_concat" | "string_push" | "string_len" | "string_clone" | "string_eq" => {
                self.require_not_declarative(span, "heap allocation (`String`)");
                let rs = |m: bool| Ty::Ref(Box::new(Ty::String), m);
                let (b, want, ret): (Builtin, Vec<Ty>, Ty) = match name {
                    "string_from" => (Builtin::StringFrom, vec![Ty::Str], Ty::String),
                    "string_concat" => (Builtin::StringConcat, vec![rs(false), rs(false)], Ty::String),
                    "string_push" => (Builtin::StringPush, vec![rs(true), Ty::Str], Ty::Unit),
                    "string_len" => (Builtin::StringLen, vec![rs(false)], Ty::Int(IntTy::I64)),
                    "string_clone" => (Builtin::StringClone, vec![rs(false)], Ty::String),
                    _ => (Builtin::StringEq, vec![rs(false), rs(false)], Ty::Bool),
                };
                let mut hs = hs;
                self.check_args(name, &want, &mut hs, span);
                Self::h(HKind::Builtin(b, hs), ret, span)
            }
            "vec_new" | "vec_push" | "vec_len" | "vec_get" | "vec_set" | "vec_pop" | "vec_clone" => {
                self.require_not_declarative(span, "heap allocation (`Vec`)");
                let mut hs = hs;
                if name == "vec_new" {
                    if !hs.is_empty() { self.err(span, "`vec_new` takes no arguments"); }
                    return match hint.as_ref().map(|t| self.resolve(t)) {
                        Some(Ty::Vec(e)) => Self::h(HKind::Builtin(Builtin::VecNew, hs), Ty::Vec(e), span),
                        _ => { self.err(span, "cannot infer the element type of `vec_new()`; give the expected type, e.g. `let v: Vec<i64> = vec_new();`"); Self::bad(span) }
                    };
                }
                let nargs = match name { "vec_len" | "vec_pop" | "vec_clone" => 1, "vec_push" | "vec_get" => 2, _ => 3 };
                if hs.len() != nargs { self.err(span, format!("`{}` takes {} argument(s) but {} were supplied", name, nargs, hs.len())); return Self::bad(span); }
                let elem = match self.resolve(&hs[0].ty) {
                    Ty::Ref(i, _) if matches!(*i, Ty::Vec(_)) => match *i { Ty::Vec(e) => *e, _ => unreachable!() },
                    Ty::Error | Ty::Never => return Self::bad(span),
                    _ => { self.err(hs[0].span, format!("`{}` expects a reference to a Vec as its first argument, e.g. `{}(&v ..)`", name, name)); return Self::bad(span); }
                };
                let vref = |m: bool| Ty::Ref(Box::new(Ty::Vec(Box::new(elem.clone()))), m);
                if matches!(name, "vec_get" | "vec_set") && !self.is_int(&hs[1].ty) && !self.is_bad(&hs[1].ty) {
                    let m = format!("`{}` index must be an integer, found {}", name, self.tname(&hs[1].ty));
                    self.err(hs[1].span, m);
                    return Self::bad(span);
                }
                let idx = hs.get(1).map(|h| h.ty.clone()).unwrap_or(Ty::Unit);
                let (b, want, ret): (Builtin, Vec<Ty>, Ty) = match name {
                    "vec_push" => (Builtin::VecPush, vec![vref(true), elem.clone()], Ty::Unit),
                    "vec_len" => (Builtin::VecLen, vec![vref(false)], Ty::Int(IntTy::I64)),
                    "vec_get" => (Builtin::VecGet, vec![vref(false), idx], elem.clone()),
                    "vec_set" => (Builtin::VecSet, vec![vref(true), idx, elem.clone()], Ty::Unit),
                    "vec_pop" => (Builtin::VecPop, vec![vref(true)], elem.clone()),
                    _ => (Builtin::VecClone, vec![vref(false)], Ty::Vec(Box::new(elem.clone()))),
                };
                self.check_args(name, &want, &mut hs, span);
                Self::h(HKind::Builtin(b, hs), ret, span)
            }
            "box_new" | "box_into" | "box_get" | "box_set" => {
                self.require_not_declarative(span, "heap allocation (`Box`)");
                let mut hs = hs;
                let nargs = match name { "box_new" | "box_into" | "box_get" => 1, _ => 2 };
                if hs.len() != nargs { self.err(span, format!("`{}` takes {} argument(s) but {} were supplied", name, nargs, hs.len())); return Self::bad(span); }
                if name == "box_new" {
                    let t = self.resolve(&hs[0].ty);
                    return match t {
                        Ty::Error | Ty::Never => Self::bad(span),
                        Ty::Ref(..) | Ty::Unit => { let m = format!("`box_new` cannot box a value of type {}", self.tname(&t)); self.err(hs[0].span, m); Self::bad(span) }
                        _ => { let ty = Ty::Box(Box::new(hs[0].ty.clone())); Self::h(HKind::Builtin(Builtin::BoxNew, hs), ty, span) }
                    };
                }
                if name == "box_into" {
                    return match self.resolve(&hs[0].ty) {
                        Ty::Box(e) => Self::h(HKind::Builtin(Builtin::BoxInto, hs), *e, span),
                        Ty::Error | Ty::Never => Self::bad(span),
                        o => { let m = format!("`box_into` expects a `Box<T>` by value, found {}", self.tname(&o)); self.err(hs[0].span, m); Self::bad(span) }
                    };
                }
                // box_get(&b) / box_set(&mut b, x): copy a non-owned value out of / into the cell
                let elem = match self.resolve(&hs[0].ty) {
                    Ty::Ref(i, m) => match *i { Ty::Box(e) => { if name == "box_set" && !m { self.err(hs[0].span, "`box_set` needs a mutable reference: `box_set(&mut b, x)`"); } *e } _ => { self.err(hs[0].span, format!("`{}` expects a reference to a Box as its first argument", name)); return Self::bad(span); } },
                    Ty::Error | Ty::Never => return Self::bad(span),
                    _ => { self.err(hs[0].span, format!("`{}` expects a reference to a Box as its first argument, e.g. `{}(&b ..)`", name, name)); return Self::bad(span); }
                };
                if self.owned(&elem) {
                    let m = format!("`{}` copies the value, but {} is owned; take it out with `box_into(b)` instead", name, self.tname(&elem));
                    self.err(span, m);
                    return Self::bad(span);
                }
                let bref = |m: bool| Ty::Ref(Box::new(Ty::Box(Box::new(elem.clone()))), m);
                if name == "box_get" {
                    self.check_args(name, &[bref(false)], &mut hs, span);
                    Self::h(HKind::Builtin(Builtin::BoxGet, hs), elem, span)
                } else {
                    self.check_args(name, &[bref(true), elem.clone()], &mut hs, span);
                    Self::h(HKind::Builtin(Builtin::BoxSet, hs), Ty::Unit, span)
                }
            }
            "peek" | "poke" => {
                if self.unsafe_depth == 0 { self.err(span, format!("`{}` accesses raw memory and requires an `unsafe` block", name)); }
                let i64t = Ty::Int(IntTy::I64);
                let want: Vec<Ty> = if name == "peek" { vec![i64t.clone()] } else { vec![i64t.clone(), i64t.clone()] };
                let mut hs = hs;
                self.check_args(name, &want, &mut hs, span);
                if name == "peek" { Self::h(HKind::Builtin(Builtin::Peek, hs), i64t, span) }
                else { Self::h(HKind::Builtin(Builtin::Poke, hs), Ty::Unit, span) }
            }
            _ => {
                // len
                if hs.len() != 1 {
                    self.err(span, format!("`len` takes 1 argument(s) but {} were supplied", hs.len()));
                } else if !matches!(self.resolve(&hs[0].ty), Ty::Array(..) | Ty::Error | Ty::Never) {
                    let m = format!("`len` expects an array, found {}", self.tname(&hs[0].ty));
                    self.err(hs[0].span, m);
                }
                // `len` of a side-effect-free place is a compile-time constant (also avoids copying the array).
                if let Some(a) = hs.first() {
                    if let (Ty::Array(_, n), true) = (self.resolve(&a.ty), Self::pure_place(a)) {
                        return Self::h(HKind::Lit(Value::Int(n as i128)), Ty::Int(IntTy::I64), span);
                    }
                }
                Self::h(HKind::Builtin(Builtin::Len, hs), Ty::Int(IntTy::I64), span)
            }
        }
    }

    fn struct_lit(&mut self, p: &Path, fields: &[(String, Expr, Span)], span: Span, hint: Option<Ty>) -> HExpr {
        let m = self.module.clone();
        let mut id = match self.lookup(&m, &p.segs, p.span) {
            Look::Found(Sym::Struct(id)) => id,
            Look::Found(_) => { self.err(p.span, format!("`{}` is not a struct", p.text())); return Self::bad(span); }
            Look::NotFound => { self.err(p.span, format!("unknown struct `{}`", p.text())); return Self::bad(span); }
            Look::Reported => return Self::bad(span),
        };
        let mut pre: Option<std::vec::IntoIter<HExpr>> = None;
        if !self.struct_asts[id].0.tparams.is_empty() {
            if let Some(i) = self.hinted_inst(false, id, &hint) {
                id = i;
            } else {
                let d = self.struct_asts[id].0;
                let hs: Vec<HExpr> = fields.iter().map(|(_, fe, _)| self.expr(fe)).collect();
                let mut pairs: Vec<(&TyExpr, Ty, Span)> = Vec::new();
                for ((fname, _, _), h) in fields.iter().zip(hs.iter()) {
                    if let Some((_, te, _)) = d.fields.iter().find(|(n, _, _)| n == fname) { pairs.push((te, h.ty.clone(), h.span)); }
                }
                id = match self.infer_inst(false, id, &pairs, &p.text(), span) { Some(i) => i, None => return Self::bad(span) };
                pre = Some(hs.into_iter());
            }
        }
        let mut out = Vec::new();
        let mut seen = HashSet::new();
        for (fname, fe, fsp) in fields {
            let pos = self.structs[id].fields.iter().position(|(n, _)| n == fname);
            let h = match pre.as_mut() {
                Some(it) => it.next().unwrap(),
                None => { let fh = pos.map(|i| self.structs[id].fields[i].1.clone()); self.expr_h(fe, fh) }
            };
            match pos {
                None => { let msg = format!("struct `{}` has no field `{}`", self.structs[id].name, fname); self.err(*fsp, msg); }
                Some(i) => {
                    if !seen.insert(i) { self.err(*fsp, format!("field `{}` specified more than once", fname)); continue; }
                    let ft = self.structs[id].fields[i].1.clone();
                    if !self.compat(&h.ty, &ft) {
                        let msg = format!("mismatched types: field `{}` is {} but initializer is {}", fname, self.tname(&ft), self.tname(&h.ty));
                        self.err(fe.span, msg);
                    }
                    out.push((i, h));
                }
            }
        }
        let missing: Vec<String> = self.structs[id].fields.iter().enumerate().filter(|(i, _)| !seen.contains(i)).map(|(_, (n, _))| n.clone()).collect();
        if !missing.is_empty() {
            let msg = format!("missing field(s) in `{}` initializer: {}", self.structs[id].name, missing.join(", "));
            self.err(span, msg);
        }
        Self::h(HKind::Struct(id, out), Ty::Struct(id), span)
    }

    // ---------- match ----------

    fn match_expr(&mut self, s: &Expr, arms: &[Arm], span: Span, hint: Option<Ty>) -> HExpr {
        let sh = self.expr(s);
        if self.resolve(&sh.ty).is_owned() {
            self.err(s.span, "cannot `match` on an owned `String` or `Vec` (it has no patterns; compare with `string_eq` or inspect with `vec_get`)");
            return Self::bad(span);
        }
        if arms.is_empty() {
            self.err(span, "`match` must have at least one arm");
            return Self::bad(span);
        }
        let mut harms = Vec::new();
        let mut rty = Ty::Never;
        for a in arms {
            self.scopes.push(HashMap::new());
            let pat = self.pattern(&a.pat, &sh.ty);
            let body = self.expr_h(&a.body, hint.clone());
            self.scopes.pop();
            let bt = body.ty.clone();
            rty = self.join(rty, bt, a.body.span, "`match` arms");
            harms.push(HArm { pat, body });
        }
        self.check_exhaustive(&sh.ty, &harms, span);
        Self::h(HKind::Match(Box::new(sh), harms), rty, span)
    }

    fn pattern(&mut self, p: &Pattern, expected: &Ty) -> HPat {
        let exp = self.resolve(expected);
        match &p.kind {
            PatKind::Wild => HPat::Wild,
            PatKind::Bind(n) => {
                if n.chars().next().map_or(false, |c| c.is_uppercase()) {
                    self.err(p.span, format!("`{}` looks like an enum variant but is not qualified; write `Enum::{}` (binding names must start with a lowercase letter or `_`)", n, n));
                }
                let slot = self.declare(n, expected.clone(), false);
                HPat::Bind(slot)
            }
            PatKind::Int(v) => {
                if !self.is_int(&exp) && exp != Ty::Error {
                    let m = format!("integer pattern does not match a scrutinee of type {}", self.tname(&exp));
                    self.err(p.span, m);
                }
                HPat::Lit(Value::Int(*v), expected.clone(), p.span)
            }
            PatKind::Bool(b) => {
                if exp != Ty::Bool && exp != Ty::Error {
                    let m = format!("bool pattern does not match a scrutinee of type {}", self.tname(&exp));
                    self.err(p.span, m);
                }
                HPat::Lit(Value::Bool(*b), Ty::Bool, p.span)
            }
            PatKind::Str(s) => {
                if exp != Ty::Str && exp != Ty::Error {
                    let m = format!("string pattern does not match a scrutinee of type {}", self.tname(&exp));
                    self.err(p.span, m);
                }
                HPat::Lit(Value::Str(s.clone()), Ty::Str, p.span)
            }
            PatKind::Variant(path, subs) => {
                match self.resolve_variant(path) {
                    VarRes::Found(eid0, vi) => {
                        let mut eid = eid0;
                        if !self.enum_asts[eid0].0.tparams.is_empty() {
                            match &exp {
                                Ty::Enum(i) if self.inst_of.get(&(true, *i)).map(|x| x.0) == Some(eid0) => eid = *i,
                                _ => {
                                    if exp != Ty::Error {
                                        let m = format!("pattern `{}` is of generic type {} but the scrutinee is {}", path.text(), self.enums[eid0].name, self.tname(&exp));
                                        self.err(p.span, m);
                                    }
                                    for s in subs { self.pattern(s, &Ty::Error); }
                                    return HPat::Wild;
                                }
                            }
                        }
                        if exp != Ty::Enum(eid) && exp != Ty::Error {
                            let m = format!("pattern `{}` is of type {} but the scrutinee is {}", path.text(), self.enums[eid].name, self.tname(&exp));
                            self.err(p.span, m);
                        }
                        let payload = self.enums[eid].variants[vi].1.clone();
                        if payload.len() != subs.len() {
                            self.err(p.span, format!("pattern `{}` has {} field(s) but the variant has {}", path.text(), subs.len(), payload.len()));
                            for s in subs { self.pattern(s, &Ty::Error); }
                            return HPat::Wild;
                        }
                        let hs = subs.iter().zip(payload.iter()).map(|(s, t)| self.pattern(s, t)).collect();
                        HPat::Variant(vi as u32, hs)
                    }
                    VarRes::Reported => HPat::Wild,
                    VarRes::NotVariant => {
                        self.err(p.span, format!("unresolved pattern `{}` (variants are written `Enum::Variant`)", path.text()));
                        HPat::Wild
                    }
                }
            }
        }
    }

    fn irrefutable(p: &HPat) -> bool { matches!(p, HPat::Wild | HPat::Bind(_)) }

    /// Conservative exhaustiveness: a variant counts as covered only by an arm whose sub-patterns are all
    /// irrefutable; otherwise a catch-all arm is required.
    fn check_exhaustive(&mut self, sty: &Ty, arms: &[HArm], span: Span) {
        if arms.iter().any(|a| Self::irrefutable(&a.pat)) { return; }
        match self.resolve(sty) {
            Ty::Error | Ty::Never => {}
            Ty::Enum(id) => {
                let mut covered = HashSet::new();
                for a in arms {
                    if let HPat::Variant(v, subs) = &a.pat {
                        if subs.iter().all(Self::irrefutable) { covered.insert(*v); }
                    }
                }
                let missing: Vec<String> = self.enums[id].variants.iter().enumerate()
                    .filter(|(i, _)| !covered.contains(&(*i as u32))).map(|(_, (n, _))| format!("{}::{}", self.enums[id].name, n)).collect();
                if !missing.is_empty() {
                    self.err(span, format!("non-exhaustive `match`: not covered: {} (add arms or a `_` arm)", missing.join(", ")));
                }
            }
            Ty::Bool => {
                let has = |b: bool| arms.iter().any(|a| matches!(&a.pat, HPat::Lit(Value::Bool(x), _, _) if *x == b));
                if !(has(true) && has(false)) { self.err(span, "non-exhaustive `match` on bool: cover both `true` and `false` or add a `_` arm"); }
            }
            _ => self.err(span, "non-exhaustive `match`: add a `_` arm"),
        }
    }

    // ---------- zonking: apply inference results, default integer literals to i64, range-check literals ----------

    fn fin(&mut self, t: &Ty) -> Ty {
        match self.resolve(t) {
            Ty::Var(v) => { self.vars[v as usize] = Some(Ty::Int(IntTy::I64)); Ty::Int(IntTy::I64) }
            Ty::Array(e, n) => Ty::Array(Box::new(self.fin(&e)), n),
            Ty::Ref(t, m) => Ty::Ref(Box::new(self.fin(&t)), m),
            Ty::Vec(e) => Ty::Vec(Box::new(self.fin(&e))),
            Ty::Box(e) => Ty::Box(Box::new(self.fin(&e))),
            o => o,
        }
    }

    fn zonk_fn(&mut self, f: &mut HFn) {
        let tys = std::mem::take(&mut f.slot_tys);
        f.slot_tys = tys.iter().map(|t| self.fin(t)).collect();
        self.zblock(&mut f.body);
    }

    fn zblock(&mut self, b: &mut HBlock) {
        for s in &mut b.stmts {
            match s {
                HStmt::Let(_, e) | HStmt::Expr(e) => self.zexpr(e),
                HStmt::Assign(p, e) => {
                    for pr in &mut p.proj { if let Proj::Index(i) = pr { self.zexpr(i); } }
                    self.zexpr(e);
                }
                HStmt::While(c, b) => { self.zexpr(c); self.zblock(b); }
                HStmt::Return(e) => { if let Some(e) = e { self.zexpr(e); } }
                HStmt::Drop(_) | HStmt::Break | HStmt::Continue => {}
            }
        }
        if let Some(t) = &mut b.tail { self.zexpr(t); }
    }

    fn zpat(&mut self, p: &mut HPat) {
        match p {
            HPat::Lit(v, t, sp) => {
                *t = self.fin(t);
                if let (Value::Int(i), Ty::Int(k)) = (&*v, &*t) {
                    if !k.contains(*i) { let m = format!("integer literal {} does not fit in {}", i, k.name()); self.err(*sp, m); }
                }
            }
            HPat::Variant(_, subs) => for s in subs { self.zpat(s); },
            _ => {}
        }
    }

    fn zexpr(&mut self, e: &mut HExpr) {
        e.ty = self.fin(&e.ty);
        match &mut e.kind {
            HKind::Lit(Value::Int(v)) => {
                if let Ty::Int(k) = &e.ty {
                    if !k.contains(*v) { let m = format!("integer literal {} does not fit in {}", v, k.name()); self.err(e.span, m); }
                }
            }
            HKind::Lit(_) | HKind::Local(_) | HKind::Move(_) => {}
            HKind::AddrOf(p, _) => { for pr in &mut p.proj { if let Proj::Index(i) = pr { self.zexpr(i); } } }
            HKind::Unary(_, x) | HKind::Cast(x) | HKind::Field(x, _) | HKind::Repeat(x, _) | HKind::Deref(x) => self.zexpr(x),
            HKind::Binary(_, a, b) | HKind::Index(a, b) => { self.zexpr(a); self.zexpr(b); }
            HKind::Call(_, xs) | HKind::Builtin(_, xs) | HKind::Array(xs) | HKind::Variant(_, xs) => for x in xs { self.zexpr(x); },
            HKind::If(c, t, el) => { self.zexpr(c); self.zblock(t); if let Some(b) = el { self.zblock(b); } }
            HKind::Block(b) => self.zblock(b),
            HKind::Struct(_, fs) => for (_, x) in fs { self.zexpr(x); },
            HKind::Match(s, arms) => {
                self.zexpr(s);
                for a in arms { self.zpat(&mut a.pat); self.zexpr(&mut a.body); }
            }
        }
    }
}

/// Call ids at or above this value are placeholders for pending generic instantiations.
const GENERIC_BASE: usize = 1 << 40;
const MAX_INSTANCES: usize = 256;

fn patch_block(b: &mut HBlock, map: &[usize]) {
    for s in &mut b.stmts {
        match s {
            HStmt::Let(_, e) | HStmt::Expr(e) => patch_expr(e, map),
            HStmt::Assign(p, e) => { for pr in &mut p.proj { if let Proj::Index(i) = pr { patch_expr(i, map); } } patch_expr(e, map); }
            HStmt::While(c, b) => { patch_expr(c, map); patch_block(b, map); }
            HStmt::Return(e) => { if let Some(e) = e { patch_expr(e, map); } }
            HStmt::Drop(_) | HStmt::Break | HStmt::Continue => {}
        }
    }
    if let Some(t) = &mut b.tail { patch_expr(t, map); }
}

fn patch_expr(e: &mut HExpr, map: &[usize]) {
    match &mut e.kind {
        HKind::Lit(_) | HKind::Local(_) | HKind::Move(_) => {}
        HKind::AddrOf(p, _) => { for pr in &mut p.proj { if let Proj::Index(i) = pr { patch_expr(i, map); } } }
        HKind::Unary(_, x) | HKind::Cast(x) | HKind::Field(x, _) | HKind::Repeat(x, _) | HKind::Deref(x) => patch_expr(x, map),
        HKind::Binary(_, a, b) | HKind::Index(a, b) => { patch_expr(a, map); patch_expr(b, map); }
        HKind::Call(id, xs) => {
            if *id >= GENERIC_BASE { *id = map[*id - GENERIC_BASE]; }
            for x in xs { patch_expr(x, map); }
        }
        HKind::Builtin(_, xs) | HKind::Array(xs) | HKind::Variant(_, xs) => for x in xs { patch_expr(x, map); },
        HKind::If(c, t, el) => { patch_expr(c, map); patch_block(t, map); if let Some(b) = el { patch_block(b, map); } }
        HKind::Block(b) => patch_block(b, map),
        HKind::Struct(_, fs) => for (_, x) in fs { patch_expr(x, map); },
        HKind::Match(s, arms) => { patch_expr(s, map); for a in arms { patch_expr(&mut a.body, map); } }
    }
}
