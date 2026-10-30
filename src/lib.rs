//! K.E.N.D.R.A.H. milestone M1: lexer, parser, checker (types, inference, modules, @layer rules) lowering to typed HIR, tree-walk interpreter.

pub mod ast;
pub mod borrow;
pub mod drops;
pub mod moves;
pub mod check;
pub mod diag;
pub mod hir;
pub mod interp;
pub mod lexer;
pub mod lower;
pub mod native;
pub mod parser;
pub mod ty;
pub mod uir;
pub mod uir_interp;

use diag::Diag;

/// Front end: lex + parse + check. Returns the program or all diagnostics.
pub fn compile(src: &str) -> Result<hir::HProgram, Vec<Diag>> {
    let toks = lexer::lex(src).map_err(|d| vec![d])?;
    let prog = parser::parse(toks).map_err(|d| vec![d])?;
    check::check(&prog)
}

#[derive(Debug)]
pub enum RunError {
    Compile(Vec<Diag>),
    Runtime(interp::RuntimeError),
    /// Compiler bug: the UIR verifier rejected lowered code, or the two engines disagreed.
    Internal(String),
}

/// Which execution engine to use.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Engine { Hir, Uir }

/// Lower a checked program to UIR and verify it. A verifier failure is a compiler bug.
pub fn lower_and_verify(h: &hir::HProgram) -> Result<uir::UProgram, RunError> {
    let u = lower::lower_program(h);
    uir::verify(&u).map_err(|e| RunError::Internal(format!("UIR verification failed:\n{}\n{}", e.join("\n"), u.dump())))?;
    Ok(u)
}

/// Front end + lowering + verification.
pub fn compile_uir(src: &str) -> Result<uir::UProgram, RunError> {
    let h = compile(src).map_err(RunError::Compile)?;
    lower_and_verify(&h)
}

fn run_engine(h: &hir::HProgram, u: Option<&uir::UProgram>, engine: Engine, fuel: Option<u64>) -> (String, Result<(), interp::RuntimeError>) {
    let mut buf: Vec<u8> = Vec::new();
    let r = match engine {
        Engine::Hir => interp::run_with_fuel(h, &mut buf, fuel),
        Engine::Uir => uir_interp::run(u.expect("uir program"), &mut buf, fuel),
    };
    (String::from_utf8_lossy(&buf).into_owned(), r)
}

fn finish(out: String, r: Result<(), interp::RuntimeError>) -> Result<String, RunError> {
    r.map_err(RunError::Runtime)?;
    Ok(out)
}

/// Compile and run `src` on the HIR interpreter, returning everything the program printed.
pub fn run_source(src: &str) -> Result<String, RunError> { run_source_with(src, Engine::Hir, None) }

/// Like `run_source` with an execution step limit (a runtime error when exceeded).
pub fn run_source_fuel(src: &str, fuel: u64) -> Result<String, RunError> { run_source_with(src, Engine::Hir, Some(fuel)) }

pub fn run_source_with(src: &str, engine: Engine, fuel: Option<u64>) -> Result<String, RunError> {
    let h = compile(src).map_err(RunError::Compile)?;
    let u = if engine == Engine::Uir { Some(lower_and_verify(&h)?) } else { None };
    let (out, r) = run_engine(&h, u.as_ref(), engine, fuel);
    finish(out, r)
}

/// Run on **both** engines and require identical observable behaviour (printed output, and the runtime error
/// message and source location if any). Disagreement or a UIR verifier failure is `RunError::Internal`.
/// With `fuel = Some(_)` the engines count steps differently, so only the HIR result is returned unchecked.
pub fn run_differential(src: &str, fuel: Option<u64>) -> Result<String, RunError> {
    let h = compile(src).map_err(RunError::Compile)?;
    let u = lower_and_verify(&h)?;
    let (o1, r1) = run_engine(&h, Some(&u), Engine::Hir, fuel);
    if fuel.is_some() { return finish(o1, r1); }
    let (o2, r2) = run_engine(&h, Some(&u), Engine::Uir, fuel);
    if o1 != o2 || r1 != r2 {
        return Err(RunError::Internal(format!(
            "engines disagree\n HIR: output={:?} result={:?}\n UIR: output={:?} result={:?}\n{}", o1, r1, o2, r2, u.dump())));
    }
    finish(o1, r1)
}
