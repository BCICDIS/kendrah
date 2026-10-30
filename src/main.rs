use std::io::Write;
use std::process::exit;

fn usage() -> ! {
    eprintln!("usage:\n  kendrah check <file.kd>\n  kendrah run [--engine hir|uir] [--fuel N] <file.kd>\n  kendrah dump-uir <file.kd>\n  kendrah emit-llvm <file.kd>          (LLVM IR for x86-64 Linux on stdout)\n  kendrah build [-O0..-O3] [--target x86_64|wasm32] [--link file.c|file.o|file.a] [-lNAME] [-o out] <file.kd>   (native executable via clang, or a .wasm module; run it with runtime/kd_wasm_host.js under Node)\n  kendrah emit-llvm [--target x86_64|wasm32] <file.kd>\n\nExit codes: 0 ok, 1 compile errors (incl. constructs the native target does not support), 2 runtime error, 64 usage/IO error, 70 internal compiler error");
    exit(64)
}

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    if args.is_empty() { usage(); }
    let cmd = args[0].as_str();
    if !matches!(cmd, "check" | "run" | "dump-uir" | "emit-llvm" | "build") { usage(); }
    let mut engine = kendrah::Engine::Hir;
    let mut fuel: Option<u64> = None;
    let mut path: Option<&String> = None;
    let mut out_path: Option<String> = None;
    let mut opt_level: u8 = 2;
    let mut link: Vec<String> = Vec::new();
    let mut target = kendrah::native::Target::X86Linux;
    let mut i = 1;
    while i < args.len() {
        match args[i].as_str() {
            "--engine" if cmd == "run" && i + 1 < args.len() => {
                engine = match args[i + 1].as_str() { "hir" => kendrah::Engine::Hir, "uir" => kendrah::Engine::Uir, _ => usage() };
                i += 2;
            }
            "--fuel" if cmd == "run" && i + 1 < args.len() => {
                fuel = Some(args[i + 1].parse().unwrap_or_else(|_| usage()));
                i += 2;
            }
            "--link" if cmd == "build" && i + 1 < args.len() => { link.push(args[i + 1].clone()); i += 2; }
            a if cmd == "build" && a.starts_with("-l") && a.len() > 2 => { link.push(a.to_string()); i += 1; }
            "-o" if cmd == "build" && i + 1 < args.len() => { out_path = Some(args[i + 1].clone()); i += 2; }
            "--target" if matches!(cmd, "build" | "emit-llvm") && i + 1 < args.len() => {
                target = match args[i + 1].as_str() { "x86_64" => kendrah::native::Target::X86Linux, "wasm32" => kendrah::native::Target::Wasm32, _ => usage() };
                i += 2;
            }
            a @ ("-O0" | "-O1" | "-O2" | "-O3") if cmd == "build" => { opt_level = a.as_bytes()[2] - b'0'; i += 1; }
            a if a.starts_with('-') && a.len() > 1 => usage(),
            _ => { if path.is_some() { usage(); } path = Some(&args[i]); i += 1; }
        }
    }
    let path = path.unwrap_or_else(|| usage());
    let src = match std::fs::read_to_string(path) {
        Ok(s) => s,
        Err(e) => { eprintln!("error: cannot read {}: {}", path, e); exit(64) }
    };
    let prog = match kendrah::compile(&src) {
        Ok(p) => p,
        Err(ds) => {
            for d in &ds { eprint!("{}", d.render(&src, path)); }
            eprintln!("{} error(s)", ds.len());
            exit(1)
        }
    };
    if cmd == "check" { println!("{}: ok", path); return; }
    let uir = if matches!(cmd, "dump-uir" | "emit-llvm" | "build") || engine == kendrah::Engine::Uir {
        match kendrah::lower_and_verify(&prog) {
            Ok(u) => Some(u),
            Err(e) => { eprintln!("internal compiler error: {:?}", e); exit(70) }
        }
    } else { None };
    if cmd == "dump-uir" { print!("{}", uir.as_ref().unwrap().dump()); return; }
    if cmd == "emit-llvm" || cmd == "build" {
        let u = uir.unwrap();
        let ll = match kendrah::native::emit_llvm_for(&u, path, target) {
            Ok(ll) => ll,
            Err(ds) => {
                for d in &ds { eprint!("{}", d.render(&src, path)); }
                eprintln!("{} error(s): not supported by the native backend", ds.len());
                exit(1)
            }
        };
        if cmd == "emit-llvm" { print!("{}", ll); return; }
        let out = out_path.unwrap_or_else(|| {
            let stem = std::path::Path::new(path).file_stem().and_then(|s| s.to_str()).unwrap_or("a");
            if target == kendrah::native::Target::Wasm32 { format!("{}.wasm", stem) } else { stem.to_string() }
        });
        if target == kendrah::native::Target::Wasm32 {
            match kendrah::native::build_wasm(&ll, std::path::Path::new(&out), opt_level) {
                Ok(()) => { eprintln!("built {} (run: node runtime/kd_wasm_host.js {})", out, out); return; }
                Err(e) => { eprintln!("error: {}", e); exit(70) }
            }
        }
        match kendrah::native::build_executable(&ll, &kendrah::native::BuildOpts { out: out.clone().into(), opt_level, link: link.clone() }) {
            Ok(()) => { eprintln!("built {}", out); return; }
            Err(e) => { eprintln!("error: {}", e); exit(70) }
        }
    }
    // Run on a big stack: both interpreters recurse natively per call.
    let h = std::thread::Builder::new().stack_size(512 * 1024 * 1024).spawn(move || {
        let stdout = std::io::stdout();
        let mut lock = stdout.lock();
        let r = match &uir {
            Some(u) => kendrah::uir_interp::run(u, &mut lock, fuel),
            None => kendrah::interp::run_with_fuel(&prog, &mut lock, fuel),
        };
        let _ = lock.flush();
        r
    }).unwrap();
    match h.join().unwrap() {
        Ok(()) => {}
        Err(e) => {
            eprintln!("{}:{}:{}: runtime error: {}", path, e.span.line, e.span.col, e.message);
            exit(2)
        }
    }
}
