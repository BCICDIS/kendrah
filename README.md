# K.E.N.D.R.A.H.

Unified Spectrum Programming Language: research/engineering project (see `docs/`). Current state (2026-10-30): typed front end with generics, `impl` blocks/methods, references with a borrow checker, owned `String`/`Vec`/`Box`/structs/enums with drop glue and by-value `match` (recursive types through `Box`); a verified intermediate representation (UIR); two interpreters; and scalar C interop (`extern fn`/`export fn`, native only), and two code-generation targets (x86-64 Linux via clang, wasm32 via clang+lld run under Node), both tested to agree with the interpreters. Large parts of the vision (traits, borrowing through references into heap values (`&*box`, borrowing `match`), standard library, pointer/string FFI, embedded/GPU targets, Python/JS interop) are not built; see `docs/LEDGER.md`. Not a release.

```
cargo build --release
./target/release/kendrah check examples/shapes.kd
./target/release/kendrah run   examples/layers.kd
./target/release/kendrah run --engine uir examples/layers.kd
./target/release/kendrah build -o fib examples/fib.kd && ./fib   # native; needs clang (see docs/TARGETS.md)
./target/release/kendrah build --target wasm32 -o fib.wasm examples/fib.kd && node runtime/kd_wasm_host.js fib.wasm   # needs clang+lld and node
./target/release/kendrah emit-llvm examples/fib.kd
./target/release/kendrah dump-uir examples/shapes.kd
cargo test            # 298 tests
```

- **Start here:** `docs/GETTING_STARTED.md` (install and commands), `CONTINUATION.md` (where development stopped and what to do next)
- Language spec: `docs/SPEC.md`; IR spec: `docs/UIR.md`; benchmarks: `docs/BENCHMARKS.md`
- What exists / what does not: `docs/LEDGER.md`
- Plan: `docs/ROADMAP.md`; assessment of the original blueprint: `docs/ASSESSMENT.md`; video notes: `docs/VIDEO_ANALYSIS.md`; decisions and defects: `docs/DEVLOG.md`
