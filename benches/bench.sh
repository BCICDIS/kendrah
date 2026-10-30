#!/usr/bin/env bash
# Informational micro-benchmarks for the two interpreters. Usage: benches/bench.sh [runs]
# Results depend on the machine; record them with the date and `uname -srm` when you publish numbers.
set -euo pipefail
cd "$(dirname "$0")/.."
RUNS=${1:-3}
cargo build --release -q
BIN=./target/release/kendrah
T=$(mktemp -d)
cat > "$T/loop.kd" <<'K'
fn main() { let mut i = 0; let mut s = 0; while i < 10000000 { s = s + i; i = i + 1; } print(s); }
K
cat > "$T/fib.kd" <<'K'
fn fib(n: i64) -> i64 { if n < 2 { return n; } fib(n - 1) + fib(n - 2) }
fn main() { print(fib(30)); }
K
cat > "$T/sieve.kd" <<'K'
fn main() { let mut s = [true; 1000000]; s[0] = false; s[1] = false; let mut i = 2;
  while i * i < 1000000 { if s[i] { let mut j = i * i; while j < 1000000 { s[j] = false; j = j + i; } } i = i + 1; }
  let mut c = 0; let mut k = 0; while k < len(s) { if s[k] { c = c + 1; } k = k + 1; } print(c); }
K
echo "machine: $(uname -srm); date: $(date -u +%F); runs per cell: $RUNS (best wall-clock seconds)"
printf "%-8s %-8s %s\n" program engine best_seconds
for prog in loop fib sieve; do
  for eng in hir uir; do
    best=999999
    for _ in $(seq "$RUNS"); do
      s=$(date +%s.%N); out=$($BIN run --engine $eng "$T/$prog.kd"); e=$(date +%s.%N)
      d=$(echo "$e - $s" | bc -l); best=$(echo "if ($d < $best) $d else $best" | bc -l)
    done
    printf "%-8s %-8s %.3f   (output: %s)\n" "$prog" "$eng" "$best" "$out"
  done
done
echo
echo "native (x86-64, clang $(clang --version | head -1 | sed 's/.*version //;s/ .*//')): compile = kendrah build wall-clock; run = best of $RUNS; size = executable bytes"
printf "%-8s %-5s %-10s %-10s %-9s %s\n" program opt compile_s run_s size_B output
for prog in loop fib sieve; do
  for opt in O0 O2; do
    s=$(date +%s.%N); $BIN build -$opt -o "$T/$prog.$opt" "$T/$prog.kd" 2>/dev/null; e=$(date +%s.%N)
    ct=$(echo "$e - $s" | bc -l)
    best=999999
    for _ in $(seq "$RUNS"); do
      s=$(date +%s.%N); out=$("$T/$prog.$opt"); e=$(date +%s.%N)
      d=$(echo "$e - $s" | bc -l); best=$(echo "if ($d < $best) $d else $best" | bc -l)
    done
    printf "%-8s %-5s %-10.3f %-10.3f %-9s %s\n" "$prog" "$opt" "$ct" "$best" "$(stat -c %s "$T/$prog.$opt")" "$out"
  done
done
rm -rf "$T"
