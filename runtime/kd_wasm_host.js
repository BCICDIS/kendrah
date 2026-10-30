// Host for K.E.N.D.R.A.H. wasm32 programs (target T2). Usage: node kd_wasm_host.js prog.wasm
// Provides the `env` imports of runtime/kd_rt_wasm.c. stdout/stderr are written as raw bytes; exit status is the
// program's (2 = runtime error, 70 = internal error).
const fs = require('fs');
const { Worker, isMainThread, parentPort } = require('worker_threads');

class Exit { constructor(code) { this.code = code; } }

// Rust `{:?}` formatting of f64 (same algorithm as kd_print_f64 in the native runtime).
function f64Debug(x) {
  if (Number.isNaN(x)) return 'NaN';
  if (x === Infinity) return 'inf';
  if (x === -Infinity) return '-inf';
  if (x === 0) return Object.is(x, -0) ? '-0.0' : '0.0';
  const neg = x < 0;
  const ax = Math.abs(x);
  const [mant, exp] = ax.toExponential().split('e'); // shortest round-trip digits
  const e = parseInt(exp, 10);
  let digits = mant.replace('.', '');
  digits = digits.replace(/0+$/, '') || '0';
  const n = digits.length;
  let o = neg ? '-' : '';
  if (ax >= 1e16 || ax < 1e-4) {
    o += digits[0];
    if (n > 1) o += '.' + digits.slice(1);
    o += 'e' + e;
  } else if (e >= 0) {
    for (let i = 0; i <= e; i++) o += i < n ? digits[i] : '0';
    o += '.';
    o += n > e + 1 ? digits.slice(e + 1) : '0';
  } else {
    o += '0.' + '0'.repeat(-e - 1) + digits;
  }
  return o;
}

async function main() {
  const bytes = fs.readFileSync(process.argv[2]);
  let mem;
  const imports = { env: {
    kd_write(fd, ptr, len) {
      const b = Buffer.from(new Uint8Array(mem.buffer, ptr, len));
      fs.writeSync(fd, b);
    },
    kd_f64_to_str(x, buf) {
      const s = f64Debug(x);
      new Uint8Array(mem.buffer, buf, s.length).set(Buffer.from(s, 'latin1'));
      return s.length;
    },
    kd_fmod(a, b) { return a % b; },
    kd_exit(code) { throw new Exit(code); },
  } };
  const { instance } = await WebAssembly.instantiate(bytes, imports);
  mem = instance.exports.memory;
  let code;
  try { code = instance.exports.kd_start(); }
  catch (e) { if (e instanceof Exit) code = e.code; else { process.stderr.write('internal error: ' + e + '\n'); code = 70; } }
  return code;
}

// The program runs in a worker thread so it gets a large JS stack (V8's default allows only ~10k wasm frames, which
// the recursive drop of a long `Box` chain exceeds). Exit status is passed back to the main thread.
if (isMainThread) {
  const w = new Worker(__filename, { argv: process.argv.slice(2), resourceLimits: { stackSizeMb: 200 } });
  w.on('message', (c) => { process.exitCode = c; });
  w.on('error', (e) => { process.stderr.write('internal error: ' + e + '\n'); process.exitCode = 70; });
} else {
  main().then((c) => parentPort.postMessage(c));
}
