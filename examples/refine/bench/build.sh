#!/usr/bin/env bash
# The A binaries of the refinement benchmark (examples/refine/bench/README.md):
# for each function of tasks.json, examples/refine/targets is linked with
# that function's driver as the entry and --gc-sections, so the binary holds
# the driver, the function and what it calls. Every function in it must be at
# L1 or above and its text must round-trip (disasm, asm, link at the same
# addresses, identical .text), so that a solver's edited text can be
# assembled back into B. Writes examples/elf/bench-<function>.elf and
# examples/refine/bench/manifest.json (with --update), or compares.
#
#   examples/refine/bench/build.sh [--update]
#   (TOOLCHAIN, CARGO_HOME, CARGO_TARGET_DIR, LLD, NOCOMPILER as for conformance.sh)
set -euo pipefail
cd "$(dirname "$0")/../../.."
TOOLCHAIN=${TOOLCHAIN:-nightly-2026-11-01}
SCRATCH=${SCRATCH:-/tmp}
export CARGO_HOME=${CARGO_HOME:-$SCRATCH/refine-cargo-home}
export CARGO_TARGET_DIR=${CARGO_TARGET_DIR:-$SCRATCH/refine-target}
LLD=${LLD:-$(command -v ld.lld || command -v ld.lld-20 || echo ld.lld)}
NOCOMPILER=${NOCOMPILER:-$PWD/target/release/nocompiler}
TARGET=riscv64im-unknown-none-elf
export RUSTFLAGS="-C target-feature=+m,+zba,+zbb -C code-model=medium -C relocation-model=static \
  -C jump-tables=no -Z trap-unreachable=no"
(cd examples/refine/targets && cargo "+$TOOLCHAIN" build -q --release --target $TARGET \
  -Zbuild-std=core,compiler_builtins -Zbuild-std-features=compiler-builtins-mem)
a="$CARGO_TARGET_DIR/$TARGET/release/librefine_targets.a"
out="$CARGO_TARGET_DIR/bench"
mkdir -p "$out"
python3 -I - "$a" "$out" "$LLD" "$NOCOMPILER" "${1:-}" <<'PY'
import hashlib, json, os, shutil, subprocess, sys
a, out, lld, nc, mode = sys.argv[1:6]
tasks = json.load(open("examples/refine/bench/tasks.json"))["tasks"]
funcs = {}
for t in tasks:
    funcs.setdefault(t["function"], t)
manifest, status = {}, 0
def run(*c, **k):
    return subprocess.run(c, capture_output=True, text=True, **k)
for f, t in funcs.items():
    elf = f"{out}/bench-{f}.elf"
    r = run(lld, "-static", "-e", t["driver"], "--gc-sections", "--build-id=none", "-z", "noseparate-code", a, "-o", elf)
    if r.returncode: sys.exit(f"{f}: ld.lld: {r.stderr}")
    chk = json.loads(run(nc, "check", "--json", elf).stdout)
    levels = {fn["name"]: fn.get("level") for fn in chk["functions"]}
    low = [n for n, l in levels.items() if l not in ("L1", "L2")]
    if low:
        print(f"FAIL {f}: below L1: {low}"); status = 1; continue
    # The round trip, as the harness will do it for B.
    s = f"{out}/{f}.s"; o = f"{out}/{f}.o"; re_ = f"{out}/{f}.re.elf"
    open(s, "w").write(run(nc, "disasm", elf).stdout)
    if run(nc, "asm", s, "-o", o).returncode: print(f"FAIL {f}: asm"); status = 1; continue
    secs = json.loads(run(nc, "sections", "--json", elf).stdout) if False else None
    starts = []
    for line in run("llvm-readelf", "-S", "-W", elf).stdout.splitlines():
        p = line.replace("[ ", "[").split()
        if len(p) > 6 and p[0].startswith("[") and p[2] in ("PROGBITS", "NOBITS") and "A" in p[7] and int(p[3], 16):
            starts.append(f"--section-start={p[1]}=0x{p[3]}")
    order = f"{out}/{f}.order"
    names = sorted(((fn["entry"], fn["name"]) for fn in chk["functions"]))
    open(order, "w").write("".join(n + "\n" for _, n in names))
    r = run(lld, "-static", "-e", t["driver"], "--build-id=none", "-z", "noseparate-code", *starts,
            f"--symbol-ordering-file={order}", o, "-o", re_)
    if r.returncode: print(f"FAIL {f}: relink: {r.stderr}"); status = 1; continue
    text = lambda e: run("llvm-objcopy", "-O", "binary", "--only-section=.text", e, "/dev/stdout").stdout
    if text(elf) != text(re_):
        print(f"FAIL {f}: the text does not round-trip"); status = 1; continue
    sym = next((n for n in levels if run("llvm-cxxfilt", n).stdout.strip().startswith(t["symbol"])), None)
    if sym is None:
        print(f"FAIL {f}: no function {t['symbol']}"); status = 1; continue
    dst = f"examples/elf/bench-{f}.elf"
    h = hashlib.sha256(open(elf, "rb").read()).hexdigest()
    manifest[f] = {"elf": dst, "sha256": h, "driver": t["driver"], "symbol": sym,
                   "level": levels[sym], "functions": len(levels)}
    if mode == "--update":
        shutil.copy(elf, dst)
    elif not os.path.exists(dst) or hashlib.sha256(open(dst, "rb").read()).hexdigest() != h:
        print(f"{f}: the build differs from {dst}"); status = 1
    print(f"ok   {f}: {len(levels)} functions, {sym} at {levels[sym]}, text round-trips")
if mode == "--update":
    json.dump(manifest, open("examples/refine/bench/manifest.json", "w"), indent=1, sort_keys=True)
sys.exit(status)
PY
