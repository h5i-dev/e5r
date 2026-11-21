"""The Rust toolchain for a task: the nightly of the base commit's date.

A 2026 nightly does not build 2019-2024 trees: crates that detect a nightly compiler turn on
unstable features that have since changed (proc-macro2's `proc_macro_span_shrink`, rustix's
`rustc_layout_scalar_valid_range_*`), and old dependencies no longer type-check (plist). The
nightly from the day of the base commit is the compiler those trees were built with, and it still
has `-Zbuild-std`, which rebuilds std for the no-C target.

For each toolchain this module installs it (minimal profile plus rust-src) under the scratch
RUSTUP_HOME, writes the no-C target spec from that toolchain's own `riscv64gc-unknown-linux-musl`
spec (the spec format changes between versions), and finds out which flags it supports.
"""

from __future__ import annotations

import datetime as dt
import json
import os
import shutil
import subprocess

SWB = os.environ.get("SWB", "/mnt/scratch/ec2-user/swe-bin")
RUSTUP_HOME = "/mnt/scratch/ec2-user/rustup"
CARGO_HOME = "/mnt/scratch/ec2-user/cargo"
TARGET = "riscv64imafd-unknown-linux-musl"
# the current nightly: for repositories without a Cargo.lock (recipes.RustProgram.toolchain)
LOCK_TOOLCHAIN = "nightly-2026-11-01"
# Older std does not build for the target: nightly-2021-10's libc 0.2.106 has no riscv64 musl
# (709 errors), and nightly-2022-03-01's std uses SYS_clone3, which its libc does not define
# for riscv64 musl (sharkdp__bat-1892). nightly-2022-11-04 builds (sharkdp__bat-2393).
FLOOR = dt.date(2022, 11, 1)


def _env():
    e = dict(os.environ)
    e.update(RUSTUP_HOME=RUSTUP_HOME, CARGO_HOME=CARGO_HOME)
    e["PATH"] = f"{CARGO_HOME}/bin:{e['PATH']}"
    return e


def _run(args, check=True):
    p = subprocess.run(args, env=_env(), stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    if check and p.returncode != 0:
        raise RuntimeError(f"{' '.join(args)}: {p.stdout.decode()[-800:]}")
    return p.stdout.decode()


def installed(tc: str) -> bool:
    return os.path.isdir(os.path.join(RUSTUP_HOME, "toolchains", f"{tc}-x86_64-unknown-linux-gnu"))


def _locked(fn):
    """One installation at a time (two converters installing the same nightly at once leave it
    without its manifest)."""
    def run(*a):
        import fcntl
        os.makedirs(os.path.join(SWB, "tc"), exist_ok=True)
        with open(os.path.join(SWB, "tc", "rustup.lock"), "w") as lk:
            fcntl.flock(lk, fcntl.LOCK_EX)
            return fn(*a)
    return run


def works(tc: str) -> bool:
    return subprocess.run(["rustc", f"+{tc}", "--version"], env=_env(), stdout=subprocess.DEVNULL,
                          stderr=subprocess.DEVNULL).returncode == 0


@_locked
def install(date: dt.date) -> str:
    """The first nightly on or after `date` that installs with rust-src (some days lack one)."""
    last = ""
    for k in range(10):
        tc = f"nightly-{(date + dt.timedelta(days=k)).isoformat()}"
        if installed(tc) and works(tc):
            return tc
        p = subprocess.run(["rustup", "toolchain", "install", tc, "--profile", "minimal",
                            "-c", "rust-src", "--no-self-update"], env=_env(),
                           stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        if p.returncode == 0:
            return tc
        last = p.stdout.decode()[-300:]
    raise RuntimeError(f"no nightly with rust-src within 10 days of {date}: {last}")


def for_commit(repo_dir: str, commit: str) -> str:
    out = subprocess.run(["git", "-C", repo_dir, "show", "-s", "--format=%cs", commit],
                         stdout=subprocess.PIPE, check=True).stdout.decode().strip()
    return install(max(dt.date.fromisoformat(out), FLOOR))


@_locked
def setup(tc: str) -> dict:
    """The target spec path and the flags `tc` understands; cached per toolchain."""
    d = os.path.join(SWB, "tc", "rust", tc)
    meta = os.path.join(d, "meta.json")
    if os.path.exists(meta):
        with open(meta) as fh:
            m = json.load(fh)
        # a meta from before the std was installed (or a std removed since) is redone
        if m.get("sysroot_std") and os.path.exists(os.path.join(m["sysroot_std"], ".swe-bin-std")):
            return m
    os.makedirs(d, exist_ok=True)
    spec = json.loads(_run(["rustc", f"+{tc}", "-Z", "unstable-options", "--print", "target-spec-json",
                            "--target", "riscv64gc-unknown-linux-musl"]))
    feats = [f for f in spec["features"].split(",") if f and f != "+c"]
    spec["features"] = ",".join(feats)
    spec["position-independent-executables"] = False
    spec["crt-static-default"] = True
    spec["crt-static-allows-dylibs"] = True  # else rustc prints no cdylib name and old cargo fails
    # "dynamic-linking" stays as the base target has it: older cargo parses a dylib name from
    # `rustc --print=file-names`, which a target without dynamic linking does not print
    spec.pop("is-builtin", None)  # older specs carry it; a JSON target must not
    if isinstance(spec.get("metadata"), dict):
        spec["metadata"]["description"] = "RISC-V Linux musl, rv64imafd (no C extension), static; swe-bin"
    path = os.path.join(d, f"{TARGET}.json")
    with open(path, "w") as fh:
        json.dump(spec, fh, indent=2, sort_keys=True)
    chelp = _run(["rustc", f"+{tc}", "-C", "help"], check=False)
    zhelp = _run(["rustc", f"+{tc}", "-Z", "help"], check=False)
    cargo_z = _run(["cargo", f"+{tc}", "-Z", "help"], check=False)
    if "jump-tables" in chelp:
        jt = "-C jump-tables=no"
    elif "no-jump-tables" in zhelp:
        jt = "-Z no-jump-tables"
    else:
        jt = ""
    # newer rustc wants -Zunstable-options for any custom target, newer cargo -Zjson-target-spec
    unstable = "-Zunstable-options" if "json-target-spec" in cargo_z else ""
    m = {"toolchain": tc, "target": path, "unstable_flag": unstable,
         "sysroot_std": install_std(tc, path, f"{jt} {unstable}", cargo_z),
         "jump_tables_flag": jt,
         "json_target_flag": "-Zjson-target-spec" if "json-target-spec" in cargo_z else ""}
    with open(meta, "w") as fh:
        json.dump(m, fh, indent=1)
    return m


# The flags std is built with: the same code generation as the programs (recipes.RV_RUSTFLAGS
# without the link arguments).
STD_RUSTFLAGS = ("-C target-feature=+zba,+zbb,-relax -C code-model=medium -C relocation-model=static "
                 "-C debuginfo=1 -C embed-bitcode=yes -Awarnings")  # bitcode: for projects built with LTO (bat)


def install_std(tc: str, spec: str, jt: str, cargo_z: str) -> str:
    """Build std for the no-C target once, and install it into the toolchain's sysroot
    (lib/rustlib/<target>/lib), as xargo did before -Zbuild-std. A project then builds with the
    plain `--target`, and build scripts that probe the target's std (autocfg: indexmap 1.x sets
    its default hasher only when it finds std) find it. With -Zbuild-std they do not, and
    plist 1.1 does not compile (sharkdp__bat-1892)."""
    sysroot = _run(["rustc", f"+{tc}", "--print", "sysroot"]).strip()
    dst = os.path.join(sysroot, "lib", "rustlib", TARGET, "lib")
    if os.path.exists(os.path.join(dst, ".swe-bin-std")):
        return dst
    shutil.rmtree(dst, ignore_errors=True)
    work = os.path.join(SWB, "tc", "rust", tc, "std-build")
    os.makedirs(os.path.join(work, "src"), exist_ok=True)
    with open(os.path.join(work, "Cargo.toml"), "w") as fh:
        fh.write('[package]\nname = "swb_std"\nversion = "0.0.0"\nedition = "2018"\n[lib]\npath = "src/lib.rs"\n'
                 '[profile.release]\npanic = "unwind"\n')
    with open(os.path.join(work, "src", "lib.rs"), "w") as fh:
        fh.write("pub fn f() -> usize { std::env::args().count() }\n")
    e = _env()
    # by name, through RUST_TARGET_PATH: rustc records a target given as a path with a hash of
    # the path in the crates' triple, and a project built by name would not find them
    e.update(RUSTFLAGS=f"{STD_RUSTFLAGS} {jt}", CARGO_TARGET_DIR=os.path.join(work, "target"),
             PATH=f"{SWB}/tc/bin:{e['PATH']}", RUST_TARGET_PATH=os.path.dirname(spec))
    args = ["cargo", f"+{tc}", "build", "--release", "-Zbuild-std=std,panic_unwind,proc_macro",
            "--target", TARGET]
    if "json-target-spec" in cargo_z:
        args.insert(4, "-Zjson-target-spec")
    p = subprocess.run(args, cwd=work, env=e, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    if p.returncode != 0:
        raise RuntimeError(f"std for {tc}: {p.stdout.decode()[-1500:]}")
    # release/deps/ in older cargo; release/build/<crate>/<hash>/out/ in the 2026 layout
    os.makedirs(dst, exist_ok=True)
    n = 0
    for root, _, files in os.walk(os.path.join(work, "target", TARGET, "release")):
        for f in files:
            # .rmeta too: newer rustc keeps the full metadata there, and the rlib has a stub
            if f.endswith((".rlib", ".rmeta")) and not f.startswith("libswb_std"):
                shutil.copy(os.path.join(root, f), os.path.join(dst, f))
                n += 1
    if n == 0:
        raise RuntimeError(f"std for {tc}: no rlib built")
    open(os.path.join(dst, ".swe-bin-std"), "w").close()
    return dst
