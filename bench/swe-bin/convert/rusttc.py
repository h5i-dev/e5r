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
import subprocess

SWB = os.environ.get("SWB", "/mnt/scratch/ec2-user/swe-bin")
RUSTUP_HOME = "/mnt/scratch/ec2-user/rustup"
CARGO_HOME = "/mnt/scratch/ec2-user/cargo"
TARGET = "riscv64imafd-unknown-linux-musl"


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


def install(date: dt.date) -> str:
    """The first nightly on or after `date` that installs with rust-src (some days lack one)."""
    last = ""
    for k in range(10):
        tc = f"nightly-{(date + dt.timedelta(days=k)).isoformat()}"
        if installed(tc):
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
    return install(dt.date.fromisoformat(out))


def setup(tc: str) -> dict:
    """The target spec path and the flags `tc` understands; cached per toolchain."""
    d = os.path.join(SWB, "tc", "rust", tc)
    meta = os.path.join(d, "meta.json")
    if os.path.exists(meta):
        with open(meta) as fh:
            return json.load(fh)
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
    m = {"toolchain": tc, "target": path,
         "jump_tables_flag": jt,
         "json_target_flag": "-Zjson-target-spec" if "json-target-spec" in cargo_z else ""}
    with open(meta, "w") as fh:
        json.dump(m, fh, indent=1)
    return m
