"""Per-repository build and test recipes for the riscv64 conversion.

A recipe builds the SUBJECT (the static riscv64 ELF the agent edits) in a checkout and runs the
SWE-bench test command with the subject replaced by a wrapper, `exec qemu-riscv64-static ELF`.
The tests themselves run on the host as in SWE-bench (no riscv64 binfmt here). The wrapper can
point at any ELF: the base build, the gold build, or a submission.

Every command a recipe runs is recorded in the task JSON (`recipe`), so a build can be
reproduced by hand.
"""

from __future__ import annotations

import os
import re
import datetime
import glob
import json
import shlex
import shutil
import subprocess
import sys
import subprocess
from dataclasses import dataclass, field

SWB = os.environ.get("SWB", "/mnt/scratch/ec2-user/swe-bin")
QEMU = os.environ.get("QEMU", "/mnt/scratch/ec2-user/bin/qemu-riscv64-static")
TC_BIN = f"{SWB}/tc/bin"
JOBS = os.environ.get("SWB_JOBS", "4")


def env():
    e = dict(os.environ)
    e["PATH"] = f"{TC_BIN}:{e['PATH']}"
    e["TERM"] = "dumb"
    return e


class Failed(Exception):
    def __init__(self, stage: str, detail: str):
        super().__init__(f"{stage}: {detail}")
        self.stage, self.detail = stage, detail


@dataclass
class Log:
    path: str
    commands: list = field(default_factory=list)

    def run(self, cmd: str, cwd: str, stage: str, timeout: int = 3600, check: bool = True) -> str:
        self.commands.append({"stage": stage, "cwd": os.path.basename(cwd), "cmd": cmd})
        with open(self.path, "a") as fh:
            fh.write(f"\n$ ({stage}) {cmd}\n")
        try:
            p = subprocess.run(["bash", "-c", cmd], cwd=cwd, env=env(), stdout=subprocess.PIPE,
                               stderr=subprocess.STDOUT, timeout=timeout)
        except subprocess.TimeoutExpired as e:
            out = (e.stdout or b"").decode("utf-8", "replace")
            with open(self.path, "a") as fh:
                fh.write(out + f"\n[timeout after {timeout}s]\n")
            if check:
                raise Failed(stage, f"timeout after {timeout}s: {cmd}")
            return out
        out = p.stdout.decode("utf-8", "replace")
        with open(self.path, "a") as fh:
            fh.write(out + f"\n[exit {p.returncode}]\n")
        if check and p.returncode != 0:
            tail = "\n".join(out.splitlines()[-15:])
            raise Failed(stage, f"exit {p.returncode}: {cmd}\n{tail}")
        return out


def wrapper(path: str, elf: str):
    """Replace PATH (in a checkout) with a script that runs ELF under qemu."""
    if os.path.lexists(path):
        os.remove(path)
    with open(path, "w") as fh:
        # -0 "$0": the program sees the wrapper's path as argv[0] (redis-check-aof is redis-server)
        fh.write(f"#!/bin/sh\nexec {shlex.quote(QEMU)} -0 \"$0\" {shlex.quote(elf)} \"$@\"\n")
    os.chmod(path, 0o755)


# ---- log parsers (statuses: PASSED / FAILED / SKIPPED) -----------------------------------------

def parse_automake(log: str) -> dict:
    r = {}
    for m in re.finditer(r"^(PASS|FAIL|ERROR|SKIP|XFAIL|XPASS): (\S+)", log, re.M):
        s = {"PASS": "PASSED", "XFAIL": "PASSED", "SKIP": "SKIPPED"}.get(m.group(1), "FAILED")
        r[m.group(2)] = s
    return r


class Recipe:
    current: dict = {}  # subject path -> the ELF the tests run (set by the converter)
    name = ""
    language = ""
    subjects: list = []  # paths in the checkout of the riscv64 ELFs the agent may edit
    excluded_tests: dict = {}  # regex -> reason, for dataset tests that do not run a subject

    def prepare(self, wt: str, log: Log):
        pass

    def build(self, wt: str, log: Log):
        raise NotImplementedError

    def reset_generated(self, wt: str, log: Log):
        """Undo what a build did to tracked files, so that a patch applies."""
        log.run("git checkout -q -- . && git clean -fdq -e '*.rv.elf'", wt, "reset")

    def run_tests(self, wt: str, task: dict, log: Log) -> str:
        raise NotImplementedError

    def refresh(self, wt: str, log: Log):
        """Bring the build tree up to date before the harness puts the wrappers in, so that the
        test command does not rebuild a subject over its wrapper."""

    def parse(self, out: str) -> dict:
        raise NotImplementedError

    def excluded(self, test: str):
        for rx, why in self.excluded_tests.items():
            if re.fullmatch(rx, test):
                return why
        return None


class Jq(Recipe):
    name = "jq"
    language = "C"
    subjects = ["jq"]
    excluded_tests = {
        r"(?!tests/).*": "oniguruma's own test programs (modules/oniguruma/test), not a test of jq",
    }
    CONFIGURE = ("./configure --host=riscv64-linux-musl CC=rv-cc CFLAGS='-O2 -g' "
                 "--with-oniguruma=builtin --disable-docs --disable-shared --enable-static "
                 "--enable-all-static")

    def prepare(self, wt, log):
        log.run("git submodule update --init -q", wt, "prepare")

    def build(self, wt, log):
        log.run("autoreconf -fi", wt, "build")
        log.run(self.CONFIGURE, wt, "build")
        # as the SWE-bench eval script does: regenerate the parser and lexer
        log.run("touch src/parser.y src/lexer.l", wt, "build")
        log.run(f"make -j{JOBS}", wt, "build", timeout=3600)

    def reset_generated(self, wt, log):
        log.run("git checkout -q -- . && git clean -fdxq -e '*.rv.elf' && git submodule foreach -q git clean -fdxq",
                wt, "reset")

    def refresh(self, wt, log):
        # `make -o jq check` keeps the top make from rebuilding jq, but -o is not passed to
        # sub-makes: the tree has to be up to date
        if os.path.lexists(os.path.join(wt, "jq")):
            os.remove(os.path.join(wt, "jq"))
        log.run("touch src/parser.y src/lexer.l", wt, "refresh")
        log.run(f"make -j{JOBS}", wt, "refresh", timeout=3600)

    def run_tests(self, wt, task, log):
        # only jq's own tests: oniguruma's are riscv64 programs of their own (excluded above);
        # -o jq keeps make from rebuilding the wrapper
        return log.run("make -o jq check SUBDIRS= ; true", wt, "test", timeout=3600, check=False)

    def parse(self, out):
        return parse_automake(out)


def parse_micropython(log: str) -> dict:
    r = {}
    for m in re.finditer(r"^(pass|FAIL|skip|lrge)\s+(\S+)", log, re.M):
        r[m.group(2)] = {"pass": "PASSED", "FAIL": "FAILED"}.get(m.group(1), "SKIPPED")
    return r


class MicroPython(Recipe):
    name = "micropython-unix-standard"
    language = "C"
    subjects = ["ports/unix/build-standard/micropython"]
    # the unix port, VARIANT=standard, cross-compiled. FFI is off: libffi is a separate
    # autotools build, and none of the C tasks' tests use ffi
    MAKE = ("make -C ports/unix VARIANT=standard CROSS_COMPILE=riscv64-linux-musl- "
            "MICROPY_PY_FFI=0 LDFLAGS_EXTRA=-static CFLAGS_EXTRA='-g -Wno-error' STRIP=: ")

    def prepare(self, wt, log):
        log.run("make -C ports/unix VARIANT=standard submodules", wt, "prepare")

    def build(self, wt, log):
        log.run(f"make -j{JOBS} -C mpy-cross", wt, "build")  # host tool (the bytecode compiler)
        log.run(f"{self.MAKE} -j{JOBS}", wt, "build")

    def reset_generated(self, wt, log):
        log.run("git checkout -q -- . && git clean -fdxq -e '*.rv.elf' && git submodule foreach -q 'git clean -fdxq; git checkout -q -- .'",
                wt, "reset")

    def run_tests(self, wt, task, log):
        cmd = test_line(task).replace("MICROPY_CPYTHON3=python3", "MICROPY_CPYTHON3=python3")
        return log.run(f"{cmd} ; true", wt, "test", timeout=3600, check=False)

    def parse(self, out):
        return parse_micropython(out)


class RedisLike(Recipe):
    """redis and valkey: the server and the cli are subjects; the Tcl test suite runs on the host."""
    language = "C"
    MAKE = ("make CC=rv-cc AR=llvm-ar RANLIB=llvm-ranlib MALLOC=libc BUILD_TLS=no USE_SYSTEMD=no "
            "uname_S=Linux uname_M=riscv64 OPTIMIZATION=-O2 CFLAGS=-g LDFLAGS=-static")

    def __init__(self, prog):
        self.prog = prog
        self.name = f"{prog}-libc-malloc"
        self.subjects = [f"src/{prog}-server", f"src/{prog}-cli"]
        # other riscv64 programs the suite runs: wrapped, not editable
        self.aux = [f"src/{prog}-benchmark", f"src/{prog}-check-aof", f"src/{prog}-check-rdb"]
        # the cli has no test of its own in this suite: its tests drive the server
        self.excluded_tests = {}

    def build(self, wt, log):
        log.run(f"{self.MAKE} -j{JOBS}", wt, "build", timeout=3600)
        for a in self.aux:
            p = os.path.join(wt, a)
            if os.path.exists(p) and not os.path.islink(p):
                os.replace(p, p + ".rv.elf")
                wrapper(p, p + ".rv.elf")

    def run_tests(self, wt, task, log):
        return log.run(f"{test_line(task)} ; true", wt, "test", timeout=5400, check=False)

    def parse(self, out):
        r = {}
        for m in re.finditer(r"^\[(ok|err|exception|skip|ignore)\]:\s+(.*?)(?:\s+\(\d+ ms\))?\s*$", out, re.M):
            name = re.sub(r" in tests/\S+\.tcl$", "", m.group(2))  # "[err]: NAME in tests/unit/x.tcl"
            st = {"ok": "PASSED", "skip": "SKIPPED", "ignore": "SKIPPED"}.get(m.group(1), "FAILED")
            if r.get(name) != "FAILED":  # a test reported twice counts as failed if either says so
                r[name] = st
        return r


sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import rusttc  # noqa: E402

RV_RUSTFLAGS = ("-C linker=rv-cc -C link-self-contained=no -C target-feature=+zba,+zbb,-relax "
                "-C code-model=medium -C relocation-model=static -C debuginfo=1 "
                "-C link-arg=-Wl,--emit-relocs -C link-arg=-lgcc -C link-arg=-lswb_lfs64 -Awarnings")
# -lgcc: old rustc links -nodefaultlibs, and musl's printf needs the long double builtins.
# -lswb_lfs64: stat64 and the other LFS64 names, which std from 2022 and earlier links
# (toolchain/build-sysroot.sh)


def rust_env_prefix(target_dir: str) -> str:
    t = "riscv64imafd_unknown_linux_musl"
    return (f"RUSTUP_HOME={rusttc.RUSTUP_HOME} CARGO_HOME={rusttc.CARGO_HOME} "
            f"CARGO_TARGET_DIR={target_dir} CC_{t}=rv-cc CXX_{t}=rv-c++ AR_{t}=llvm-ar CFLAGS_{t}=-g ")


class RustProgram(Recipe):
    """A Rust program whose integration tests run it as a child process (bat, rg, coreutils, nu).

    The subject is the program, built --release for riscv64 (the no-C target, its std installed in
    the toolchain by rusttc.install_std). The
    tests are the SWE-bench command, built for the host. Every copy of the host program that the
    tests can find (target/debug/P, deps/P-HASH, which cargo copies to target/debug/P on each run,
    and P next to a test executable, where assert_cmd looks) is replaced by the qemu wrapper.
    Tests in a test executable that does not run the program are excluded (see judge)."""
    language = "Rust"

    def __init__(self, name, bins, package_args=""):
        self.name = name
        self.bins = bins  # cargo bin target names
        self.subjects = [f"rv/{b}" for b in bins]  # copied here from the riscv64 target dir
        self.package_args = package_args  # cargo args selecting the bin's package

    def dirs(self, wt):
        # shared by the tasks of one repository (the converter runs them one at a time), so
        # that dependencies and the rebuilt std are compiled once
        root = os.path.join(SWB, "cargo-target", self.name)
        return os.path.join(root, "rv"), os.path.join(root, "host")

    def toolchain(self, wt, log):
        head = subprocess.run(["git", "-C", wt, "rev-parse", "HEAD"], stdout=subprocess.PIPE,
                              check=True).stdout.decode().strip()
        try:
            tracked = subprocess.run(["git", "-C", wt, "ls-files", "--error-unmatch", "Cargo.lock"],
                                     stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL).returncode == 0
            if tracked:
                self.tc = rusttc.for_commit(wt, head)
            else:
                # no lock file (axum): dependencies resolve today, as SWE-bench's images resolved
                # them when they were built, so the compiler is a current one. A lock resolved as
                # of the commit date does not work: some of those versions are yanked now
                self.tc = rusttc.LOCK_TOOLCHAIN
            self.tcm = rusttc.setup(self.tc)
        except RuntimeError as e:
            raise Failed("toolchain", str(e))
        log.commands.append({"stage": "toolchain", "cwd": "", "cmd": f"# {json.dumps(self.tcm)}"})
        return self.tc

    def target_env(self):
        # the no-C target by name, with its std installed in the toolchain (rusttc.install_std)
        return f"RUST_TARGET_PATH={os.path.dirname(self.tcm['target'])} "

    def build(self, wt, log):
        tc = self.toolchain(wt, log)
        rv, _ = self.dirs(wt)
        bins = " ".join(f"--bin {b}" for b in self.bins)
        flags = f"{RV_RUSTFLAGS} {self.tcm['jump_tables_flag']}"
        cmd = (f"{rust_env_prefix(rv)}{self.target_env()}RUSTFLAGS='{flags}' cargo +{tc} build --release "
               f"-j{JOBS} {self.package_args} {bins} --target {rusttc.TARGET}")
        try:
            log.run(cmd, wt, "build", timeout=7200)
        except Failed as e:
            # an old libc without riscv64 musl: bump libc only (recorded in the task's commands)
            if "could not compile `libc`" not in e.detail:
                raise
            log.run(f"{rust_env_prefix(rv)}cargo +{tc} update -p libc --precise 0.2.155", wt, "build-libc-bump")
            log.run(cmd, wt, "build", timeout=7200)
        os.makedirs(os.path.join(wt, "rv"), exist_ok=True)
        for b in self.bins:
            shutil.copy(os.path.join(rv, "riscv64imafd-unknown-linux-musl", "release", b), os.path.join(wt, "rv", b))

    def reset_generated(self, wt, log):
        # keeps a libc bump (Cargo.lock) through the reset: the gold build uses the same lock
        lock = os.path.join(wt, "Cargo.lock")
        saved = open(lock, "rb").read() if os.path.exists(lock) else None
        log.run("git checkout -q -- . && git clean -fdq", wt, "reset")
        if saved is not None:
            with open(lock, "wb") as fh:
                fh.write(saved)

    def _cargo_test(self, task):
        t = test_line(task)
        m = re.match(r"^((?:\w+=(?:\"[^\"]*\"|\S+)\s+)*)cargo test (.*)$", t)
        if not m:
            raise Failed("test", f"not a cargo test command: {t}")
        return m.group(1), m.group(2)

    def run_tests(self, wt, task, log):
        _, host = self.dirs(wt)
        envs, args = self._cargo_test(task)
        # cargo's own args are before "--"; --no-run takes no test-binary args
        cargo_args = args.split(" -- ")[0]
        pre = f"{rust_env_prefix(host)}{envs}"
        tc = self.tc
        out = log.run(f"{pre}cargo +{tc} test -j{JOBS} {cargo_args} --no-run --message-format=json "
                      f"2>/dev/null", wt, "test-build", timeout=7200, check=False)
        exes = []
        for line in out.splitlines():
            try:
                j = json.loads(line)
            except json.JSONDecodeError:
                continue
            if j.get("reason") == "compiler-artifact" and j.get("executable") and j["profile"]["test"]:
                exes.append(j["executable"])
        if not exes:
            raise Failed("test-build", "the host tests did not build")
        elfs = {b: self.current[f"rv/{b}"] for b in self.bins}
        for b in self.bins:
            places = [os.path.join(host, "debug", b)]
            places += [p for p in glob.glob(os.path.join(host, "debug", "deps", b + "-*"))
                       if not os.path.splitext(p)[1]]
            places += [os.path.join(os.path.dirname(e), b) for e in exes]
            for p in places:
                wrapper(p, elfs[b])
        return log.run(f"{pre}cargo +{tc} test -j{JOBS} {args} 2>&1 ; true", wt, "test",
                       timeout=5400, check=False)

    def parse(self, out):
        # tests in a unit-test executable (cargo prints "Running unittests ...") run host code
        # in-process, not the program: excluded
        unit = getattr(self, "unit_tests", set())
        section = ""
        for line in out.splitlines():
            m = re.match(r"^\s+Running (\S+)", line)
            if m:
                section = m.group(1)
            m = re.match(r"^test (\S+) \.\.\. ", line)
            if m and section == "unittests":
                unit.add(m.group(1))
        self.unit_tests = unit
        return parse_cargo(out)

    def excluded(self, test):
        if test in getattr(self, "unit_tests", set()):
            return "an in-process unit test of host code (cargo 'Running unittests'): it does not run the program"
        return super().excluded(test)


class RustTests(RustProgram):
    """Class B (tokio, axum, ruff): the tests are compiled into the ELF with the code under test.

    The subjects are the riscv64 test executables of the SWE-bench command, built at the base
    commit WITH the test patch (as SWE-bench builds them), in the dev profile at opt-level 2 with
    debug assertions kept. Each runs under qemu with the command's test filter and the arguments
    after `--`, from its package's directory. Lead decision (Q1, 12:28 UTC): the submission is
    that test ELF, and run_tests/submit reject a binary whose functions outside the crates under
    test differ from base; the tests being visible in the binary is a recorded deviation."""

    build_with_test_patch = True
    deviation = ("class B: the FAIL_TO_PASS tests are compiled into the submitted test ELF, so "
                 "they are visible in it (in SWE-bench they are hidden); functions outside the "
                 "crates under test must stay byte-identical to base")

    def __init__(self, name):
        super().__init__(name, [])
        self.subjects = []

    def _parts(self, task):
        envs, args = self._cargo_test(task)
        cargo_part, _, after = args.partition(" -- ")
        toks = shlex.split(cargo_part)
        cargo_opts, filt, i = [], [], 0
        takes_value = {"--package", "-p", "--test", "--features", "--bin", "--example", "--bench"}
        while i < len(toks):
            t = toks[i]
            if t in takes_value and i + 1 < len(toks):
                cargo_opts += [t, toks[i + 1]]
                i += 2
            elif t.startswith("-"):
                cargo_opts.append(t)
                i += 1
            else:
                filt.append(t)
                i += 1
        cargo_opts = [o for o in cargo_opts if o != "--no-fail-fast"]
        return envs, cargo_opts, filt + shlex.split(after)

    def build(self, wt, log):
        tc = self.toolchain(wt, log)
        rv, _ = self.dirs(wt)
        envs, cargo_opts, _ = self._parts(self.task)
        rustflags = f"{RV_RUSTFLAGS} {self.tcm['jump_tables_flag']}"
        m = re.search(r"RUSTFLAGS=(\"[^\"]*\"|\S+)", envs)
        if m:  # e.g. --cfg tokio_unstable
            rustflags += " " + m.group(1).strip('"').replace("-Awarnings", "")
        cmd = (f"{rust_env_prefix(rv)}CARGO_PROFILE_DEV_OPT_LEVEL=2 "
               f"{self.target_env()}RUSTFLAGS='{rustflags}' cargo +{tc} test --no-run -j{JOBS} "
               f"{' '.join(map(shlex.quote, cargo_opts))} --target {rusttc.TARGET} "
               f"--message-format=json 2>/dev/null")
        out = log.run(cmd, wt, "build", timeout=7200, check=False)
        exes = []
        for line in out.splitlines():
            try:
                j = json.loads(line)
            except json.JSONDecodeError:
                continue
            if j.get("reason") == "compiler-artifact" and j.get("executable") and j["profile"]["test"]:
                kind = j["target"]["kind"][0]
                name = j["target"]["name"] + ("" if kind == "test" else f"-{kind}")
                exes.append((name, j["executable"], os.path.dirname(j["manifest_path"])))
            if j.get("reason") == "build-finished" and not j.get("success"):
                # show the compiler's errors
                log.run(cmd.replace("--message-format=json 2>/dev/null", "2>&1 | tail -40"), wt, "build-errors",
                        timeout=7200, check=False)
                raise Failed("build", "the test executables did not build (with the test patch at this commit)")
        if not exes:
            raise Failed("build", "no test executable")
        os.makedirs(os.path.join(wt, "rv-tests"), exist_ok=True)
        self.subjects, self.pkg_dirs = [], {}
        for name, exe, pkg in sorted(exes):
            rel = f"rv-tests/{name}"
            shutil.copy(exe, os.path.join(wt, rel))
            self.subjects.append(rel)
            self.pkg_dirs[rel] = os.path.relpath(pkg, wt)
        with open(os.path.join(wt, "rv-tests", "pkgdirs.json"), "w") as fh:
            json.dump(self.pkg_dirs, fh)
        # the crates under test: the workspace's own library crates (the integrity check)
        meta = log.run(f"{rust_env_prefix(rv)}cargo +{tc} metadata --no-deps --format-version 1 2>/dev/null",
                       wt, "metadata", check=False)
        crates = set()
        for line in meta.splitlines():
            if line.startswith("{"):
                for pk in json.loads(line).get("packages", []):
                    for tg in pk.get("targets", []):
                        if "lib" in tg.get("kind", []) or "proc-macro" in tg.get("kind", []):
                            crates.add(tg["name"].replace("-", "_"))
        self.editable = sorted(crates)

    def run_tests(self, wt, task, log):
        envs, _, exe_args = self._parts(task)
        pkg_dirs = getattr(self, "pkg_dirs", None)
        if not pkg_dirs:
            with open(os.path.join(wt, "rv-tests", "pkgdirs.json")) as fh:
                pkg_dirs = json.load(fh)
        out = []
        for rel, elf in self.current.items():
            pkg = os.path.join(wt, pkg_dirs.get(rel, "."))
            args = " ".join(shlex.quote(a) for a in exe_args)
            out.append(f"     Running {rel}")
            out.append(log.run(f"CARGO_MANIFEST_DIR={shlex.quote(pkg)} {shlex.quote(QEMU)} {shlex.quote(elf)} {args} 2>&1 ; true",
                               pkg, "test", timeout=5400, check=False))
        return "\n".join(out)

    def parse(self, out):
        return parse_cargo(out)

    def excluded(self, test):
        return Recipe.excluded(self, test)


def parse_cargo(out: str) -> dict:
    r = {}
    for m in re.finditer(r"^test (\S+) \.\.\. (ok|FAILED|ignored)", out, re.M):
        r[m.group(1)] = {"ok": "PASSED", "ignored": "SKIPPED"}.get(m.group(2), "FAILED")
    return r


def test_line(task) -> str:
    es = task["eval_script"]
    t = es.split(": '>>>>> Start Test Output'")[1].split(": '>>>>> End Test Output'")[0].strip()
    # "(cmd) | cat" -> "cmd"
    if t.startswith("(") and t.endswith(") | cat"):
        t = t[1:-len(") | cat")]
    return t


RECIPES = {"jqlang/jq": Jq(), "micropython/micropython": MicroPython(),
           "redis/redis": RedisLike("redis"), "valkey-io/valkey": RedisLike("valkey"),
           "sharkdp/bat": RustProgram("bat", ["bat"], "--package bat"),
           "burntsushi/ripgrep": RustProgram("ripgrep", ["rg"], "--package ripgrep"),
           "uutils/coreutils": RustProgram("coreutils", ["coreutils"], "--package coreutils"),
           "nushell/nushell": RustProgram("nushell", ["nu"], "--package nu"),
           "tokio-rs/tokio": RustTests("tokio"),
           "tokio-rs/axum": RustTests("axum"),
           "astral-sh/ruff": RustTests("ruff")}
