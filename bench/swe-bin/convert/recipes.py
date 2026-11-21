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
import shlex
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


def test_line(task) -> str:
    es = task["eval_script"]
    t = es.split(": '>>>>> Start Test Output'")[1].split(": '>>>>> End Test Output'")[0].strip()
    # "(cmd) | cat" -> "cmd"
    if t.startswith("(") and t.endswith(") | cat"):
        t = t[1:-len(") | cat")]
    return t


RECIPES = {"jqlang/jq": Jq(), "micropython/micropython": MicroPython(),
           "redis/redis": RedisLike("redis"), "valkey-io/valkey": RedisLike("valkey")}
