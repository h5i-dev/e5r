#!/usr/bin/env python3
"""Measure r12e against the other reverse engineering tools on this machine.

Driven by ``scripts/compare-tools.sh``, which finds the tools and checks they
run. This file does the measuring and nothing else.

Two jobs are timed per tool, because they are different questions and running
them together answers neither:

``load``     parse the container and report what is in it. No code analysis.
``recover``  find the functions, and nothing else the tool can be told to skip.
``analyze``  the tool's full analysis, then write out every function found.

Each tool gets the invocation its own documentation recommends for the job, and
the table says which command produced which row. Timing full analysis against a
container parse would be measuring the wrong thing, which is why they are
separate rows rather than one.

A count of functions on its own is close to meaningless: a tool reporting 4,000
where another reports 3,500 may be finding more or inventing more. So every
count is split against a symbol table:

  recall   the share of functions the symbol table names that the tool found
  extra    entries the tool reports that no FUNC symbol names

``extra`` is a false-positive count only where the oracle is complete, meaning
it came from a full ``.symtab``. Where the only symbols are the dynamic ones,
an unnamed entry is usually a real static function, so the column is reported
but is not a defect count, and ``oracle`` in the JSON says which it is.

Import thunks are excluded from both sides. They are real code with no FUNC
symbol, so counting them would charge a false positive to whichever tool is
more thorough.

Adding a tool is adding one entry to ``TOOLS``: a version probe, a load
command, and an analyze command that yields a set of entry point addresses.
Nothing above that knows how many tools there are.
"""

from __future__ import annotations

import argparse
import bisect
import hashlib
import json
import os
import re
import platform
import shutil
import subprocess
import sys
import tempfile
import time
from dataclasses import dataclass, field
from pathlib import Path

# Sections holding linker-generated call stubs. Entries inside them are real
# code that no FUNC symbol names, so they are excluded from the oracle
# comparison rather than charged to a tool as an invention.
PLT_SECTIONS = {".plt", ".plt.sec", ".plt.got", ".iplt", ".mplt"}


# ------------------------------------------------------- the ELF, from outside


@dataclass
class Layout:
    """What the ELF headers say about where code can be."""

    lo: int = 0
    hi: int = 0
    plt: list[tuple[int, int]] = field(default_factory=list)
    exec_ranges: list[tuple[int, int]] = field(default_factory=list)

    def in_file(self, addr: int) -> bool:
        return self.lo <= addr < self.hi

    def in_plt(self, addr: int) -> bool:
        return any(start <= addr < end for start, end in self.plt)

    def executable(self, addr: int) -> bool:
        """Is this address in a section the loader will make executable?

        Needed because the symbol table cannot settle a false positive on a
        stripped shared library: an entry no symbol names may be a real static
        function. An entry in a section that never becomes executable is not a
        function under any reading.
        """
        return any(start <= addr < end for start, end in self.exec_ranges)


def readelf(*args: str) -> str:
    """readelf rather than r12e: the oracle for a comparison r12e takes part
    in cannot be r12e."""
    return subprocess.run(
        ["readelf", *args], capture_output=True, text=True
    ).stdout


def layout(path: Path) -> Layout:
    """Allocated address range and PLT ranges."""
    lay = Layout()
    lo, hi = None, 0
    for line in readelf("-SW", str(path)).splitlines():
        m = re.match(
            r"\s*\[\s*\d+\]\s+(\S+)\s+(\S+)\s+([0-9a-f]+)\s+([0-9a-f]+)\s+([0-9a-f]+)",
            line,
        )
        if not m:
            continue
        name, _kind, addr, _off, size = m.groups()
        addr, size = int(addr, 16), int(size, 16)
        if addr == 0:
            continue
        lo = addr if lo is None else min(lo, addr)
        hi = max(hi, addr + size)
        if name in PLT_SECTIONS:
            lay.plt.append((addr, addr + size))
        # readelf's columns after the size are ES then the flag letters.
        rest = line[m.end():].split()
        if len(rest) >= 2 and "X" in rest[1]:
            lay.exec_ranges.append((addr, addr + size))
    lay.lo, lay.hi = lo or 0, hi
    return lay


def elf_base(path: Path) -> int:
    """Lowest virtual address of a loadable segment: zero for a PIE.

    A tool that relocates a position-independent image to an image base of its
    own has to be brought back to this before its addresses can be compared
    with anyone else's.
    """
    lows = [
        int(m.group(1), 16)
        for m in re.finditer(r"\n\s*LOAD\s+0x\S+\s+0x([0-9a-f]+)", readelf("-lW", str(path)))
    ]
    return min(lows) if lows else 0


def symbol_functions(path: Path) -> tuple[set[int], list[tuple[int, int]], bool]:
    """Function entries and extents from the symbol table, and whether it is
    complete.

    Complete means the static symbol table was present, which lists every
    function the compiler emitted. A dynamic-only table lists the exported ones
    and nothing else, so it bounds recall but says nothing about the rest.

    The extents matter as much as the entries. An address a tool reports that
    falls inside a function the symbol table already names is that tool
    splitting one function in two, which is a different mistake from inventing
    a function where there is no code, and the two should not share a column.
    """
    have_symtab = " .symtab " in readelf("-SW", str(path))
    out = readelf("-sW", str(path)) if have_symtab else readelf("-sW", "--dyn-syms", str(path))
    found: set[int] = set()
    extents: list[tuple[int, int]] = []
    for line in out.splitlines():
        parts = line.split()
        # Num: Value Size Type Bind Vis Ndx Name
        if len(parts) < 8 or not parts[0].endswith(":"):
            continue
        if parts[3] != "FUNC" or parts[6] in ("UND", "ABS"):
            continue
        value = int(parts[1], 16)
        if value:
            # AArch64 and x86-64 only in this corpus, so no Thumb low bit to
            # clear. If ARM32 joins the corpus this needs `value & ~1`.
            found.add(value)
            size = int(parts[2], 0) if parts[2].isdigit() or parts[2].startswith("0x") else 0
            if size:
                extents.append((value, value + size))
    extents.sort()
    return found, extents, have_symtab


def oracle_for(path: Path) -> tuple[set[int], list[tuple[int, int]], str]:
    """The ground truth for one binary, and where it came from.

    A stripped fixture is measured against its own unstripped twin, which is
    the strongest oracle available: the same bytes at the same addresses, with
    every name the compiler emitted.
    """
    if str(path).endswith(".stripped"):
        twin = Path(str(path)[: -len(".stripped")])
        if twin.exists():
            syms, extents, complete = symbol_functions(twin)
            if complete:
                return syms, extents, "symtab of unstripped twin"
    syms, extents, complete = symbol_functions(path)
    return syms, extents, "symtab" if complete else "dynsym only"


# ------------------------------------------------------------------- running


# A run this long is not a measurement any more, it is a hang, and a benchmark
# that hangs is a benchmark nobody reruns. `timeout` reports 124, which the
# table prints as a timeout rather than as a failure: the distinction matters,
# because a tool that needs longer than the budget is a result.
TIMEOUT_EXIT = 124
DEFAULT_TIMEOUT = 1800


def run_timed(
    argv: list[str], stdout_path: Path | None, limit: int = DEFAULT_TIMEOUT
) -> tuple[float, int, int]:
    """Run once under /usr/bin/time; return seconds, peak RSS in KB, exit code.

    /usr/bin/time rather than a clock inside Python, because peak resident
    memory has to come from the kernel and taking both from one source keeps
    them describing the same run.
    """
    with tempfile.NamedTemporaryFile("r+", suffix=".time") as tf:
        cmd = [
            "/usr/bin/time", "-f", "%e %M", "-o", tf.name,
            "timeout", "-k", "5", str(limit), *argv,
        ]
        out = open(stdout_path, "wb") if stdout_path else subprocess.DEVNULL
        try:
            proc = subprocess.run(cmd, stdout=out, stderr=subprocess.DEVNULL)
        finally:
            if stdout_path:
                out.close()
        tf.seek(0)
        line = tf.read().strip().splitlines()[-1]
    secs, rss = line.split()
    return float(secs), int(rss), proc.returncode


def best_of(runs: int, once):
    """Take the fastest of several runs.

    The minimum, not the mean: other work on this machine can only make a run
    slower, so the fastest run is the closest estimate of the tool's own cost.
    """
    best_t, best_rss, payload = None, None, None
    for _ in range(runs):
        secs, rss, value = once()
        if value is None or isinstance(value, str):
            return (secs if value else float("nan")), rss, value
        if best_t is None or secs < best_t:
            best_t, payload = secs, value
        best_rss = rss if best_rss is None else min(best_rss, rss)
    return best_t, best_rss, payload


# --------------------------------------------------------------- the tools
#
# One class per tool, with one method per timed job. `recover` and `analyze`
# return the set of function entry points, which is what the scoring works on;
# `load` returns True, because nothing is counted from a container parse. Any
# of them may return the string "timeout" instead, which the table prints as a
# timeout rather than as a failure, because a tool needing longer than the
# budget is a result. A tool whose executable is not configured is skipped and
# said to be skipped, never quietly dropped from the table.


def outcome(code: int, value):
    """Turn an exit code into a payload: the value, a timeout, or a failure."""
    if code == TIMEOUT_EXIT:
        return "timeout"
    return None if code else value


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1 << 20), b""):
            digest.update(chunk)
    return digest.hexdigest()


def probe(argv: list[str]) -> str:
    try:
        out = subprocess.run(argv, capture_output=True, text=True, timeout=60)
        return (out.stdout or out.stderr).strip().splitlines()[0]
    except Exception:
        return "unknown"


class R12e:
    name = "r12e"

    def __init__(self, exe: str, limit: int = DEFAULT_TIMEOUT):
        self.exe = exe
        self.limit = limit

    def version(self) -> str:
        return probe([self.exe, "--version"])

    def load(self, binary: Path, work: Path):
        secs, rss, code = run_timed([self.exe, "info", str(binary), "--json"], None, self.limit)
        return secs, rss, outcome(code, True)

    def recover(self, binary: Path, work: Path):
        """Function recovery alone. Analysis is lazy, so listing functions
        forces nothing else."""
        out = work / "r12e-recover.json"
        secs, rss, code = run_timed(
            [self.exe, "funcs", str(binary), "--json"], out, self.limit
        )
        if code:
            return secs, rss, outcome(code, True)
        try:
            data = json.loads(out.read_text())
        except json.JSONDecodeError:
            return secs, rss, None
        return secs, rss, {int(f["addr"], 16) for f in data["items"]}

    def analyze(self, binary: Path, work: Path):
        """Time `r12e stats`, count what `r12e funcs` lists.

        `stats` is the command that does the whole job -- functions, control
        flow, cross references and strings -- which is what `rizin -A` also
        does. `funcs` alone is cheaper, because analysis is lazy and listing
        functions does not force the rest, and timing that against a tool doing
        everything would be measuring the wrong thing in our favour. The
        address set comes from a separate untimed `funcs` run.
        """
        secs, rss, code = run_timed([self.exe, "stats", str(binary), "--json"], None, self.limit)
        if code:
            return secs, rss, outcome(code, True)
        out = work / "r12e.json"
        if run_timed([self.exe, "funcs", str(binary), "--json"], out)[2] != 0:
            return secs, rss, None
        try:
            data = json.loads(out.read_text())
        except json.JSONDecodeError:
            return secs, rss, None
        return secs, rss, {int(f["addr"], 16) for f in data["items"]}


class Rizin:
    name = "rizin"

    def __init__(self, exe: str, limit: int = DEFAULT_TIMEOUT):
        self.exe = exe
        self.limit = limit
        # rz-bin ships beside rizin and is the documented way to ask about a
        # container without analyzing it.
        sibling = Path(exe).with_name("rz-bin")
        self.rz_bin = str(sibling) if sibling.exists() else "rz-bin"

    def version(self) -> str:
        return probe([self.exe, "-v"])

    def load(self, binary: Path, work: Path):
        # rz-bin, not rizin, for the container parse: rizin builds a whole
        # session around the file, which is not what this row is asking.
        secs, rss, code = run_timed([self.rz_bin, "-I", str(binary)], None, self.limit)
        return secs, rss, outcome(code, True)

    def recover(self, binary: Path, work: Path):
        # `aa` is rizin's own "analyze all (fcns + bbs)": function recovery
        # without the passes -A adds on top of it. This is the row that is
        # like for like against r12e's function recovery, and on this corpus
        # it is both much faster and much more accurate than -A.
        out = work / "rizin-aa.json"
        secs, rss, code = run_timed(
            [self.exe, "-N", "-q", "-c", "aa; aflj", str(binary)], out, self.limit
        )
        if code == TIMEOUT_EXIT:
            return secs, rss, "timeout"
        try:
            data = json.loads(out.read_text() or "[]")
        except json.JSONDecodeError:
            return secs, rss, None
        return secs, rss, {int(f["offset"]) for f in data}

    def analyze(self, binary: Path, work: Path):
        # -N so a user's rizinrc cannot change what is measured; -A is the
        # documented flag for full analysis; aflj lists what it found.
        out = work / "rizin.json"
        secs, rss, code = run_timed(
            [self.exe, "-N", "-q", "-A", "-c", "aflj", str(binary)], out, self.limit
        )
        if code == TIMEOUT_EXIT:
            return secs, rss, "timeout"
        try:
            data = json.loads(out.read_text() or "[]")
        except json.JSONDecodeError:
            return secs, rss, None
        return secs, rss, {int(f["offset"]) for f in data}


class Ghidra:
    """Ghidra headless, off unless GHIDRA_INSTALL_DIR names an installation.

    Kept working rather than deleted: the comparison the roadmap names is three
    ways, and a script that would have to be rewritten to add the third tool is
    a script that never gets it.
    """

    name = "ghidra"

    def __init__(self, install: str, timeout: int, scripts: Path):
        self.install = Path(install)
        self.timeout = timeout
        # Ghidra gets its own analysis timeout as well, so it stops itself
        # rather than being killed mid-write.
        self.limit = timeout + 300
        self.scripts = scripts

    def version(self) -> str:
        app = self.install / "Ghidra" / "application.properties"
        if app.exists():
            for line in app.read_text().splitlines():
                if line.startswith("application.version="):
                    return "Ghidra " + line.split("=", 1)[1]
        return "unknown"

    def _headless(self, binary: Path, work: Path, extra: list[str]):
        # A fresh project every run: importing into an existing project is a
        # no-op, which would report the previous run's analysis as this one's.
        proj = work / "gproj"
        shutil.rmtree(proj, ignore_errors=True)
        proj.mkdir(parents=True)
        argv = [
            str(self.install / "support" / "analyzeHeadless"),
            str(proj),
            "bench",
            "-import",
            str(binary),
            *extra,
            "-deleteProject",
        ]
        secs, rss, code = run_timed(argv, None, self.limit)
        shutil.rmtree(proj, ignore_errors=True)
        return secs, rss, code

    def load(self, binary: Path, work: Path):
        secs, rss, code = self._headless(binary, work, ["-noanalysis"])
        return secs, rss, outcome(code, True)

    def recover(self, binary: Path, work: Path):
        # Ghidra headless has no documented "functions only" analysis: the
        # analyzer set is all or a hand-picked list, and hand-picking one would
        # be us deciding what Ghidra's function recovery is. Left unmeasured.
        return float("nan"), 0, None

    def analyze(self, binary: Path, work: Path):
        dump = work / "ghidra.txt"
        if dump.exists():
            dump.unlink()
        secs, rss, code = self._headless(
            binary,
            work,
            [
                "-analysisTimeoutPerFile",
                str(self.timeout),
                "-scriptPath",
                str(self.scripts),
                "-postScript",
                "DumpFunctions.java",
                str(dump),
            ],
        )
        if code == TIMEOUT_EXIT:
            return secs, rss, "timeout"
        if not dump.exists():
            return secs, rss, None
        found, delta = set(), 0
        for line in dump.read_text().splitlines():
            if line.startswith("# imagebase "):
                delta = elf_base(binary) - int(line.split()[2], 16)
                continue
            parts = line.split(None, 3)
            if len(parts) >= 3:
                found.add(int(parts[0], 16) + delta)
        return secs, rss, found


# ------------------------------------------------------------------- scoring


def inside_any(addr: int, extents: list[tuple[int, int]]) -> bool:
    """Is this address inside the body of a function the symbol table names?"""
    i = bisect.bisect_right(extents, (addr, float("inf")))
    return i > 0 and extents[i - 1][0] <= addr < extents[i - 1][1]


def score(found, oracle: set[int], extents: list[tuple[int, int]], lay: Layout) -> dict:
    if isinstance(found, str):
        return {"ran": False, "why": found}
    if found is None:
        return {"ran": False, "why": "failed"}
    # A tool may report functions outside the file image: Ghidra puts imports
    # in a synthetic block past the end. Those are not functions in the binary.
    # Every tool is filtered the same way.
    inside = {a for a in found if lay.in_file(a)}
    plt = {a for a in inside if lay.in_plt(a)}
    real = inside - plt
    truth = {a for a in oracle if not lay.in_plt(a)}
    hit = real & truth
    # A miss where the tool reported an entry a few bytes into the same
    # function is a boundary disagreement, not a function it failed to find.
    # Counted separately rather than folded into recall, because the entry
    # point is what a caller jumps to and being four bytes late is wrong.
    ordered = sorted(real)
    near = sum(
        1
        for a in truth - real
        if (i := bisect.bisect_right(ordered, a)) < len(ordered) and ordered[i] <= a + 16
    )
    return {
        "ran": True,
        "reported": len(found),
        "in_file": len(inside),
        "plt": len(plt),
        "counted": len(real),
        "hit": len(hit),
        "missed": len(truth - real),
        "near": near,
        "extra": len(real - truth),
        # An extra inside a function the symbol table already names is that
        # function split in two, not a function invented out of data. A
        # boundary disagreement otherwise costs a tool twice, once in recall
        # and once here, which overstates invention.
        "extra_inside": sum(1 for a in real - truth if inside_any(a, extents)),
        # Independent of any symbol table: an entry in a section that is never
        # executable is not a function, whatever the symbols do or do not say.
        "non_executable": sum(1 for a in inside if not lay.executable(a)),
        "recall": round(len(hit) / len(truth), 4) if truth else None,
    }


# ------------------------------------------------------------------ explain


def symbol_names(path: Path) -> dict[int, str]:
    """Address to name, from whichever symbol table the file has."""
    have_symtab = " .symtab " in readelf("-SW", str(path))
    out = readelf("-sW", str(path)) if have_symtab else readelf("-sW", "--dyn-syms", str(path))
    names: dict[int, str] = {}
    for line in out.splitlines():
        parts = line.split()
        if len(parts) < 8 or not parts[0].endswith(":"):
            continue
        if parts[3] != "FUNC" or parts[6] in ("UND", "ABS"):
            continue
        value = int(parts[1], 16)
        if value:
            names.setdefault(value, parts[7])
    return names


def explain_run(results: Path, examples: int) -> int:
    """What each tool found that the others did not.

    A count is not an answer: two tools disagreeing by five hundred functions
    may differ by five hundred real functions one of them missed or by five
    hundred addresses the other invented. This prints the difference itself,
    with the symbol name where the binary has one, so the disagreement can be
    read rather than guessed at.
    """
    doc = json.loads(results.read_text())
    for row in doc["results"]:
        ran = {
            name: set(entry["addresses"])
            for name, entry in row["tools"].items()
            if entry.get("ran")
        }
        if len(ran) < 2:
            continue
        path = Path(row["path"])
        if not path.exists():
            print(f"\n{row['binary']}: gone from disk, cannot name addresses")
            continue
        lay = layout(path)
        # The same filtering the table used, so the counts here and there agree.
        ran = {
            name: {a for a in found if lay.in_file(a) and not lay.in_plt(a)}
            for name, found in ran.items()
        }
        twin = Path(str(path)[: -len(".stripped")]) if str(path).endswith(".stripped") else path
        names = symbol_names(twin if twin.exists() else path)
        print(f"\n{row['binary']}  ({row['oracle']}, {row['oracle_functions']} named)")
        for name, found in ran.items():
            others = set().union(*(v for k, v in ran.items() if k != name))
            only = sorted(found - others)
            named = [a for a in only if a in names]
            print(
                f"  {name:<8} {len(found):>6} found, {len(only):>5} that no other tool "
                f"reported, {len(named):>5} of those named by a symbol"
            )
            for addr in only[:examples]:
                print(f"      0x{addr:x}  {names.get(addr, '(no symbol here)')}")
            if len(only) > examples:
                print(f"      ... and {len(only) - examples} more")
    return 0


# ------------------------------------------------------------------ rescore


def rescore_run(results: Path) -> int:
    """Recompute the scoring from the addresses a run already recorded.

    Every run stores the entry points each tool reported, so a change to how
    they are scored does not need the tools rerun. Timing is left exactly as it
    was measured: this rewrites conclusions, never measurements.
    """
    doc = json.loads(results.read_text())
    for row in doc["results"]:
        path = Path(row["path"])
        if not path.exists():
            print(f"{row['binary']}: gone from disk, left as it was", file=sys.stderr)
            continue
        lay = layout(path)
        oracle, extents, source = oracle_for(path)
        row["oracle"], row["oracle_functions"] = source, len(oracle)
        for entry in row["tools"].values():
            if not entry.get("ran"):
                continue
            keep = ("load_seconds", "load_peak_kb", "seconds", "peak_kb", "addresses")
            fresh = score(set(entry["addresses"]), oracle, extents, lay)
            fresh.update({k: entry[k] for k in keep if k in entry})
            old = entry.get("recover")
            if old and old.get("ran"):
                rescored = score(set(old["addresses"]), oracle, extents, lay)
                rescored.update({k: old[k] for k in ("seconds", "peak_kb", "addresses") if k in old})
                fresh["recover"] = rescored
            elif old:
                fresh["recover"] = old
            entry.clear()
            entry.update(fresh)
    results.write_text(json.dumps(doc, indent=2) + "\n")
    print(f"rescored {results}")
    return 0


# ----------------------------------------------------------------- markdown


def markdown_run(results: Path) -> int:
    """Emit the tables in docs/benchmarks.md from a results file.

    The document's numbers are generated rather than transcribed, because a
    table copied by hand is a table that drifts from the run it claims to
    report.
    """
    doc = json.loads(results.read_text())
    tools = []
    for row in doc["results"]:
        for name in row["tools"]:
            if name not in tools:
                tools.append(name)

    def cell(row, tool, key, fmt):
        entry = row["tools"].get(tool)
        if not entry or not entry.get("ran") or entry.get(key) is None:
            return "n/a"
        return fmt(entry[key])

    machine = doc.get("machine", {})
    print(f"Measured {doc['when']}, load average "
          f"{', '.join(f'{x:.1f}' for x in doc['loadavg'])} at the end of the run.")
    print(f"Machine: {machine.get('uname', 'unknown')}, {machine.get('cpus', '?')} cores.")
    # Rows merged from separate passes can carry different run counts, and a
    # header claiming one number for all of them would be false.
    counts: dict[int, list[str]] = {}
    for row in doc["results"]:
        counts.setdefault(row.get("runs", doc["runs"]), []).append(row["binary"])
    common = max(counts, key=lambda k: len(counts[k]))
    print(f"Fastest of {common} runs per binary.")
    for runs, names in sorted(counts.items()):
        if runs != common:
            word = "once" if runs == 1 else f"{runs} times"
            print(f"Measured {word} rather than {common}: {', '.join(f'`{n}`' for n in names)}.")
    print()
    for name, text in doc["versions"].items():
        print(f"- `{name}`: {text}")
    for line in doc.get("not_measured", []):
        print(f"- {line}")

    print("\n### Wall time and peak memory\n")
    head = "| binary | size |" + "".join(f" {t} load | {t} analyze | {t} peak |" for t in tools)
    print(head)
    print("| --- | --- |" + " --- | --- | --- |" * len(tools))
    for row in doc["results"]:
        line = f"| `{row['binary']}` | {row['size'] // 1024}K |"
        for tool in tools:
            line += " " + cell(row, tool, "load_seconds", lambda v: f"{v:.2f}s") + " |"
            line += " " + cell(row, tool, "seconds", lambda v: f"{v:.2f}s") + " |"
            line += " " + cell(row, tool, "peak_kb", lambda v: f"{v / 1024:.0f} MB") + " |"
        print(line)

    print("\n### Function recovery alone, without the rest of a full analysis\n")
    head = "| binary | named |" + "".join(
        f" {t} time | {t} found | {t} recall | {t} not in code |" for t in tools
    )
    print(head)
    print("| --- | --- |" + " --- | --- | --- | --- |" * len(tools))
    for row in doc["results"]:
        line = f"| `{row['binary']}` | {row['oracle_functions']} |"
        for tool in tools:
            rec = (row["tools"].get(tool) or {}).get("recover") or {}
            if not rec.get("ran"):
                line += " n/a | n/a | n/a | n/a |"
                continue
            recall = "n/a" if rec["recall"] is None else f"{rec['recall'] * 100:.1f}%"
            line += (
                f" {rec['seconds']:.2f}s | {rec['counted']} | {recall} |"
                f" {rec['non_executable']} |"
            )
        print(line)

    print("\n### Functions found by the full analysis, against the symbol table\n")
    head = "| binary | oracle | named |" + "".join(
        f" {t} found | {t} recall | {t} missed | {t} unnamed | {t} not in code |"
        for t in tools
    )
    print(head)
    print("| --- | --- | --- |" + " --- | --- | --- | --- | --- |" * len(tools))
    for row in doc["results"]:
        line = f"| `{row['binary']}` | {row['oracle']} | {row['oracle_functions']} |"
        for tool in tools:
            line += " " + cell(row, tool, "counted", str) + " |"
            line += " " + cell(row, tool, "recall", lambda v: f"{v * 100:.1f}%") + " |"
            # A miss with the tool's own entry a few bytes inside the same
            # function is a boundary disagreement, not a function it never
            # found, and saying which is the difference between a fair table
            # and a flattering one.
            entry = row["tools"].get(tool) or {}
            if entry.get("ran") and entry.get("near"):
                line += f" {entry['missed']} ({entry['near']} within 16 bytes) |"
            else:
                line += " " + cell(row, tool, "missed", str) + " |"
            entry = row["tools"].get(tool) or {}
            if entry.get("ran") and entry.get("extra_inside"):
                line += f" {entry['extra']} ({entry['extra_inside']} inside a named function) |"
            else:
                line += " " + cell(row, tool, "extra", str) + " |"
            line += " " + cell(row, tool, "non_executable", str) + " |"
        print(line)
    return 0


# ---------------------------------------------------------------------- main


def build_tools(args) -> tuple[list, list[str]]:
    """The tools to measure, and a line per tool that is not measured.

    A tool left out is announced. A two-tool table where the roadmap asked for
    three reads as though the third was never wanted.
    """
    skip = {s.strip() for s in args.skip.split(",") if s.strip()}
    scripts = Path(__file__).resolve().parent / "ghidra"
    tools, absent = [], []

    if "r12e" in skip:
        absent.append("r12e: skipped by request")
    else:
        tools.append(R12e(args.r12e, args.timeout))

    if "rizin" in skip:
        absent.append("rizin: skipped by request")
    else:
        tools.append(Rizin(args.rizin, args.timeout))

    if "ghidra" in skip:
        absent.append(
            "Ghidra: not measured in this run. Set GHIDRA_INSTALL_DIR and drop it "
            "from SKIP to include it; scripts/compare-ghidra.sh compares function "
            "recovery on its own."
        )
    elif not args.ghidra:
        absent.append(
            "Ghidra: not measured, no GHIDRA_INSTALL_DIR. Its headless analyzer "
            "works on this architecture; its decompiler ships x86-64 only, so a "
            "decompiler comparison is not available on an aarch64 host either way."
        )
    else:
        tools.append(Ghidra(args.ghidra, args.ghidra_timeout, scripts))
    return tools, absent


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("binaries", nargs="*", type=Path)
    ap.add_argument("--r12e", default=os.environ.get("R12E", "target/release/r12e"))
    ap.add_argument(
        "--r12e-name",
        default="",
        help="where the r12e binary came from, when --r12e is a snapshot of it",
    )
    ap.add_argument("--rizin", default=os.environ.get("RIZIN", "rizin"))
    ap.add_argument("--ghidra", default=os.environ.get("GHIDRA_INSTALL_DIR", ""))
    ap.add_argument("--runs", type=int, default=3)
    ap.add_argument("--slow-runs", type=int, default=2, help="runs for Ghidra, which is slow")
    ap.add_argument("--ghidra-timeout", type=int, default=1800)
    ap.add_argument(
        "--timeout",
        type=int,
        default=DEFAULT_TIMEOUT,
        help="seconds before one invocation is called a timeout rather than a number",
    )
    ap.add_argument("--skip", default="", help="comma-separated tool names to leave out")
    ap.add_argument("--json", type=Path, help="write the measurements here")
    ap.add_argument(
        "--append",
        action="store_true",
        help="merge into an existing --json file instead of replacing it, so a "
        "long corpus can be measured in parts with different run counts",
    )
    ap.add_argument(
        "--explain",
        type=Path,
        help="read back a results file and print what each tool found alone",
    )
    ap.add_argument("--examples", type=int, default=8, help="addresses to show per tool")
    ap.add_argument(
        "--markdown", type=Path, help="read back a results file and emit the doc tables"
    )
    ap.add_argument(
        "--rescore",
        type=Path,
        help="recompute the scoring of a results file from the addresses it stored",
    )
    args = ap.parse_args()

    if args.explain:
        return explain_run(args.explain, args.examples)
    if args.markdown:
        return markdown_run(args.markdown)
    if args.rescore:
        return rescore_run(args.rescore)

    tools, absent = build_tools(args)
    for line in absent:
        print(f"not measured -- {line}")
    versions = {t.name: t.version() for t in tools}
    # The exact bytes measured, because this workspace gets rebuilt while a run
    # is in progress and "r12e 0.1.0" does not distinguish two builds of it.
    for tool in tools:
        if isinstance(tool, R12e):
            versions["r12e"] += (
                f" ({args.r12e_name or args.r12e}, sha256 {sha256(Path(tool.exe))[:16]})"
            )
    for name, text in versions.items():
        print(f"{name:<8} {text}")
    print()

    header = (
        f"{'binary':<28} {'size':>7}  {'tool':<7} {'load':>7} {'recover':>8} "
        f"{'analyze':>9} {'peak':>8} {'funcs':>7} {'recall':>7} {'extra':>6}"
    )
    print(header)
    print("-" * len(header))

    results = []
    for binary in args.binaries:
        if not binary.exists():
            print(f"{binary}: missing, skipped", file=sys.stderr)
            continue
        lay = layout(binary)
        oracle, extents, source = oracle_for(binary)
        size = binary.stat().st_size
        row = {
            "binary": binary.name,
            "path": str(binary),
            "size": size,
            # The input's identity, because this workspace rebuilds its
            # fixtures and a row has to say which bytes it describes.
            "sha256": sha256(binary)[:16],
            "oracle": source,
            "oracle_functions": len(oracle),
            "tools": {},
        }
        with tempfile.TemporaryDirectory(prefix="r12e-bench-") as tmp:
            work = Path(tmp)
            for tool in tools:
                runs = args.slow_runs if isinstance(tool, Ghidra) else args.runs
                lsecs, lrss, lok = best_of(runs, lambda: tool.load(binary, work))
                lok = lok is True
                rsecs, rrss, rfound = best_of(runs, lambda: tool.recover(binary, work))
                asecs, arss, found = best_of(runs, lambda: tool.analyze(binary, work))
                entry = score(found, oracle, extents, lay)
                entry["recover"] = score(rfound, oracle, extents, lay)
                entry["recover"]["seconds"] = round(rsecs, 3) if rsecs == rsecs else None
                entry["recover"]["peak_kb"] = rrss
                entry["load_seconds"] = round(lsecs, 3) if lok else None
                entry["load_peak_kb"] = lrss if lok else None
                entry["seconds"] = round(asecs, 3) if asecs == asecs else None
                entry["peak_kb"] = arss
                entry["addresses"] = sorted(found) if found else []
                entry["recover"]["addresses"] = sorted(rfound) if isinstance(rfound, set) else []
                row["tools"][tool.name] = entry
                if not entry["ran"]:
                    why = entry.get("why", "failed")
                    print(f"{binary.name:<28} {size // 1024:>6}K  {tool.name:<7} {why:>7}")
                    continue
                rec = "-" if entry["recall"] is None else f"{entry['recall'] * 100:.1f}%"
                load = f"{lsecs:.2f}s" if lok else "-"
                recover = f"{rsecs:.2f}s" if entry["recover"]["ran"] else "n/a"
                print(
                    f"{binary.name:<28} {size // 1024:>6}K  {tool.name:<7} {load:>7} "
                    f"{recover:>8} {asecs:>8.2f}s {arss / 1024:>7.1f}M "
                    f"{entry['counted']:>7} {rec:>7} {entry['extra']:>6}"
                )
        results.append(row)

    if args.json:
        # Merging by binary name, so a second pass over the slow inputs at a
        # lower run count lands beside the first pass rather than discarding
        # it. The run count that produced each row is recorded on the row.
        previous = []
        if args.append and args.json.exists():
            old = json.loads(args.json.read_text())
            fresh = {row["binary"] for row in results}
            previous = [row for row in old["results"] if row["binary"] not in fresh]
        for row in results:
            row["runs"] = args.runs
        doc = {
            "schema": "r12e-bench/1",
            "when": time.strftime("%Y-%m-%dT%H:%M:%S"),
            "loadavg": os.getloadavg(),
            # The cost half of any budget derived from this run belongs to this
            # machine and nowhere else, so the machine is written down with it.
            "machine": {
                "uname": " ".join(platform.uname()[:1] + platform.uname()[2:5]),
                "cpus": os.cpu_count(),
            },
            "runs": args.runs,
            "slow_runs": args.slow_runs,
            "versions": versions,
            "not_measured": absent,
            "results": previous + results,
        }
        args.json.write_text(json.dumps(doc, indent=2) + "\n")
        print(f"\nwrote {args.json}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
