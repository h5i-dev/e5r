#!/usr/bin/env python
"""Drive DecBench over already-compiled binaries with r12e as one column.

DecBench's own `scripts/run_benchmark.py` is the resilient full-corpus driver.
It is not usable here: it decompiles through its own `decompile_one.py`
subprocess, which imports only the in-tree backends, so an out-of-tree column
is invisible to it unless the DecBench checkout is edited, and it drives the
whole corpus rather than one project.
This driver is the same pipeline at one project's scale -- strip, decompile the
stripped copy by DWARF address, relabel to DWARF names, evaluate, aggregate --
using DecBench's own library calls at every step, so the numbers come from its
code and not from a reimplementation of its metrics.

Usage:
    decbench_run.py <results-tree> <project> <opt[,opt...]> [decompiler,...]
    decbench_run.py --compile <results-tree> <project> <opt[,opt...]>

Env:
    DECBENCH_REPO   the DecBench checkout (required)
    R12E            the r12e executable (default: target/release/r12e)
    DECBENCH_MAXBINS / DECBENCH_MAXFUNCS  cap the work for a smoke run
    DECBENCH_TIMEOUT  seconds per (binary, decompiler), default 1800
    DECBENCH_REDO     decompilers to rerun rather than reuse from the tree
"""

from __future__ import annotations

import json
import multiprocessing
import os
import pickle
import re
import shutil
import subprocess
import sys
import tempfile
import time
from pathlib import Path

if multiprocessing.get_start_method(allow_none=True) != "spawn":
    multiprocessing.set_start_method("spawn", force=True)

_REPO = Path(__file__).resolve().parent.parent
_DECBENCH = Path(os.environ.get("DECBENCH_REPO", "")).expanduser()
if not (_DECBENCH / "decbench").is_dir():
    raise SystemExit("set DECBENCH_REPO to the DecBench checkout")
sys.path.insert(0, str(_DECBENCH))
sys.path.insert(0, str(_REPO / "scripts"))

import decbench.decompilers  # noqa: E402,F401  (registers the in-tree backends)
import decbench_r12e  # noqa: E402,F401  (registers ours)
from decbench.models.decompilation import DecompilationResult  # noqa: E402
from decbench.models.project import OptimizationLevel, Project  # noqa: E402
from decbench.pipeline.evaluate import evaluate_project  # noqa: E402
from decbench.pipeline.executor import PipelineConfig, PipelineExecutor  # noqa: E402
from decbench.scoring.aggregator import aggregate_results  # noqa: E402
from decbench.scoring.scoreboard import build_scoreboard, render_scoreboard_text  # noqa: E402
from decbench.utils import binfmt  # noqa: E402
from decbench.utils.cfg import extract_cfgs_from_source  # noqa: E402

TIMEOUT = float(os.environ.get("DECBENCH_TIMEOUT", "1800"))


def stripped_copy(binary: Path, strip_dir: Path) -> Path:
    """A copy with no symbols and no DWARF: what the decompiler is allowed to see."""
    strip_dir.mkdir(parents=True, exist_ok=True)
    out = strip_dir / binary.name
    if not out.exists() or out.stat().st_mtime < binary.stat().st_mtime:
        shutil.copy2(binary, out)
        subprocess.run(["strip", "--strip-all", str(out)], capture_output=True)
    return out


def relabel_to_dwarf(result: DecompilationResult, addr2name: dict[int, str]) -> None:
    """Rename address-named functions to their DWARF names, in code and key.

    Pure bookkeeping so name-keyed evaluation lines up; the decompiler still
    only ever saw the stripped binary. Mirrors run_benchmark.py's version.
    """
    new: dict[str, object] = {}
    for fd in list(result.functions.values()):
        addr = int(fd.address)
        name = addr2name.get(addr) or addr2name.get(addr & ~1)
        if name and name != fd.name:
            fd.decompiled_code = re.sub(
                r"\b" + re.escape(fd.name) + r"\b", name, fd.decompiled_code
            )
            fd.name = name
        prev = new.get(fd.name)
        if prev is None or len(fd.decompiled_code or "") >= len(prev.decompiled_code or ""):
            new[fd.name] = fd
    result.functions = new


def decompile_worker() -> int:
    """`--decompile-one <binary> <dec> <out_dir> <pkl> <addrs.json>` in a child process.

    A separate process per (binary, decompiler) is what keeps angr's and r12e's
    memory out of the driver and lets a hung backend be killed.
    """
    binary, dec_name, out_dir, pkl, addrs_json = sys.argv[2:7]
    from decbench.decompilers.base import DecompilerConfig
    from decbench.pipeline.decompile import decompile_binary

    targets = None
    if addrs_json not in ("", "NONE"):
        targets = {int(a) for a in json.loads(Path(addrs_json).read_text())} or None
    result = decompile_binary(
        Path(binary),
        dec_name,
        Path(out_dir),
        config=DecompilerConfig(binary_timeout_seconds=TIMEOUT),
        function_names=targets,
        progress_path=Path(pkl),
    )
    Path(pkl).write_bytes(pickle.dumps(result))
    return 0


def run_decompile(binary: Path, dec: str, out_dir: Path, addrs_json: str) -> DecompilationResult | None:
    out_dir.mkdir(parents=True, exist_ok=True)
    pkl = out_dir / f"{dec.replace('@', '_')}_{binary.stem}.pkl"
    # Reuse an earlier pass so adding a second decompiler to a tree does not
    # redo the first one. DECBENCH_REDO names the decompilers to rerun anyway.
    redo = {d for d in (os.environ.get("DECBENCH_REDO") or "").split(",") if d}
    if dec not in redo and pkl.exists() and pkl.stat().st_mtime >= binary.stat().st_mtime:
        try:
            return pickle.loads(pkl.read_bytes())
        except Exception:  # noqa: BLE001
            pass
    cmd = [
        sys.executable,
        str(Path(__file__).resolve()),
        "--decompile-one",
        str(binary),
        dec,
        str(out_dir),
        str(pkl),
        addrs_json,
    ]
    try:
        subprocess.run(cmd, timeout=TIMEOUT + 60, check=False)
    except subprocess.TimeoutExpired:
        print(f"    [{dec}] TIMEOUT after {TIMEOUT}s")
    if pkl.exists():
        try:
            return pickle.loads(pkl.read_bytes())
        except Exception as e:  # noqa: BLE001
            print(f"    [{dec}] unreadable result: {e}")
    return None


def project_toml(name: str) -> Path:
    toml = _DECBENCH / "projects" / "sailr" / f"{name}.toml"
    if toml.is_file():
        return toml
    matches = list((_DECBENCH / "projects").glob(f"*/{name}.toml"))
    if not matches:
        raise SystemExit(f"no project TOML for {name}")
    return matches[0]


def compile_mode() -> int:
    """`--compile <tree> <project> <opts>`: build the corpus project from source.

    DecBench's own compile driver runs every project in the corpus; this is the
    same `compile_project` call for one of them, so the tree it writes is the
    one the decompile pass expects. It needs the network: the project TOMLs
    name upstream tarballs and git remotes.
    """
    from decbench.pipeline.compile import compile_project

    tree = Path(sys.argv[2]).resolve()
    project = Project.from_toml(project_toml(sys.argv[3]))
    for opt in sys.argv[4].split(","):
        results = compile_project(project, tree, OptimizationLevel(opt))
        ok = sum(1 for r in results if r.success)
        print(f"[{opt}] {ok}/{len(results)} build steps succeeded")
    return 0


def main() -> int:
    tree = Path(sys.argv[1]).resolve()
    # Joern plants its CPG store in a `workspace/` directory under the current
    # one, so run from the results tree rather than from wherever we were
    # invoked, which is usually the repository.
    tree.mkdir(parents=True, exist_ok=True)
    os.chdir(tree)
    project_name = sys.argv[2]
    opts = [OptimizationLevel(o) for o in sys.argv[3].split(",")]
    decs = (sys.argv[4] if len(sys.argv) > 4 else "r12e").split(",")
    max_bins = int(os.environ.get("DECBENCH_MAXBINS", "0"))
    max_funcs = int(os.environ.get("DECBENCH_MAXFUNCS", "0"))

    project = Project.from_toml(project_toml(project_name))

    executor = PipelineExecutor(PipelineConfig(output_dir=tree, optimization_levels=opts))
    executor._discover_existing_binaries([project], tree)

    evaluation: dict = {project_name: {}}
    decompiled: dict = {project_name: {}}

    for opt in opts:
        binaries = list(project.compiled_binaries.get(opt, []))
        if not binaries:
            print(f"[skip] {opt.value}: nothing compiled under {tree}")
            continue
        source_stems = set(project.preprocessed_sources.get(opt, {}).keys())

        # The DWARF filter: only functions this project's own sources define,
        # keyed by low_pc because the decompiler works on the stripped copy.
        keep, fn_names, fn_owners, needed_stems = [], {}, {}, set()
        for binary in binaries:
            addr_stem: dict[int, str] = {}
            owners = binfmt.source_function_owners(binary, source_stems)
            names = {addr: name for addr, (name, _stem) in owners.items()}
            addr_stem.update({addr: stem for addr, (_n, stem) in owners.items()})
            if max_funcs:
                names = dict(sorted(names.items())[:max_funcs])
            if not names:
                continue
            fn_names[binary.stem] = names
            fn_owners[binary.stem] = {
                a: (n, addr_stem[a]) for a, n in names.items() if a in addr_stem
            }
            needed_stems.update(addr_stem[a] for a in names if a in addr_stem)
            keep.append(binary)
        if max_bins:
            keep = keep[:max_bins]
        if not keep:
            print(f"[skip] {opt.value}: no binary has a usable DWARF source filter")
            continue
        project.compiled_binaries[opt] = keep

        print(
            f"[{opt.value}] {len(keep)} binaries, "
            f"{sum(len(fn_names[b.stem]) for b in keep)} source functions; "
            "extracting source CFGs...",
            flush=True,
        )
        t0 = time.time()
        src_cfgs = {}
        for stem, ipath in project.preprocessed_sources.get(opt, {}).items():
            if stem not in needed_stems:
                continue
            try:
                src_cfgs[stem] = extract_cfgs_from_source(ipath) or {}
            except Exception as e:  # noqa: BLE001
                print(f"    [warn] source CFGs failed for {stem}: {e}")
                src_cfgs[stem] = {}
        print(f"[{opt.value}] source CFGs in {time.time() - t0:.0f}s", flush=True)

        strip_dir = tree / opt.value / project_name / "stripped"
        dec_out = tree / opt.value / project_name / "decompiled"
        addr_dir = Path(tempfile.mkdtemp(prefix="decaddrs_"))
        results: dict[str, dict[str, DecompilationResult]] = {}
        try:
            for binary in keep:
                stripped = stripped_copy(binary, strip_dir)
                addrs = addr_dir / f"{binary.stem}.json"
                addrs.write_text(json.dumps(sorted(fn_names[binary.stem])))
                results[binary.stem] = {}
                for dec in decs:
                    t1 = time.time()
                    res = run_decompile(stripped, dec, dec_out, str(addrs))
                    if res is None:
                        print(f"    [{dec}] {binary.stem}: no result")
                        continue
                    relabel_to_dwarf(res, fn_names[binary.stem])
                    res.binary_path = binary
                    results[binary.stem][res.decompiler.decompiler_name] = res
                    print(
                        f"    [{res.decompiler.decompiler_name}] {binary.stem}: "
                        f"{len(res.functions)}/{len(fn_names[binary.stem])} functions "
                        f"in {time.time() - t1:.0f}s",
                        flush=True,
                    )
        finally:
            shutil.rmtree(addr_dir, ignore_errors=True)

        print(f"[{opt.value}] evaluating...", flush=True)
        t2 = time.time()
        ev = evaluate_project(
            project,
            results,
            tree,
            opt,
            None,
            parallel=False,
            precomputed_source_cfgs=src_cfgs,
            source_function_owners=fn_owners,
        )
        print(f"[{opt.value}] evaluated in {time.time() - t2:.0f}s", flush=True)
        evaluation[project_name][opt] = ev
        decompiled[project_name][opt] = results

    aggregated = aggregate_results(evaluation)
    scoreboard = build_scoreboard(
        aggregated,
        projects=[project_name],
        optimization_levels=[o.value for o in opts],
        decompilers=aggregated.decompilers,
        name=f"DecBench: {project_name}",
    )
    out = tree / f"scoreboard_{project_name}.toml"
    scoreboard.to_toml(out)
    (tree / f"aggregated_{project_name}.pkl").write_bytes(pickle.dumps(aggregated))
    print("\n" + render_scoreboard_text(scoreboard))
    print(f"\nscoreboard: {out}")
    return 0


if __name__ == "__main__":
    if len(sys.argv) > 1 and sys.argv[1] == "--decompile-one":
        raise SystemExit(decompile_worker())
    if len(sys.argv) > 1 and sys.argv[1] == "--compile":
        raise SystemExit(compile_mode())
    raise SystemExit(main())
