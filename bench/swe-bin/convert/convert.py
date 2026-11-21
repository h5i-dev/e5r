"""Convert SWE-bench Multilingual C/Rust tasks into swe-bin tasks (stage 1).

For each task:
  1. check out the base commit; build the subject (static riscv64 ELF) with the repo's recipe;
  2. apply the test patch, point the subject at the base ELF (qemu wrapper), run the tests;
  3. reset, apply the GOLD patch, build again (the environment's oracle, never an agent tool);
  4. apply the test patch, point the subject at the gold ELF, run the tests;
  5. keep the task iff every FAIL_TO_PASS test fails (or is missing) at base and passes at gold,
     and every PASS_TO_PASS test passes at both. Tests that do not run a subject are excluded,
     each with its reason;
  6. record the sizes, the instruction counts, `nocompiler check` levels, and the functions the
     gold patch changes (funcs.py), and the removals for scratch mode.

Usage: convert.py DATASET.jsonl [--only ID ...] [--repo owner/name]
Output: tasks/<id>.json (in this directory's parent), artifacts under $SWB/artifacts/<id>/.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import shutil
import subprocess
import sys
import time

sys.path.insert(0, os.path.dirname(__file__))
import funcs  # noqa: E402
from recipes import RECIPES, SWB, Failed, Log, wrapper  # noqa: E402

HERE = os.path.dirname(os.path.abspath(__file__))
TASKS = os.path.join(os.path.dirname(HERE), "tasks")
NC = os.environ.get("NOCOMPILER", "/mnt/scratch/ec2-user/target-nc-d/release/nocompiler")


def sha256(path):
    h = hashlib.sha256()
    with open(path, "rb") as fh:
        for b in iter(lambda: fh.read(1 << 20), b""):
            h.update(b)
    return h.hexdigest()


def test_cmd(task):
    es = task["eval_script"]
    return es.split(": '>>>>> Start Test Output'")[1].split(": '>>>>> End Test Output'")[0].strip()


def levels(elf):
    p = subprocess.run([NC, "check", "--json", elf], stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    try:
        j = json.loads(p.stdout)
    except json.JSONDecodeError:
        return {"error": p.stderr.decode()[-300:]}, {}
    count = {}
    by_name = {}
    for f in j["functions"]:
        lv = f.get("level") or "below L0"
        count[lv] = count.get(lv, 0) + 1
        by_name[f["name"]] = lv
    return count, by_name


def analyze(rel, b, g, patch=""):
    """Sizes, levels and the gold patch's changes for one subject (base ELF b, gold ELF g).

    Two views of the change. `gold_changes` is byte level: functions and data whose
    relocation-masked form differs. That also catches code the patch did not touch but whose
    bytes moved, e.g. every assert after an inserted line carries a new __LINE__. `source_changes`
    is the functions whose code comes from lines the patch touches, by the DWARF line tables of
    the -g builds (inlined copies included). Scratch mode removes the source-level set."""
    fb, db = funcs.canonical(b)
    fg, dg = funcs.canonical(g)
    mod, add, rem = funcs.changed(fb, fg)
    dmod, dadd, drem = funcs.changed(db, dg)
    anon = [k for k in dmod + dadd + drem if funcs.ANON.match(k.split("::")[-1])]
    dmod = [k for k in dmod if k not in anon]
    dadd = [k for k in dadd if k not in anon]
    drem = [k for k in drem if k not in anon]
    pl = funcs.patch_lines(patch)
    bd, gd = b.replace(".elf", ".debug.elf"), g.replace(".elf", ".debug.elf")
    src_b = funcs.functions_at_lines(bd, {p: o for p, (o, _) in pl.items()}) if os.path.exists(bd) else []
    src_g = funcs.functions_at_lines(gd, {p: n for p, (_, n) in pl.items()}) if os.path.exists(gd) else []
    by_name_b = {f.name: f for f in fb.values()}
    by_name_g = {f.name: f for f in fg.values()}
    removes = sorted(set(src_b) | {n for n in src_g if n in by_name_b})
    basis = "source lines (DWARF)"
    if not removes:  # no line tables: the byte-level set
        removes, basis = sorted({fb[k].name for k in mod}), "bytes (no line tables)"
    sigs = funcs.signatures(bd, removes) if os.path.exists(bd) else {}
    calls = funcs.callers(b, removes)
    cb, lb = levels(b)
    _, lg = levels(g)
    return {
        "subject": rel,
        "base": {"path": os.path.relpath(b, SWB), "sha256": sha256(b), "bytes": os.path.getsize(b),
                 "functions": len(fb), "instructions": sum(f.insns for f in fb.values()),
                 "levels": cb},
        "gold": {"path": os.path.relpath(g, SWB), "sha256": sha256(g), "bytes": os.path.getsize(g),
                 "functions": len(fg), "instructions": sum(f.insns for f in fg.values())},
        "gold_changes": {
            "modified": [{"key": k, "name": fb[k].name, "base_insns": fb[k].insns,
                          "gold_insns": fg[k].insns, "base_level": lb.get(fb[k].name),
                          "gold_level": lg.get(fg[k].name)} for k in mod],
            "added": [{"key": k, "name": fg[k].name, "gold_insns": fg[k].insns,
                       "gold_level": lg.get(fg[k].name)} for k in add],
            "removed": [{"key": k, "name": fb[k].name, "base_insns": fb[k].insns} for k in rem],
            "data_modified": [{"key": k, "name": db[k].name, "base_bytes": db[k].size,
                               "gold_bytes": dg[k].size} for k in dmod],
            "data_added": [{"key": k, "name": dg[k].name, "gold_bytes": dg[k].size} for k in dadd],
            "data_removed": [{"key": k, "name": db[k].name, "base_bytes": db[k].size} for k in drem],
        },
        # scratch mode (SWE-bench-derived, function-level from-scratch): every base function the
        # gold patch modifies is replaced by a stub, and the agent writes it. Data the gold patch
        # changes is listed: the agent has to write that too.
        "anonymous_literals_changed": len(anon),
        "source_changes": {"base": src_b, "gold": src_g,
                           "debug_info": os.path.exists(bd) and bool(src_b or src_g)},
        "scratch": {"removes": removes,
                    "basis": basis,
                    "functions": [{"name": n, "instructions": by_name_b[n].insns if n in by_name_b else None,
                                   "signature": sigs.get(n), "callers": calls.get(n, [])} for n in removes],
                    "instructions": sum(by_name_b[n].insns for n in removes),
                    "gold_instructions": sum(by_name_g[n].insns for n in set(removes) | set(src_g) if n in by_name_g),
                    "new_functions": [n for n in src_g if n not in by_name_b],
                    "data_to_write": [dg[k].name for k in dmod + dadd]},
    }


def git(wt, log, args, stage):
    return log.run("git " + args, wt, stage)


def apply_patch(wt, log, text, name, stage):
    p = os.path.join(wt, "..", f"{name}.patch")
    with open(p, "w") as fh:
        fh.write(text)
    log.run(f"git apply --whitespace=nowarn {os.path.abspath(p)}", wt, stage)


def run_side(recipe, wt, log, task, elfs, side):
    recipe.current = dict(zip(recipe.subjects, elfs))
    for rel, elf in zip(recipe.subjects, elfs):
        wrapper(os.path.join(wt, rel), elf)
    out = recipe.run_tests(wt, task, log)
    with open(os.path.join(wt, "..", f"tests-{side}.log"), "w") as fh:
        fh.write(out)
    return recipe.parse(out)


def judge(task, recipe, base, gold):
    """Per-test outcome, the excluded tests, and the reason a task is dropped (or None)."""
    rows, excluded, why = [], {}, []
    for kind in ("FAIL_TO_PASS", "PASS_TO_PASS"):
        for t in task[kind]:
            ex = recipe.excluded(t)
            if ex:
                excluded[t] = ex
                continue
            b, g = base.get(t, "MISSING"), gold.get(t, "MISSING")
            if kind == "PASS_TO_PASS" and b == g == "SKIPPED":
                # the suite itself skips it here (micropython's native emitter tests: there is
                # no riscv64 emitter in these versions); it cannot pass or fail on this platform
                excluded[t] = "skipped by the test suite on riscv64 under qemu, at base and at gold"
                continue
            rows.append({"test": t, "kind": kind, "base": b, "gold": g})
            if g != "PASSED":
                why.append(f"{kind} {t}: gold {g}")
            if kind == "FAIL_TO_PASS" and b == "PASSED":
                why.append(f"FAIL_TO_PASS {t}: passes at base")
            if kind == "PASS_TO_PASS" and b != "PASSED":
                why.append(f"PASS_TO_PASS {t}: base {b}")
    if not any(r["kind"] == "FAIL_TO_PASS" for r in rows):
        why.append("no FAIL_TO_PASS test runs a subject")
    return rows, excluded, why


def convert(task, keep_work=False):
    iid = task["instance_id"]
    recipe = RECIPES[task["repo"]]
    recipe.task = task
    work = os.path.join(SWB, "work", iid)
    art = os.path.join(SWB, "artifacts", iid)
    shutil.rmtree(work, ignore_errors=True)
    os.makedirs(work)
    os.makedirs(art, exist_ok=True)
    wt = os.path.join(work, "src")
    log = Log(os.path.join(work, "convert.log"))
    rec = {"instance_id": iid, "repo": task["repo"], "base_commit": task["base_commit"],
           "language": recipe.language, "recipe": recipe.name, "subjects": recipe.subjects,
           "test_command": test_cmd(task), "FAIL_TO_PASS": list(task["FAIL_TO_PASS"]),
           "PASS_TO_PASS": list(task["PASS_TO_PASS"]), "status": "dropped"}
    t0 = time.time()
    try:
        bare = os.path.join(SWB, "repos", task["repo"].split("/")[1] + ".git")
        log.run(f"git clone -q {bare} {wt}", work, "checkout")
        git(wt, log, f"checkout -q {task['base_commit']}", "checkout")
        recipe.prepare(wt, log)
        sides = {}
        for side in ("base", "gold"):
            rec["failed_side"] = side
            if side == "gold":
                recipe.reset_generated(wt, log)
                apply_patch(wt, log, task["patch"], "gold", "gold-patch")
            early = getattr(recipe, "build_with_test_patch", False)
            if early:  # the tests are compiled into the subject: build with the test patch
                apply_patch(wt, log, task["test_patch"], "test", "test-patch")
            t = time.time()
            recipe.build(wt, log)
            elfs = []
            recipe.unit_tests = set()
            for rel in recipe.subjects:
                dst = os.path.join(art, f"{side}.{os.path.basename(rel)}.debug.elf")
                shutil.copy(os.path.join(wt, rel), dst)
                stripped = dst.replace(".debug.elf", ".elf")
                # .debug_gdb_scripts stays: rustc references it from .text (an --emit-relocs relocation)
                log.run(f"llvm-objcopy --strip-debug --keep-section=.debug_gdb_scripts {dst} {stripped}", wt, "strip")
                elfs.append(stripped)
            build_s = round(time.time() - t, 1)
            if not early:
                apply_patch(wt, log, task["test_patch"], "test", "test-patch")
            t = time.time()
            res = run_side(recipe, wt, log, task, elfs, side)
            sides[side] = {"elfs": elfs, "results": res, "build_s": build_s,
                           "test_s": round(time.time() - t, 1)}
            log.run(f"git apply -R --whitespace=nowarn {os.path.join(work, 'test.patch')}", wt, "test-unpatch")
        rec.pop("failed_side", None)
        rec["subjects"] = list(recipe.subjects)
        if getattr(recipe, "deviation", None):
            rec["deviation"] = recipe.deviation
            rec["editable_crates"] = getattr(recipe, "editable", [])
        rows, excluded, why = judge(task, recipe, sides["base"]["results"], sides["gold"]["results"])
        rec["tests"] = rows
        rec["excluded_tests"] = excluded
        rec["timing_s"] = {s: {"build": v["build_s"], "test": v["test_s"]} for s, v in sides.items()}
        rec["binaries"] = [analyze(rel, sides["base"]["elfs"][i], sides["gold"]["elfs"][i], task["patch"])
                           for i, rel in enumerate(recipe.subjects)]
        if not any(any(b["gold_changes"][k] for k in b["gold_changes"]) for b in rec["binaries"]):
            why.append("the gold patch changes neither code nor data of a subject")
        if why:
            rec["drop_reason"] = why
        else:
            rec["status"] = "kept"
    except Failed as e:
        rec["drop_reason"] = [f"{e.stage} failed at {rec.get('failed_side', 'checkout')}"]
        rec["error"] = e.detail[-2000:]
    rec["commands"] = log.commands
    rec["convert_s"] = round(time.time() - t0, 1)
    os.makedirs(TASKS, exist_ok=True)
    with open(os.path.join(TASKS, f"{iid}.json"), "w") as fh:
        json.dump(rec, fh, indent=1, sort_keys=False)
        fh.write("\n")
    if not keep_work and rec["status"] == "kept":
        pass  # the checkout is kept for now: run_tests in stage 3 reuses the build tree
    return rec


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("dataset")
    ap.add_argument("--only", nargs="*")
    ap.add_argument("--repo")
    ap.add_argument("--skip-done", action="store_true")
    ap.add_argument("--reanalyze", action="store_true",
                    help="recompute the binaries' analysis of converted tasks from their artifacts, without building")
    a = ap.parse_args()
    if a.reanalyze:
        for t in [json.loads(line) for line in open(a.dataset)]:
            p = os.path.join(TASKS, t["instance_id"] + ".json")
            if not os.path.exists(p) or (a.only and t["instance_id"] not in a.only) or (a.repo and t["repo"] != a.repo):
                continue
            rec = json.load(open(p))
            if "binaries" not in rec:
                continue
            rec["binaries"] = [analyze(b["subject"], os.path.join(SWB, b["base"]["path"]),
                                       os.path.join(SWB, b["gold"]["path"]), t["patch"]) for b in rec["binaries"]]
            with open(p, "w") as fh:
                json.dump(rec, fh, indent=1)
                fh.write("\n")
            print(t["instance_id"], "reanalyzed:", [len(b["scratch"]["removes"]) for b in rec["binaries"]], flush=True)
        return
    tasks = [json.loads(line) for line in open(a.dataset)]
    for t in tasks:
        if t["repo"] not in RECIPES:
            continue
        if a.only and t["instance_id"] not in a.only:
            continue
        if a.repo and t["repo"] != a.repo:
            continue
        if a.skip_done and os.path.exists(os.path.join(TASKS, t["instance_id"] + ".json")):
            continue
        r = convert(t)
        print(t["instance_id"], r["status"], "; ".join(r.get("drop_reason", [])), f"{r['convert_s']}s", flush=True)


if __name__ == "__main__":
    main()
