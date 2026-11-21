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


def analyze(rel, b, g):
    """Sizes, levels and the gold patch's changes for one subject (base ELF b, gold ELF g)."""
    fb, db = funcs.canonical(b)
    fg, dg = funcs.canonical(g)
    mod, add, rem = funcs.changed(fb, fg)
    dmod, dadd, drem = funcs.changed(db, dg)
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
        "scratch": {"removes": [fb[k].name for k in mod],
                    "instructions": sum(fb[k].insns for k in mod),
                    "gold_instructions": sum(fg[k].insns for k in mod) + sum(fg[k].insns for k in add),
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
            if side == "gold":
                recipe.reset_generated(wt, log)
                apply_patch(wt, log, task["patch"], "gold", "gold-patch")
            t = time.time()
            recipe.build(wt, log)
            elfs = []
            recipe.unit_tests = set()
            for rel in recipe.subjects:
                dst = os.path.join(art, f"{side}.{os.path.basename(rel)}.debug.elf")
                shutil.copy(os.path.join(wt, rel), dst)
                stripped = dst.replace(".debug.elf", ".elf")
                log.run(f"llvm-objcopy --strip-debug {dst} {stripped}", wt, "strip")
                elfs.append(stripped)
            build_s = round(time.time() - t, 1)
            apply_patch(wt, log, task["test_patch"], "test", "test-patch")
            t = time.time()
            res = run_side(recipe, wt, log, task, elfs, side)
            sides[side] = {"elfs": elfs, "results": res, "build_s": build_s,
                           "test_s": round(time.time() - t, 1)}
            log.run(f"git apply -R --whitespace=nowarn {os.path.join(work, 'test.patch')}", wt, "test-unpatch")
        rows, excluded, why = judge(task, recipe, sides["base"]["results"], sides["gold"]["results"])
        rec["tests"] = rows
        rec["excluded_tests"] = excluded
        rec["timing_s"] = {s: {"build": v["build_s"], "test": v["test_s"]} for s, v in sides.items()}
        rec["binaries"] = [analyze(rel, sides["base"]["elfs"][i], sides["gold"]["elfs"][i])
                           for i, rel in enumerate(recipe.subjects)]
        if not any(any(b["gold_changes"][k] for k in b["gold_changes"]) for b in rec["binaries"]):
            why.append("the gold patch changes neither code nor data of a subject")
        if why:
            rec["drop_reason"] = why
        else:
            rec["status"] = "kept"
    except Failed as e:
        rec["drop_reason"] = [f"{e.stage} failed"]
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
    a = ap.parse_args()
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
