"""The environment's test harness: run a task's tests against given ELFs.

  harness.py run TASK_ID ELF... [--which all|p2p]

ELF i stands for the task's subject i (tasks/<id>.json, "subjects"). The tests run in the
task's converted checkout ($SWB/work/<id>/src), reset to the base commit with the test patch
applied, as in the conversion. Prints one JSON object: {"results": {test: PASSED|FAILED|...},
"f2p_passed": n, "p2p_passed": n, "f2p": N, "p2p": N}, over the tests the task keeps (the
excluded ones are left out). `--which p2p` runs the same command and reports PASS_TO_PASS only:
what an agent may see in patch mode, where FAIL_TO_PASS tests are hidden as in SWE-bench.

One run per task at a time (a lock file): the checkout is shared by every episode of the task.
This is the environment's own code, run by the server; no agent tool reaches it except through
run_tests and submit.
"""

from __future__ import annotations

import argparse
import fcntl
import json
import os
import re
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import funcs  # noqa: E402
from recipes import RECIPES, SWB, Failed, Log, wrapper  # noqa: E402

HERE = os.path.dirname(os.path.abspath(__file__))
TASKS = os.path.join(os.path.dirname(HERE), "tasks")
DATASET = os.environ.get("SWB_DATASET", os.path.join(SWB, "dl", "cr.jsonl"))


def dataset_row(iid):
    with open(DATASET) as fh:
        for line in fh:
            r = json.loads(line)
            if r["instance_id"] == iid:
                return r
    raise SystemExit(f"{iid}: not in {DATASET}")


def counted(task_json):
    """The tests the task keeps, by kind."""
    f2p = [t["test"] for t in task_json["tests"] if t["kind"] == "FAIL_TO_PASS"]
    p2p = [t["test"] for t in task_json["tests"] if t["kind"] == "PASS_TO_PASS"]
    return f2p, p2p


V0_CRATE = re.compile(r"C(?:s[0-9A-Za-z]*?_)?(\d+)([A-Za-z_][A-Za-z0-9_]*)")


def rust_path(sym: str):
    """(crate, path segments) of a Rust symbol (v0 `_R...` or legacy `_ZN...E`), or None."""
    if sym.startswith("_R"):
        m = V0_CRATE.search(sym)
        if not m:
            return None
        crate = m.group(2)[: int(m.group(1))]
        rest, segs, i = sym[m.start(2) + int(m.group(1)):], [], 0
        while i < len(rest):  # <len><ident>, length first: the identifier may end in digits
            if rest[i].isdigit():
                j = i
                while j < len(rest) and rest[j].isdigit():
                    j += 1
                n = int(rest[i:j])
                if j < len(rest) and rest[j] == "_":  # an identifier that starts with a digit
                    j += 1
                segs.append(rest[j : j + n])
                i = j + n
            else:
                i += 1
        return crate, segs
    if sym.startswith("_ZN"):
        segs, i = [], 3
        while i < len(sym) and sym[i].isdigit():
            j = i
            while sym[j].isdigit():
                j += 1
            n = int(sym[i:j])
            segs.append(sym[j : j + n])
            i = j + n
        return (segs[0], segs[1:]) if segs else None
    return None


def integrity(tj, elfs):
    """Class B: the functions a submission may change are those of the crates under test, and
    not test code. The violations (key: reason), against the base build."""
    allowed = set(tj.get("editable_crates", []))
    bad = {}
    for b, elf in zip(tj["binaries"], elfs):
        base, _ = funcs.canonical(os.path.join(SWB, b["base"]["path"]))
        sub, _ = funcs.canonical(elf)
        for k, f in base.items():
            g = sub.get(k)
            if g is not None and g.sha256 == f.sha256:
                continue
            p = rust_path(f.name)
            if p is None:
                bad[f.name] = "not Rust code of the crates under test (std, libc, compiler builtins)"
            elif p[0] not in allowed:
                bad[f.name] = f"crate {p[0]} is not under test"
            elif "tests" in p[1] or "test" in p[1]:
                bad[f.name] = "test code"
    return bad


def run(iid, elfs, which="all"):
    with open(os.path.join(TASKS, f"{iid}.json")) as fh:
        tj = json.load(fh)
    if tj.get("deviation"):
        bad = integrity(tj, elfs)
        if bad:
            f2p, p2p = counted(tj)
            some = dict(list(sorted(bad.items()))[:20])
            return {"error": f"{len(bad)} functions outside the crates under test differ from base", "violations": some,
                    "results": {}, "f2p_passed": 0, "p2p_passed": 0, "f2p": len(f2p), "p2p": len(p2p)}
    row = dataset_row(iid)
    recipe = RECIPES[row["repo"]]
    recipe.subjects = list(tj["subjects"])  # class B recipes find theirs at build time
    if len(elfs) != len(recipe.subjects):
        raise SystemExit(f"{iid}: {len(recipe.subjects)} subjects ({', '.join(recipe.subjects)}), {len(elfs)} ELFs given")
    work = os.path.join(SWB, "work", iid)
    wt = os.path.join(work, "src")
    log = Log(os.path.join(work, "harness.log"))
    with open(os.path.join(work, "harness.lock"), "w") as lock:
        fcntl.flock(lock, fcntl.LOCK_EX)
        # the checkout as the base commit's tests see it: base sources plus the test patch
        tp = os.path.join(work, "harness-test.patch")
        with open(tp, "w") as fh:
            fh.write(row["test_patch"])
        log.run(f"git checkout -q {row['base_commit']} -- . && git apply --whitespace=nowarn {tp}", wt, "harness-prepare")
        try:
            recipe.refresh(wt, log)
            recipe.unit_tests = set()
            recipe.current = dict(zip(recipe.subjects, [os.path.abspath(e) for e in elfs]))
            for rel, elf in recipe.current.items():
                wrapper(os.path.join(wt, rel), elf)
            out = recipe.run_tests(wt, row, log)
            res = recipe.parse(out)
        finally:
            log.run(f"git apply -R --whitespace=nowarn {tp}", wt, "harness-unpatch", check=False)
    f2p, p2p = counted(tj)
    show = (f2p if which == "all" else []) + p2p
    results = {t: res.get(t, "MISSING") for t in show}
    rep = {"results": results, "p2p_passed": sum(res.get(t) == "PASSED" for t in p2p), "p2p": len(p2p)}
    if which == "all":
        rep.update(f2p_passed=sum(res.get(t) == "PASSED" for t in f2p), f2p=len(f2p))
    return rep


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("cmd", choices=["run"])
    ap.add_argument("task")
    ap.add_argument("elfs", nargs="+")
    ap.add_argument("--which", choices=["all", "p2p"], default="all")
    a = ap.parse_args()
    try:
        print(json.dumps(run(a.task, a.elfs, a.which)))
    except Failed as e:
        print(json.dumps({"error": f"{e.stage}: {e.detail[-500:]}"}))
        sys.exit(1)


if __name__ == "__main__":
    main()
