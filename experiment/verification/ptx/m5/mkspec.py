#!/usr/bin/env python3
"""Write m5/specs/NAME.json from the task table in tasks.json."""
import json, os, sys
here = os.path.dirname(os.path.abspath(__file__))
tasks = json.load(open(os.path.join(here, "tasks.json")))
os.makedirs(os.path.join(here, "specs"), exist_ok=True)
for t in tasks:
    k = t["name"]
    p = lambda s: f"{k}_{s}"
    sched = t["schedule"]
    if sched["kind"] == "stride":
        sched = dict(sched)
        sched["loop"] = {"head": sched.pop("head"), "registers": sched.pop("registers")}
    spec = {"schema": "e5r.ptx.spec.v1", "kernel": k, "class": "map32",
            "arrays": [p(a) for a in t["arrays"]], "output": p(t["output"]),
            "length": p(t["length"]), "scalars": [p(s) for s in t.get("scalars", [])],
            "element": t["element"], "schedule": sched}
    with open(os.path.join(here, "specs", k + ".json"), "w") as f:
        json.dump(spec, f, indent=2)
        f.write("\n")
