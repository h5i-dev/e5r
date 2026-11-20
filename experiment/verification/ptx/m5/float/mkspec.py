#!/usr/bin/env python3
"""specs/NAME.json for every float task: parameter names are KERNEL_NAME."""
import json, os, re
HERE = os.path.dirname(os.path.abspath(__file__))
os.makedirs(os.path.join(HERE, "specs"), exist_ok=True)
for t in json.load(open(os.path.join(HERE, "tasks.json"))):
    k = t["name"]
    p = lambda n: f"{k}_{n}"
    el = t["element"]
    for n in sorted(t["arrays"] + t["scalars"], key=len, reverse=True):
        el = re.sub(rf"(?<![\w.]){re.escape(n)}(?![\w(])", p(n), el)
    sp = {"schema": "e5r.ptx.spec.v1", "kernel": k, "class": "map32", "element_type": "f32",
          "arrays": [p(a) for a in t["arrays"]], "output": p(t["output"]), "length": p("n"),
          "scalars": [p(s) for s in t["scalars"]], "element": el, "result": "bit_exact"}
    if t.get("stride"):
        sp["schedule"] = {"kind": "stride", "bound": "2^64", "loop": {"head": "$L_loop", "registers": {
            "%rd1": f"base {p('x')}", "%rd2": f"base {p('y')}", "%f1": f"scalar {p('a')}",
            "%rd3": "index64", "%rd5": "stride64", "%rd6": "length"}}}
    else:
        sp["schedule"] = {"kind": "guarded", "max_threads": "2^32"}
    json.dump(sp, open(os.path.join(HERE, "specs", k + ".json"), "w"), indent=1)
