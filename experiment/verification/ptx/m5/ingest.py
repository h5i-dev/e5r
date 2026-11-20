#!/usr/bin/env python3
"""Split a batch file written by the model into kernels/NAME.ptx and add its
tasks to tasks.json. A batch is a sequence of

  === name | task | arrays | output | length | scalars | element | schedule-json
  <the PTX entry, as written>

The PTX header (.version 8.0, .target sm_86, .address_size 64) is added here.
"""
import json, os, sys
here = os.path.dirname(os.path.abspath(__file__))
HEAD = ".version 8.0\n.target sm_86\n.address_size 64\n\n"
tasks = json.load(open(os.path.join(here, "tasks.json")))
names = {t["name"] for t in tasks}
for path in sys.argv[1:]:
    text = open(path).read()
    for chunk in text.split("=== ")[1:]:
        head, body = chunk.split("\n", 1)
        f = [x.strip() for x in head.split("|")]
        sched = json.loads(f[-1])
        name, task, arrays, output, length, scalars = f[:6]
        element = " | ".join(f[6:-1])
        t = {"name": name, "task": task, "arrays": arrays.split(","), "output": output,
             "length": length, "scalars": [s for s in scalars.split(",") if s], "element": element,
             "schedule": sched, "batch": os.path.basename(path)}
        if task.startswith("SEEDED: "):
            # written with a deliberate defect, or deliberately outside the
            # subset, to test detection; not a natural mistake
            t["seeded"] = task[len("SEEDED: "):].split(";")[0]
        assert name not in names, name
        names.add(name)
        tasks.append(t)
        open(os.path.join(here, "kernels", name + ".ptx"), "w").write(HEAD + body.rstrip() + "\n")
json.dump(tasks, open(os.path.join(here, "tasks.json"), "w"), indent=1)
print(len(tasks), "tasks")
