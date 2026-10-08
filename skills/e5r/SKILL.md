---
name: e5r
description: Analyze binaries with e5r's JSON CLI and coordinate reverse engineering projects, evidence, and human/agent handoffs in its shared project workspace.
---

# Driving e5r

Use `e5r COMMAND --help` before guessing flags. In this checkout the executable
is `./target/release/e5r`; build with `cargo build --release`.

```sh
e5r project new ./binary --name investigation
e5r project list --json
e5r project task investigation list --json
e5r funcs ./binary --json
e5r decompile ./binary main --json
e5r xrefs ./binary main --json
e5r ui                              # human view of all global projects
```

Projects default to `~/.local/share/e5r/projects`; `E5R_PROJECT_HOME` overrides
that root. `project import FILE --name NAME` brings in an existing manifest and
task history. `--out FILE` retains local projects.

Claim tasks through `project task NAME update ID --revision N --input task.json
--author AGENT`. The input is the complete previous `content` object with your
changes. On a conflict, read the current revision and reconcile; never overwrite
another writer blindly. Active work requires an owner; blocked work requires a
reason. Record a concrete `next` action and supporting `evidence` before handing
off. `function:0xADDRESS` links a task to the decompiler pane.

Keep proven, inferred and asserted facts distinct. Incomplete control flow and
unmodelled operations limit what pseudocode establishes. Prefer a single
function and bounded `--limit` / `--budget` requests for large binaries. Exit
codes: 0 success, 1 no match, 2 usage, 3 bad input.

For details, read [the manual](../../docs/MANUAL.md) and
[project/task formats](../../docs/dashboard.md). For repository development,
read [the roadmap](../../docs/ROADMAP.md) first.
