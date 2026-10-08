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

## Names and investigation records

The UI is read-only. Make requested edits through the CLI, including tasks and
project registration. When a function's purpose is supported by evidence, give
it a descriptive name with `e5r annotate BINARY name ADDRESS NAME --db LOG`.
Use the project's recorded annotation log, then check `funcs` and `decompile`
with the same `--db LOG`. Record the rationale and uncertainty in a comment.
Restart the UI server to reload annotations. Do not invent meanings from a
single call site. Per-variable name annotations are not currently supported;
record proposed variable names and their storage in a note instead.

Save investigation output with `e5r project record PROJECT KIND add TITLE
--description BODY --evidence function:0xADDRESS --author AGENT`, where KIND is
`finding`, `note` or `report`. Findings describe a claim and its supporting
evidence; notes retain observations and open questions; reports explain the
investigation and conclusions. These records reuse task content, revision,
history and update semantics in separate stores per kind; record IDs are local
to each kind. Use `record PROJECT KIND list --json` and `update ID --revision N
--input FILE` to read and revise them. Put the full text in `description` (or a
complete JSON input document); evidence is one reference per array entry.
