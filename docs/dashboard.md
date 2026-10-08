# A workspace for people and agents

Create a binary project, then serve its workspace locally:

```sh
./target/release/e5r project new ./a.out --out investigation.e5rproj
./target/release/e5r project dashboard investigation.e5rproj
```

Open the printed `http://127.0.0.1:7879` address. `--port 0` selects a free
port; `--binary PATH` opens a moved binary only if its content still matches the
project. Ctrl-C stops the workspace. Assets ship inside the Rust executable;
there is no frontend build step, CDN, font download, or Node runtime requirement.

The overview answers “what needs me?” before showing the rest of the work.
Blocked work always carries a reason, review requests carry their handoff, and
ready tasks have no unfinished prerequisites. High priority sorts first within
these groups. Counts have literal meanings; there is no inferred health score.
Search and state filters keep completed work available without crowding the
initial view. Tasks refresh every five seconds, including changes from agents.
An open editor keeps its contents while the background refreshes.

The decompiler uses a familiar three-column workspace: searchable functions on
the left, code in the center, and evidence, variables and related tasks on the
right. Use `/` to focus function search. Pseudocode, disassembly and incoming
references are tabs over the same recovered function. Click a known function
name or address to navigate; Back returns to the previous function. Toggle **Wrap** for long expressions. Copy code
or its CLI command, or use **Task here** to retain the function address as
evidence in a new task. Large function lists are loaded in display batches;
search always searches the complete list. Narrow screens collapse the context
column so code keeps space.

The library owns all analysis facts and all task readiness rules. The pane
shows boundary strength, source evidence, incomplete control flow, unmodelled
operations and signature conflicts. It does not imply that pseudocode is
verified source or fabricate a source-to-instruction mapping. Binary analysis
and annotations are a **startup snapshot**; restart the server after changing
them. Task data stays live. Signature-library references and patch-set references
remain in the project file; they are not automatically applied to the loaded
binary. Unknown analysis settings and custom readers are refused. Supported
analysis settings are `scan_gaps`, `follow_calls`, `strings`, `xrefs`, `noreturn`,
`data` (boolean) and `threads` (integer).

## The agent interface

The CLI reads and writes exactly the same task store as the browser:

```sh
e5r project task investigation.e5rproj add 'Trace input validation' \
  --owner agent-a --next 'Inspect parse_header and its callers' \
  --priority high --evidence function:0x401000 --author agent-a
e5r project task investigation.e5rproj list --json
e5r project task investigation.e5rproj update T-0001 \
  --revision 1 --input task.json --author agent-a
```

`add` and `update` return the saved task as JSON. `list --json` returns
`e5r.work.v1`, with each saved task, `ready`, `waiting_on` and `attention`.
`update` takes the last observed revision and a complete content document:

```json
{
  "title": "Trace input validation",
  "description": "Determine whether the parser validates length before copying.",
  "state": "active",
  "priority": "high",
  "owner": "agent-a",
  "next": "Inspect the copy call and its guard",
  "blocker": "",
  "evidence": ["function:0x401000", "notes/input-validation.md"],
  "depends_on": []
}
```

States: `planned`, `active`, `blocked`, `review`, `done`. Priority: `high`,
`normal`, `low`. Active work requires an owner; blocked work requires a reason.
Clear `blocker` when leaving the blocked state. Prerequisites must exist, be
unique, and not form a cycle. Active, review and done tasks require completed
prerequisites. Reopening a prerequisite is refused while a dependent is active,
in review or done. Next actions and evidence are free text; their correctness
remains the writer's responsibility. Link a task to a function with the exact
`function:0xADDRESS` evidence string shown by **Task here**.

Task content is limited to 64 KiB. Writer names contain 1–200 bytes. `--input`
can also create a task from a full content document. Content flags
apply when supplying a title and cannot be combined with `--input`, which
supplies the whole content instead.
`--author` defaults to `E5R_AUTHOR`, then the OS user. Browser writer names are
remembered locally and remain editable.

## Durability and conflicts

Coordination lives in `<project>.work/T-0001.json`, one file per task, separate
from the existing binary project and annotation log. Each task retains previous
contents, writer names and timestamps. Commit the directory with the project.
Different task files merge normally; concurrent edits to the same task, or two
branches allocating the same new id, require a git conflict review. This store
does not claim the annotation log's order-independent merge semantics.

Local writes take a directory lock, check the revision and prerequisites, write
a synced temporary file, and rename it over the task. A stale update is refused
instead of overwriting the human or agent who edited first. The browser keeps
your rejected edit visible and offers **Reload latest task**. The lock and
scratch files are ignored by git. If a process dies during a write, inspect the
PID in `<project>.work/.lock`; remove that lock only after confirming the writer
is no longer running. Corrupt JSON is an error, never an invisible missing task.

## Local HTTP surface

The workspace binds IPv4 loopback only. Host and Origin checks reject cross-site
and rebound-host requests. Writes require JSON and the custom
`X-E5R-Client: dashboard` header; there is no CORS permission. Task request bodies
are capped at 128 KiB. Binary paths and arbitrary commands cannot be supplied by
HTTP. Analysis endpoints accept only a recovered function's address.

| Route | Meaning |
| --- | --- |
| `GET /api/project` | project identity and container information |
| `GET /api/tasks` | shared task snapshot |
| `POST /api/tasks` | create `{content, author, revision: null}` |
| `POST /api/tasks/T-0001` | update `{content, author, revision}` |
| `GET /api/functions` | recovered functions, using the existing `e5r/1` JSON |
| `GET /api/decompile/0xADDRESS` | one function's pseudocode |
| `GET /api/disas/0xADDRESS` | one function's instructions |
| `GET /api/xrefs/0xADDRESS` | incoming references |

Responses are JSON; task conflicts return 409, missing routes/functions return
404, invalid content returns 400. The server handles requests serially, and
single-function decompilation can delay task requests. The existing budget is
checked between functions, so it is not a hard preemptive timeout for one very
large function. The CLI remains available independently during analysis.

## Checking changes

Run `cargo test --release --workspace` for Rust checks. For the browser workflow,
install Playwright and its Chromium browser outside the checkout, then run:

```sh
cargo build --release -p e5r-cli
E5R_PLAYWRIGHT_MODULE=/path/to/playwright/index.mjs node scripts/test-dashboard.mjs
```

The integration check compiles a small C binary with `cc`, starts an isolated
workspace on a free port, compares decompiler output with the CLI, tests browser
editing and stale revisions, checks function navigation and linked evidence,
and verifies cross-origin rejection and mobile layout. It removes its temporary
project and stops the server when finished. Screenshots are written under `/tmp`.
