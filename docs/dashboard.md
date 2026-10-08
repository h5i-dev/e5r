# A workspace for people and agents

Start the global collection from any directory:

```sh
e5r project new ./a.out --name parser
e5r ui
```

In this checkout, use `./target/release/e5r` if e5r is not installed. Open the
printed `http://127.0.0.1:7879` address. The collection shows every project's
live tasks, blockers, review requests and binary availability. Select a project
to open its task dashboard and decompiler; **All projects** returns to the
collection. The UI is read-only. Ask an agent to register projects and edit tasks through
the CLI. An unavailable binary does not prevent reading that project's tasks.

Project storage follows h5i's convention, in this order:

1. `E5R_PROJECT_HOME`
2. `$XDG_DATA_HOME/e5r/projects` (absolute XDG paths only)
3. `~/.local/share/e5r/projects`

Each name owns `<root>/<name>/project.e5rproj` and
`project.e5rproj.work/`. Binaries and existing annotation logs remain at their
recorded absolute paths. Creation refuses existing names. Omitting `--name`
uses the binary filename; `--out FILE` keeps the explicit local-file workflow.
Named project commands work from any directory. A registered name takes
precedence over a same-named local file; use `./FILE` to select a local manifest:

```sh
e5r project list --json
e5r project task parser list --json
e5r project task parser add 'Trace input validation' --owner agent-a
e5r project import ./old.e5rproj --name older-investigation
e5r project relocate parser /new/path/to/a.out
e5r project dashboard parser           # optional single-project mode
```

Import copies the manifest and task history, preserving the original files.
Legacy relative references resolve against the original manifest's directory;
use `--base-dir ORIGINAL_CWD` if they were recorded relative to a different
working directory. New manifests always use absolute references. Relocate
checks content before changing a path. The collection checks existence and
size only; the content digest is verified before loading a binary.

Both UI modes support `--port 0` for a free port. Single-project mode also
accepts `--binary PATH` as a temporary path override. Ctrl-C stops the server.
Assets ship inside the Rust executable; no frontend build step, CDN, font
download, or Node runtime is required.

The overview answers “what needs me?” before showing the rest of the work.
Blocked work always carries a reason, review requests carry their handoff, and
ready tasks have no unfinished prerequisites. High priority sorts first within
these groups. Counts have literal meanings; there is no inferred health score.
Search and state filters keep completed work available without crowding the
initial view. Tasks refresh every five seconds, including changes from agents.
Open task details follow agent updates. **Full view** expands the popup;
**Back to popup** restores it. Evidence occupies its own full-width section.

The decompiler gives code the center of attention: project navigation occupies a
compact top strip, the searchable function browser sits on the left, and the
**Evidence & tasks** panel sits on the right on wide screens. Layout buttons
let you hide either side to give long expressions more space. On narrow screens,
functions and evidence open as dismissible overlays; selecting a function closes
the function browser. Evidence remains accessible at every width.

Use `/` to focus function search, and **Back** / **Forward** or `Alt+Left` /
`Alt+Right` to retrace function navigation. Following a known function name or
address keeps the browser selection visible, clearing a filter that excludes it.
Pseudocode, disassembly, references, call graph, control flow, records and
annotations share the same selected function. Arrow keys move between focused view tabs. **A− / A+** adjust code
text from 12 to 22 pixels (14 by default), with the preference retained in this
browser; **Wrap** also persists. Copy code or its CLI command, and ask an agent
to retain the function address as evidence in a task.

**Call graph** groups unique callers on the left, the selected function in the
center, and unique callees on the right. Click a caller or callee to navigate.
Unresolved indirect call targets are not included. Large function lists are
loaded in display batches; search always searches the complete list. Variables
are shown for pseudocode only.

**Disassembly** shows each instruction's address, raw encoding, length, control
flow kind and known target name. Saved comments appear at their instruction
address, with author and anchor match. **Annotations** shows saved names, types
and comments together; low-confidence anchor matches are marked explicitly.
Comments are also readable in the context panel while viewing pseudocode; e5r
keeps their instruction addresses rather than inventing source-line positions.

**References** defaults to incoming references to the selected entry address.
Its selector also offers **All outgoing references**, covering every recovered
block, and **Strings & data**, showing data/read/write references with section,
symbol, extracted string and encoding, or up to 32 mapped bytes. References into
a string retain its start address and byte offset. Click an instruction address
to open it in disassembly, or a known function target to navigate to that function.
A split function's unanalysed gaps do not contribute references.

**Control flow** draws the function's basic blocks and recovered successor edges,
with instruction counts, block endings and unresolved states. **View instructions**
opens the block's disassembly. A table retains every block, successor and target
outside the recovered blocks. Graphs with more than 160 blocks use the table to
keep the browser responsive; the table loads 200 blocks at a time with a button
to reveal the next batch. This graph describes control inside one function;
**Call graph** describes calls between functions.

The overview's **Binary information** section shows format, architecture, bitness,
endianness, entry point, image base, counts, container metadata and loader warnings.
Unavailable binaries leave the project records and tasks readable.

The visual hierarchy follows a repeatable reading path: project and mode at the
top, function selection at the left, function identity and output in the center,
then supporting evidence at the right. Body and code text carry the findings;
metadata is quieter but readable. Blue marks selection, focus and navigation;
amber marks attention and incomplete analysis. Status and provenance always
remain words, so color alone never carries an analysis claim. Project work and
records use the same surfaces and type hierarchy.

Design references: h5i's local console uses restrained surface steps and reserves
color for meaningful signals. [IDA's subviews](https://docs.hex-rays.com/ida-9.2/user-guide/user-interface/subviews)
keep function selection synchronized with the active view and retain navigation
history. [Ghidra's CodeBrowser](https://ghidra.re/ghidra_docs/GhidraClass/Beginner/Introduction_to_Ghidra_Student_Guide.html)
provides a stable function/listing/decompiler context. e5r uses these navigation
principles at function granularity; its analysis does not supply instruction to
pseudocode correspondence.

The library owns all analysis facts and all task readiness rules. The pane
shows boundary strength, source evidence, incomplete control flow, unmodelled
operations and signature conflicts. It does not imply that pseudocode is
verified source or fabricate a source-to-instruction mapping. Binary analysis
and annotations are a snapshot taken when the decompiler first loads. Restart
the server after changing binary bytes or annotations. Manifest changes and
relocated paths invalidate the cached analysis. Task data stays live. Signature-library references and patch-set references
remain in the project file; they are not automatically applied to the loaded
binary. Unknown analysis settings and custom readers are refused. Supported
analysis settings are `scan_gaps`, `follow_calls`, `strings`, `xrefs`, `noreturn`,
`data` (boolean) and `threads` (integer).

## The agent interface

The CLI writes the task store that the browser reads:

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
`function:0xADDRESS` evidence string shown in the function pane.

Task content is limited to 64 KiB. Writer names contain 1–200 bytes. `--input`
can also create a task from a full content document. Content flags
apply when supplying a title and cannot be combined with `--input`, which
supplies the whole content instead.
`--author` defaults to `E5R_AUTHOR`, then the OS user. The browser has no write controls.

## Durability and conflicts

Coordination lives in `<project>.work/T-0001.json`, one file per task, separate
from the existing binary project and annotation log. Each task retains previous
contents, writer names and timestamps. Commit the directory with the project.
Different task files merge normally; concurrent edits to the same task, or two
branches allocating the same new id, require a git conflict review. This store
does not claim the annotation log's order-independent merge semantics.

Local writes take a directory lock, check the revision and prerequisites, write
a synced temporary file, and rename it over the task. A stale update is refused
instead of overwriting the human or agent who edited first. Agents must reread and reconcile rejected updates. The lock and
scratch files are ignored by git. If a process dies during a write, inspect the
PID in `<project>.work/.lock`; remove that lock only after confirming the writer
is no longer running. Corrupt JSON is an error, never an invisible missing task.

## Local HTTP surface

The workspace binds IPv4 loopback only. Host and Origin checks reject cross-site
and rebound-host requests. All non-GET requests are refused with 405. Edits use the CLI. Analysis endpoints accept only a recovered function's address.

| Route | Meaning |
| --- | --- |
| `GET /api/projects` | all registered projects and live task signals |
| `GET /api/project` | project identity and container information |
| `GET /api/tasks` | shared task snapshot |
| `GET /api/functions` | recovered functions, using the existing `e5r/1` JSON |
| `GET /api/decompile/0xADDRESS` | one function's pseudocode |
| `GET /api/disas/0xADDRESS` | one function's instructions |
| `GET /api/xrefs/0xADDRESS` | incoming references |
| `GET /api/callgraph/0xADDRESS` | incoming and outgoing direct-call edges |
| `GET /api/context/0xADDRESS` | function-local annotations, outgoing references with target context, and CFG blocks (`e5r.context.v1`) |
| `GET /api/records` | findings, notes and reports |

In collection mode, workspace routes are prefixed with `/p/NAME` (for example,
`/p/parser/api/tasks`); `/api/projects` remains global.

Responses are JSON; task conflicts return 409, missing routes/functions return
404, invalid content returns 400. Analysis runs on a separate worker with a bounded queue, so project monitoring
and task viewing remain responsive during decompilation. Only one analyzed
program is resident at a time; switching projects evicts it. The existing budget is
checked between functions, so it is not a hard preemptive timeout for one very
large function. The CLI remains available independently during analysis.

## Checking changes

Run `cargo test --release --workspace` for Rust checks. For the browser workflow,
install Playwright and its Chromium browser outside the checkout, then run:

```sh
cargo build --release -p e5r-cli
E5R_PLAYWRIGHT_MODULE=/path/to/playwright/index.mjs node scripts/test-dashboard.mjs
E5R_PLAYWRIGHT_MODULE=/path/to/playwright/index.mjs node scripts/test-projects.mjs
```

The integration check compiles a small C binary with `cc`, starts an isolated
workspace on a free port, compares decompiler output with the CLI, tests live agent updates, read-only HTTP routes, records, call graphs and task full view, checks function navigation, comments, encodings, function-local outgoing/data references, CFG edges and linked evidence,
and verifies cross-origin rejection and mobile layout. It removes its temporary
project and stops the server when finished. Screenshots are written under `/tmp`.

The collection check verifies global registration/import, working-directory
independence, project isolation, CLI creation and read-only collection, decompiler access and binary
relocation with a temporary `E5R_PROJECT_HOME`.

## Findings, notes and reports

Agents write records; humans read them in the overview and function workspace. Each kind has a separate
revisioned store under `<project>.work/{finding,note,report}/`, using the same
content and history format as tasks. IDs and prerequisites are local to a kind.
Records do not contribute to task readiness or task counts. Imports preserve
all three stores along with tasks.

```sh
e5r project record parser finding add 'Length check before copy' \
  --description 'The recovered guard rejects lengths above 32 before the copy.' \
  --evidence function:0x401000 --author agent-a
e5r project record parser note add 'Open questions' --description 'Check indirect callers.'
e5r project record parser report add 'Parser investigation' --description 'Investigation text'
e5r project record parser finding list --json
e5r project record parser finding update T-0001 --revision 1 --input finding.json
```

Attach a note to a recovered function using its exact address as evidence:

```sh
e5r project record parser note add 'Input length checks' \
  --description 'The parser rejects lengths above 32 before the copy.' \
  --evidence function:0x401000 --author agent-a
```

The decompiler's **Function records** section shows notes, findings and reports
linked to the selected function. Click a record or open the **Records** tab to
read full text beside the function browser. Writer and revision are displayed; updates refresh every five
seconds without restarting analysis. Records linked to other functions and records
without a function link stay in the project overview. Selecting another function
changes the displayed records. The Records tab is also accessible on narrow screens.
The CLI command panel supplies a note creation command for the selected function.
Existing `annotate comment` entries remain analysis annotations, separate from
these live project records; comments are shown in disassembly and Annotations.

Full record text lives in `description`; use `--input FILE` for large content.
The UI renders text literally, including Markdown, without executing HTML.

Disassembly JSON (`e5r/1`) includes additive `bytes` and `target_name` fields for
each instruction. `bytes` is the mapped encoding in hex, or null if unavailable;
`target_name` is a known name for a direct flow target, or null. The JSON includes
encodings regardless of the CLI's text-only `--bytes` switch. Other CLI consumers
continue to receive the same fields as before.
