# swe-bin: SWE-bench Multilingual on binaries

An RL environment in which the agent fixes a real GitHub issue by producing the fixed binary
itself. It is built from the C (30) and Rust (43) tasks of SWE-bench Multilingual
(`SWE-bench/SWE-bench_Multilingual`). Each project is built as a static riscv64 Linux binary.
The agent edits that binary with nocompiler's tools; writing and compiling source is not
possible. The submission is judged by SWE-bench's criterion: every FAIL_TO_PASS and every
PASS_TO_PASS test passes against the submitted binary, run under `qemu-riscv64-static`.

Two modes share the tasks, the tests and the reward criterion:

| mode | starting binary | what the agent gets | naming |
| --- | --- | --- | --- |
| **patch** (default) | the base commit's binary | the issue | the SWE-bench port |
| **scratch** (opt-in, `--mode scratch`) | the base binary, with every function the gold patch changes replaced by a stub (`exit(127)`) | the issue, the tests, and per removed function its symbol, DWARF prototype, callers and size; no source | **SWE-bench-derived (function-level from-scratch)**, never reported as SWE-bench |

```
bench/swe-bin/
  toolchain/   build-sysroot.sh: musl 1.2.5 + compiler-rt + libunwind for rv64imafd_zba_zbb (no C
               extension: nocompiler refuses RVC), rv-cc; the no-C rustc target spec
  convert/     stage 1: convert.py (build base and gold, run the tests, validate, analyse),
               recipes.py (per repository), funcs.py (changed functions), rusttc.py (per-date
               nightlies), harness.py (the tests against any ELF), summary.py
  tasks/       one JSON per task: recipe and commands, sizes, profile levels, tests, the changes
  SUMMARY.md   counts by status and reason, one row per task
  env/         stages 2-3: kernel/ (pure, h5i-app), proofs/ (Lean), server/ (senv + MCP tools)
  smoke/       stage 4: smoke.py, scripted episodes over OpenEnv's own client
```

## Stage 1: conversion

For each task, `convert.py`:
1. builds the base commit's subject (the program the tests run, or for tokio, axum and ruff the
   test executable) with the recipe's commands;
2. applies the test patch and runs the SWE-bench test command, with the subject replaced by a
   wrapper `exec qemu-riscv64-static -0 "$0" ELF "$@"` (there is no riscv64 binfmt here). The
   test harness itself (Tcl, shell, run-tests.py, cargo integration tests) runs on the host;
3. builds the gold commit the same way. This is the environment's oracle, never an agent tool;
4. keeps the task iff every FAIL_TO_PASS test fails at base and passes at gold, and every
   PASS_TO_PASS test passes at both.

Tests that do not run a subject are excluded, each with its reason in the task JSON:
- oniguruma's own test programs in jq;
- in-process unit tests of host code;
- PASS_TO_PASS tests that the suite itself skips on riscv64 at both base and gold.

Builds:
- **C:** `rv-cc` with nocompiler's code-generation flags (medany, no relax, no PIC, no jump tables, block placement off), `-g`, `--emit-relocs`. redis and valkey use libc malloc (no jemalloc).
- **Rust:**
  - `-Zbuild-std` for the no-C target, with the nightly of the base commit's date (floor 2022-03-01; older std has no riscv64 musl libc), when the repository tracks a Cargo.lock;
  - otherwise (axum) the current nightly and a fresh resolution, as SWE-bench's images did.
  - Programs are built with `--release`. Test executables use the dev profile at opt-level 2, with debug assertions kept.

Recorded per task:
- the commands run;
- binary size and instruction count;
- `nocompiler check` levels;
- the functions and data the gold patch changes, in two views:
  - byte level: relocation-masked canonical forms (`funcs.canonical`);
  - source level: the patch's lines mapped to functions through the DWARF line tables (`funcs.functions_at_lines`);
  - the byte level also flags code the patch did not touch, such as every assert after an inserted line, whose `__LINE__` moved;
- what scratch mode removes (the source-level set) and its instruction count;
- the reason for each dropped task.

```bash
venv/bin/python convert/convert.py $SWB/dl/cr.jsonl --repo jqlang/jq     # or --only ID ...
venv/bin/python convert/convert.py $SWB/dl/cr.jsonl --reanalyze          # analysis only, from the artifacts
python3 convert/summary.py                                                # SUMMARY.md
```

Artifacts (base, gold, with and without debug info) are under `$SWB/artifacts/<id>/`; the
JSON gives each one's SHA-256.

## Stage 2: the kernel

`env/kernel/src/lib.rs` decides every reward and `done`, in the Rust subset that Charon and
Aeneas extract. Its state is the task (id, mode, test counts), the last test report and the last
proof result (each about one binary, by SHA-256), the submitted binary, `done` and the reward.
Commands:
- `Reset(task)`;
- `RecordTests(report)` and `RecordProof(result)`, both from the harness;
- `Submit(binary)`.

The reward is 1000 milli when the last report is about the submitted binary and every test of
both kinds passed. It is 1250 when, in addition, a checked proof about that binary is of the
mode's kind: `Refines` in patch mode, `Verified` against a non-vacuous spec in scratch mode. It
is 0 otherwise. `Submit` ends the episode.

`env/proofs/Theorems.lean` proves the following about the extracted kernel, for both modes:
- `reward_spec`, `submit_spec`;
- `full_reward_iff_all_pass`;
- `bonus_only_with_proof`, `patch_bonus_needs_refines`, `scratch_bonus_needs_verified`;
- `reward_values`;
- `no_reward_without_submission`, `only_submit_pays`;
- `done_is_final`, `task_is_fixed`, `reset_spec`;
- `panic_free`, `read_only_sound`.

`h5i app prove` gates 46 theorems on the standard axioms. `h5i app mutate` catches all 12
reward-hack mutants in `h5i-app.toml`.

## Stage 3: the server and the tools

```bash
cargo build --release -p swe-bin-env      # in env/
swe-bin-env --bind 127.0.0.1:8000 [--mode scratch] --nocompiler PATH
```

`reset(seed)` picks kept task `seed mod N` and creates the episode directory with the starting
binary. MCP tools (OpenEnv `call_tool`, over the WebSocket or `POST /mcp`):
- **files:** list_files, read_file, write_file (text only), copy_file;
- **nocompiler:** disasm, asm, check, funcs, symbols, sections, info, strings, stats, xrefs, decompile, diff, refine, emulate;
- **`link`:** an `asm` object into a binary; its functions replace the binary's, and calls go to the new code;
- **run_tests:** patch mode shows the PASS_TO_PASS results only, since FAIL_TO_PASS stays hidden as in SWE-bench; scratch mode shows all;
- **check_proof.**

The step action `{"submit": ["jq.elf"]}` checks that each file is a static RV64 executable,
runs every test, and reports to the kernel.

No tool runs a compiler, a shell or an interpreter on the agent's input. Each runs a fixed
argument vector over plain file names in the episode directory, with a time limit (60 s) and
an output limit (256 KiB). nocompiler's `cc`, `repl`, `ui`, `batch` and `project` are not
exposed.

## Stage 4: smoke test

```bash
$SWB/venv312/bin/python smoke/smoke.py --task jqlang__jq-2650                  # patch
$SWB/venv312/bin/python smoke/smoke.py --task jqlang__jq-2235 --mode scratch   # scratch
```

The script uses OpenEnv's own `MCPToolClient` (pinned checkout 58d0344, Python 3.12) and runs
two episodes per mode:
- the gold binary (patch mode), or the gold build's versions of the removed functions linked in with the `link` tool (scratch mode), gets 1000;
- the base binary, or the stubs, gets 0.

## Deviations and limits

- **Class B (tokio, axum, ruff):** the tests are compiled into the submitted test executable, so they are visible in it (lead decision Q1). A submission may change only functions of the crates under test, outside test modules; `harness.integrity` checks this against base before any test runs.
- **No proof bonus yet:** `check_proof` reports "not available". nocompiler cannot yet build the Lean module of a whole musl binary (STATUS-D R-D1, assigned to B). The kernel's bonus path is proved, but it cannot be reached yet.
- **Disassembly workaround:** until R-D1 lands, `disasm FILE FUNC` prints FUNC from a copy of the binary in which every other function is `ret` (`swb-elf isolate`). Functions outside the profile (F/D/A instructions) have no structured text; patch them with `nocompiler patch`, or rewrite them in profile code.
- **Platform:** musl rather than glibc, and qemu rather than hardware. A test that needs a glibc locale or real timing can fail at gold; such tasks are dropped with the reason (`tasks/notes.json`).
