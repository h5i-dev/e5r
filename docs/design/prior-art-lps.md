# Prior art: oss-verify-proofs and LPS

How theorem-labs/oss-verify-proofs ("OVP") and its semantics,
theorem-labs/rocq-linux-process-semantics ("LPS"), prove theorems about whole
RISC-V binaries. This is a read-only study. Every number below comes from a
command written next to it. Sections 1–6 are facts. The last section is our
reading of them.

**Versions read** (2026-11-21):

- LPS at `d3f3a701d99afeee638963228562f4b5ff6e96ba`: a full clone (34 MB).
- OVP at `90e648c1779a01da0f20d5f3932ccfa632cc6559`: a blobless, depth-1
  clone (`git clone --filter=blob:none --no-checkout --depth 1`). Only these
  paths were checked out:
  - the top-level files, `index/`, `docs/`, `theories/`, `.github/`;
  - three harness directories;
  - 400 randomly sampled proof files.
- The binaries come from the release asset `v2026.10.0/{zlib,zstd}-bin.tar.zst`.
  Their SHA-256s match `index/binaries.tsv`:

```
$ sha256sum zlib/checksum_fuzzer/checksum_fuzzer.plain zstd/fse_read_ncount/fse_read_ncount.plain zstd/simple_decompress/simple_decompress.plain
4f04e95082d3e0baa9d55c72288945d99e64bb7503e39c0e644f4b38a7781af2  (binaries.tsv: 4f04e950…af2)
422deab3981d9dac9868e7c5907b0c00e98079faa9a639039ff2ba190619929a  (binaries.tsv: 422deab3…9a)
915a2df41813d9b88edf3031572374cbd2ce35f51e6ce468dd861581d0957259  (binaries.tsv: 915a2df4…59)
```

Link prefixes used below:

- LPS = `https://github.com/theorem-labs/rocq-linux-process-semantics/blob/d3f3a701d99afeee638963228562f4b5ff6e96ba/`
- OVP = `https://github.com/theorem-labs/oss-verify-proofs/blob/90e648c1779a01da0f20d5f3932ccfa632cc6559/`

## 1. State and memory representation

| Part | Representation | Where |
| --- | --- | --- |
| Integer and FP registers | `bvmap 5 word` = `tree A`, a binary trie keyed by `positive` (`bv_key b = Z.to_pos (bv_unsigned b + 1)`); missing keys read 0; x0 is handled in `rget`/`rset` | LPS `theories/Riscv/Prelude.v#L104-L119`, `theories/Riscv/Sem.v#L285-L313` |
| Machine state | record `{ms_regs; ms_fregs; ms_pc_val; ms_svc_pending; ms_resv; ms_fcsr; ms_mem; ms_rom}` | LPS `theories/LinuxProcessSem/RiscvSemantics.v#L100-L109` |
| Memory | `ms_mem : word -> option byte`, a byte-level FUNCTION; writes nest closures (`write_to_mem`, `apply_writes`) | LPS `RiscvSemantics.v#L107`, `#L139`; `theories/LinuxProcessSem/Run.v#L96-L151` |
| File descriptors | association lists: `fdst_table : list (word * FdEntry)`, `fdst_pipes : list (word * PipeBuf)` | LPS `theories/LinuxProcessSem/State.v#L3591-L3593` |
| Kernel state | one record `Model` (fd, vm, io, fs, proc, limits, time, …) | LPS `State.v#L4885` |
| Trace / behaviour | `bh_traces : list event -> Prop` (a set of event lists) | LPS `Run.v#L81-L86` |

**Reasoning about reads after writes.**

- **Registers:** two trie lemmas, `bvmap_get_set_same` and
  `bvmap_get_set_other` (`Prelude.v#L121-L126`).
- **Memory: not by rewriting the function semantics.** The proof libraries
  work at a higher level:
  - the reflective symbolic executor keeps a store log, plus "knowledge"
    facts about the base memory (`KWord`, `KZero`, `KBlob`, `KImg`);
  - a load is resolved log-first, then knowledge, then a fallback side
    condition (`theories/Common/AxSymExec3.v#L20-L28`);
  - the proof libraries add separation-style heap predicates, e.g. `AREP`,
    `AHEAP_P`, `rw_cells` in OVP
    `projects/zstd/simple_decompress/proofs/lib/AsanT/AFake_arep.v`.

## 2. How execution is stepped in proofs

They use three engines. All are proved sound in LPS once, for every image:

1. **A reflective, certified symbolic executor** (`AxSymExec3`, 3,801 lines;
   soundness in `AxSymExec3Sound.v`).
   - It runs over symbolic values (constant folding, byte slices, base+offset
     addresses) and is evaluated by `vm_compute`.
   - Its soundness theorem `sym_exec_sound` turns a computed run, plus its
     side conditions, into `CatSim.msteps` from any concrete state the
     symbolic entry state describes.
   - Header: LPS `theories/Common/AxSymExec3.v#L1-L30`.
   - The workflow is one straight-line block per call (`sym_run_tac`):
     compute, apply soundness, leave the side conditions that `sc_auto`
     could not close. See LPS `theories/Common/AxSymRun3.v#L1-L25`.
2. **Reflective certificates checked once by the kernel** (`cert_refl`,
   `cert_refl_vm`).
   - A plan checker (e.g. `AsanPlan.AP.check`) is run beforehand to get its
     result `shape`.
   - Then `check ARGS plan = COk shape` is proved by a raw `eq_refl` cast
     handed to the kernel with `exact_no_check`. Conversion runs once, at
     `Qed`, by `native_compute` or VM.
   - Header: LPS `theories/Common/CertRefl.v#L1-L40`.
   - The header itself says native compilation is 3–5x faster on the ASan
     plan checks.
3. **A propositional single-step engine** (`PropExec`): per-instruction
   `step_*` lemmas over a pinned state shape (`mkst`), used by Ltac proofs.
   See LPS `theories/Common/PropExec.v#L1-L15`.

What the proved harnesses actually use, counted over the largest one:

```
$ grep -rhoE "\b(vm_compute|PropExec|msteps|CatSim|AsanPlan|AxSymExec3|sym_exec|SymExec|run_sound|sym_run_tac)\b" \
    projects/zstd/simple_decompress/proofs/lib | sort | uniq -c | sort -rn
   2428 vm_compute
    852 PropExec
    389 msteps
     73 CatSim
     64 AsanPlan
     57 AxSymExec3
     33 sym_exec
      8 SymExec
      2 run_sound
      1 sym_run_tac
```

The same lib, counted for proof tactics:

- `Lemma|Theorem`: 35,305;
- `Qed.`: 33,307;
- `lia`: 201,963;
- `native_compute`: 0;
- `cert_refl`: 0;
- `Admitted`: 0.

So the program-specific part is mostly ordinary lemma-and-`lia` proofs: heap
predicates, layout and range facts. `vm_compute` appears where blocks are run
or values are computed. No `native_compute` is used in the three harnesses
checked (command in section 3).

## 3. Per-instruction cost, three harnesses

**Instructions:**

```
llvm-objdump -d --no-show-raw-insn <elf> | grep -cE '^ +[0-9a-f]+:\s'
```

The binaries are stripped static musl executables, RV64GC (compressed
instructions count as one each).

**Proof sizes:**

```
find <harness>/proofs/lib -name '*.v' -print0 | xargs -0 cat | wc -l / wc -c
```

| Harness | Proved statements (index/proofs.tsv) | Instructions per build: plain / ubsan / asan / asan-ubsan | `proofs/lib` files / lines / bytes | `Proof.v` files / lines | Harness-level .v (Statements, Images, …) lines |
| --- | --- | --- | --- | --- | --- |
| zlib/checksum_fuzzer | plain_halts, plain_halts_may_fail | 9,892 / 10,045 / 105,037 / 105,148 | 625 / 246,398 / 15,998,349 | 2 / 20 | 348 |
| zstd/fse_read_ncount | plain_halts, asan_halts, asan_ubsan_halts, asan_agrees, ubsan_agrees, asan_ubsan_agrees (and a ubsan_halts proof dir added in 13295bb, not yet in the index) | 9,793 / 9,972 / 105,444 / 105,613 | 1,442 / 368,139 / 28,722,089 | 7 / 35 | 318 |
| zstd/simple_decompress | asan_agrees, ubsan_agrees, asan_ubsan_agrees | 28,391 / 34,522 / 150,827 / 155,303 | 3,977 / 1,072,498 / 86,936,691 | 3 / 15 | 316 |

**Proof lines per instruction.** Instruction counts are of the WHOLE binary
(libc, malloc and the sanitizer runtime included). The proofs cover only what
the statements reach, so these ratios are lower bounds on the cost per
instruction actually reasoned about.

- **zlib:** 246,398 lines / 9,892 (plain) = **24.9 lines/instruction**.
- **fse_read_ncount:**
  - 368,139 / 9,793 (plain) = 37.6;
  - over the four builds its proofs touch (9,793 + 9,972 + 105,444 +
    105,613 = 230,822) it is **1.6 lines/instruction**.
- **simple_decompress:**
  - 1,072,498 / 28,391 (plain) = 37.8;
  - over all four builds (369,043) it is **2.9 lines/instruction**. (The
    `agrees` statements relate each sanitizer build to plain.)
- **Bytes:**
  - the lib files average 64,000 bytes/instruction for zlib plain
    (15,998,349 / 9,892);
  - 3,062 bytes/instruction for simple_decompress over all builds.

**Shared library:**

- LPS: 351 .v files, 282,639 lines in total, of which:

  ```
  $ for d in theories/*/; do find $d -name '*.v' | xargs cat | wc -l; done
  theories/Common/                88,522 lines   4,504,836 bytes
  theories/EquivalenceDefinition/ 28,089 lines   1,360,278 bytes
  theories/Examples/               6,527 lines     305,421 bytes
  theories/LinuxProcessSem/      155,962 lines   7,734,444 bytes
  theories/Riscv/                  3,539 lines     156,362 bytes
  ```

- OVP's own shared `theories/` is 1,270 lines (59,556 bytes).

**Check time: not published for these proofs.**

- The `check:` field of `proof.yaml` (wall time and peak memory, written by
  CI; OVP `docs/proving.md#L29`) is absent in all 12 proof.yaml files of the
  three harnesses.
- The GitHub Actions jobs API returns no jobs for the PR runs that touched
  these proofs (runs 44023871896 and 43485486029: `total_count` 0 and a
  3-minute failed run, respectively).
- What they do publish:
  - "A full build uses about 45 CPU-minutes. Each compile job can use up to
    3 GB of memory" (LPS `README.md#L106`, the LPS library alone);
  - "On 16 cores, one proof check needs up to 20 GiB of memory" (OVP
    `README.md#L159`);
  - `rocqchk` without the bytecode machine "can take hours for the proofs of
    one harness" (OVP `docs/checking.md#L111`).
- So **seconds per instruction cannot be computed from published data.** We
  did not build Rocq 9.2 + LPS + a harness to measure it.

## 4. How proofs are split and reused

- **Per harness, many small modules.**
  - A statement's `Proof.v` is 5–10 lines: it applies lemmas from the
    harness's `proofs/lib`. For example, OVP
    `projects/zlib/checksum_fuzzer/proofs/plain_halts/Proof.v` is
    `apply plain_halts_from_valid_checksum. intros rc fx. apply checksum_valid_contract.`
  - The lib is split into hundreds to thousands of files, by function/block
    and by build variant (directories `Plain/`, `Ubsan/`, `AsanT/`, `BothW/`,
    `Malloc/`, `MayFail/`, `Reusable/`). The names suggest per-function and
    per-block lemmas (`F_printf_core_t*.v`, `AZ_huf_dx*_mr*.v`, `ASlot_W*.v`).
  - Rocq compiles the files in parallel (dune, one job per file; OVP
    `README.md#L159`).
- **Reuse across harnesses is by copying files, not by a shared library.**
  - zlib's lib has 482 of its 625 files marked "copied from": 455 from
    `proofs/cgif/cgif_file_fuzzer`, 27 from `varnish/esi_parse_fuzzer`.
  - Command: `grep -rh "copied from" … | grep -o "proofs/[a-z0-9_-]*/[a-z0-9_-]*" | sort | uniq -c`.
  - fse_read_ncount has 1 such file; simple_decompress has 0.
  - After normalising module paths (`OSSVerify.Proofs.<lib>.<harness>`) and
    dropping header lines, the three libs share **0 byte-identical files**,
    even the two zstd harnesses (1,432 and 3,964 distinct contents). Copies
    are edited, not shared.
- **Shared, image-independent machinery is in LPS** (`theories/Common`,
  88,522 lines: the executors, ASan plan checker, allocator interface,
  sanitizer windows). It is proved once.
- **Caching:**
  - inside a harness, dune caches compiled `.vo` files;
  - across releases, a proof is pinned to its statement's fingerprint
    (`proof.yaml`; OVP `docs/proving.md#L20-L30`), so an unchanged
    statement keeps its proof;
  - we found no content-addressed reuse of proofs of identical code across
    binaries.

## 5. What their theorems cover, against ours

- **Whole process, whole binary.** Statements are about the process run as
  `<file> FILE`, quantified over every input and every other process input:
  - `halts_within_budget`: exits 0 or 2, never crashes, hangs or "leaves the
    model";
  - sanitizer-build agreement with the plain build;
  - bounds;
  - decidability.
  
  Source: OVP `projects/zstd/simple_decompress/Statements.v`.
- **libc and malloc.** The binaries are static musl, so musl's code
  (including malloc, printf) is part of what is proved. The libs have
  `Malloc/` and `F_printf_core_t*` files; LPS has `Common/AllocIface.v`,
  `AllocSim*.v`.
- **Syscalls.** They are modelled by LPS against Linux v6.18.46:
  `theories/LinuxProcessSem/Sys/` (37 files: fs, mm, net, kernel, drivers),
  vDSO, mmap placement, stack layout.
- **Sanitizers.** ASan and UBSan builds are separate images. An ASan
  `halts` proof implies that ASan reports no error in the instrumented code;
  the shadow memory and runtime are modelled (`Common/Asan*.v`).
- **Ours today** (for contrast):
  - per function, over every layout, on a bare RV64IM core;
  - the environment is the `ecall` model only;
  - no libc or malloc;
  - leaf and simple-frame functions;
  - refinement between two versions of one function.

## 6. Totals

Rechecked at OVP HEAD `90e648c` (`index/statements.tsv`, `index/harnesses.tsv`):

```
statements 20421 Counter({'open': 19600, 'proved': 526, 'model-gap': 229, 'counterexample': 56, 'witnessed-false': 7, 'suspected-false': 3})
kinds proved Counter({'agreement': 255, 'halts': 179, 'bound': 46, 'decidability': 46})
proofs.tsv rows 526 libraries 32 entry points 90
harnesses 2183 sum statements 20421 sum proved 526 false 63
```

This confirms our earlier count: 20,421 statements, 526 proved. The proved
ones are on 90 harnesses of 32 libraries.

**The "180 million lines" claim: not confirmed.**

- File inventory from the tree listing (no blobs downloaded):

  ```
  git ls-tree -r --name-only HEAD
  269,846 files; 247,975 .v files, of which 241,498 are under proofs/lib/ (93 harnesses), 5,845 harness-level
  ```

- Sampling 400 lib files uniformly at random (seed 20261121, one sparse
  checkout) gave:
  - mean 315.5 lines, median 197, max 2,651;
  - mean 52,926 bytes.
- Estimate for all proof-library .v files:
  - **76.2 M lines (±9.0 M, 2 standard errors)**;
  - about 12.8 GB uncompressed.
  - For comparison, the GitHub API reports `size` 4,193,011 KB for the
    packed repository.
- The other 6,477 .v files are harness-level and small (316–348 lines in
  the three sampled harnesses).
- So the repository holds roughly **70–85 M lines of Rocq**, not 180 M.
- We did not count non-.v files (.c sources, .log, .out, .tsv). Only a
  count including them, or including generated memory-image modules (which
  exist only under `_build/`; OVP `projects/*/*/images/dune`), could reach
  180 M. We did not measure either.

---

## What this implies for nocompiler (our reading, not facts)

1. **Their scale comes from automation volume, not from cheap
   per-instruction proofs.**
   - At 1.6–37.8 proof lines per binary instruction, and tens of megabytes
     of proof per harness, OVP proofs are large: 25–3,000 bytes per
     instruction.
   - The 1 ms/instruction budget in our design is a different regime. No
     published OVP number shows that rate, and none shows it is out of
     reach.
2. **Reflection is the part worth copying.** LPS proves the block executor
   (`AxSymExec3`) and the plan checkers sound once, then runs them by
   `vm_compute`, and with `cert_refl` the kernel evaluates once at `Qed`.
   That matches the required design for our VC generator: a verified
   evaluator, no per-instruction proof terms. Their engines still leave side
   conditions per block (`sc_auto`) that the program-specific libraries
   close by hand-style lemmas. Those lemmas are where their line count is.
3. **Representation.**
   - LPS uses a trie for registers but a byte-level function for memory,
     and avoids the cost of the latter by reasoning over a symbolic store
     log plus knowledge facts, not over the function.
   - That supports the lead's plan: keep the trusted semantics, and add a
     proof-side word-level memory and a flat register file with a one-time
     equivalence proof.
4. **Reuse.**
   - OVP's cross-harness reuse is copy-and-edit, with zero byte-identical
     files between the two zstd harnesses.
   - Content-addressed reuse of proofs of identical code (our ledger hash,
     function/subtree byte equality in refinement) would be new relative to
     them, and is the lever for whole-binary scale when most code (libc,
     runtime) is shared between binaries.
5. **Statements.**
   - Their `agrees` statements (a sanitizer build agrees with the plain
     build) are the same shape as our `Refines` between two binaries.
   - Their `halts` statements quantify over all process inputs, which is
     what the 2026-11-21 decision 3 asks of A in a refinement (A runs, for
     all inputs).
   - Their trust base is larger than ours (the Linux model, 155,962 lines of
     `LinuxProcessSem`), and covers libc, syscalls and sanitizers, which
     ours does not.
6. **Data we still lack:**
   - their check time per proof (not published for these three harnesses);
   - how many instructions each proof actually reasons about (as opposed to
     the binary's size).
   
   Measuring either needs a Rocq 9.2 + LPS build. We did not do it.

---

## Implementation plan (B, round2-next.md)

**Files B owns** (round2-next.md):
- `lean/NoCompiler/{Module,Relocate,Refine*}.lean`
- `lean/Examples/**`
- `docs/isa/{refine,ledger}.md`

**Not mine, needed by step 2** (requested in STATUS-B, waiting for the lead):
- `crates/nocompiler/src/treediff.rs` and `crates/nocompiler/tests/treediff.rs`.
  The tree diff writes `theorem refines … : Refines …` into
  `lean/Examples/Refine/Diff/*.lean`, and the test compares those files with
  its output. Changing the statement therefore needs a one-line change in
  the generator.
- `lean/Audit.lean`: theorem names stay the same, so it needs no change.

**Step 1: decision 2, a layout-dependent `Verified`** (Module.lean,
Relocate.lean, Examples/Link.lean).

```lean
def Verified (M : Module) (f : Sym) (spec : Layout → Spec α) : Prop :=
  ∀ L, M.Ok L → VerifiedImg (M.link L) (M.dom L f) (L.addr f) (spec L)
```

- A spec that mentions a data address writes `L.addr "table"`. A
  layout-independent spec is `fun _ => sp`.
- `Verified.of_leaf`: a leaf without relocations reads no symbol, so it
  concludes `Verified M f.name (fun _ => sp)`.
- `Verified.mono` is generic in `spec`.
- Migrate `Examples/Link.lean` (`sum_relocatable`, `sum_in_any_program`).
  Nothing else uses `Verified`:
  `grep -rlw Verified lean --include=*.lean` gives Module, Relocate, Shift
  (a comment only), Link and Audit (names only).
- Then the first data-symbol theorem: a leaf that loads from a data symbol
  through `auipc`/`ld` relocations. Its spec reads `L.addr d`, and it is
  proved over every layout from one image. That needs a pcrel-data case of
  `Verified.of_leaf`. This is a separate commit after step 1.

**Step 2: decision 3, Refines carries a full proof that A runs**
(Refine*.lean, Examples/Refine/**).

```lean
def ARuns (sp) (cA DA eA) : Prop :=          -- A runs safely and ends, for every entry sp allows
  ∀ a s, Entry DA eA s → sp.pre a s → Exec cA (sp.perm a s) DA (fun _ => True) s
def RefinesRel (sp) (cA DA eA cB DB eB) : Prop := …today's Refines…   -- conditional on A's run
structure Refines (sp) (cA DA eA cB DB eB) : Prop where
  runs : ARuns sp cA DA eA
  rel  : RefinesRel sp cA DA eA cB DB eB
theorem ARuns.of_verified : VerifiedImg cA DA eA sp → ARuns sp cA DA eA
```

- Today's `Refines` assumes `Exec cA …` as a premise, so it holds vacuously
  for an A that never runs. Under the structure above, a `Refines` cannot
  be stated without A's proof.
- The proof methods produce `RefinesRel`:
  - `of_sim`, `of_bigSim`, `of_lockstep`, `of_cert`;
  - `nocompiler_refine` (RefineAuto.lean).
- `Refines.of_cert (hA : ARuns …) …` and friends build the structure.
- `Refines.refl` takes `ARuns`. `trans` and `verified` read `.runs`/`.rel`.
- Every example's `refines` supplies `ARuns.of_verified sum_verified`
  (Relink, Peephole, Jump, Diff).
- The generated `refines` becomes
  `theorem refines (sp) (hA : ARuns sp A…) : Refines sp A… B…`. That is the
  generator change requested above.
- Controls: a crashing A (an `ebreak`-like illegal word) has a `RefinesRel`
  to anything, but `ARuns` for it is refuted by `decide` on its one step.
- Audit (not mine): suggest that it reject any theorem whose conclusion is
  `RefinesRel` in an `Examples.` namespace. Posted to STATUS for the lead
  and the Audit owner.

**Step 3: a written plan for porting the LPS environment model to Lean, with
a first step.**
- The plan doc is `docs/design/lps-port.md`, which needs the lead's OK as a
  new file.
- Scope order: process start state (stack, auxv), then `exit`/`write`/`read`
  on fds as lists, then `brk`/`mmap` placement.
- The first step: a Lean `SyscallEffect`-style record and the `exit_group`
  and `write` cases, checked against LPS's Rocq text side by side.

**Measured budget** (lake env lean per file, today, on this machine; command
`for f in …; do time lake env lean $f; done`):

| File | Time |
| --- | --- |
| Module.lean | 1.5 s |
| Relocate.lean | 5.7 s |
| Refine.lean | 1.2 s |
| RefineLockstep.lean | 3.6 s |
| Examples/Link.lean | 2.4 s |
| Relink.lean | 3.7 s |
| Peephole.lean | 4.0 s |
| Diff.lean | 2.2 s |
| Jump.lean | 3.2 s |

Steps 1 and 2 may change each by at most +20 % (they add one argument or
field, no new stepping). They are re-measured with the same command, and the
numbers go in the commit message.

**Chunks:** each step is one commit of at most a few hundred lines. Each
lands on `next` only after `lake build`, the audit, `cargo test -p nocompiler
-p nocompiler-cli`, fmt and clippy, with outputs in STATUS-B.md.

---

## Plan: porting the LPS environment model to Lean (step 3 of the plan above)

**What there is to port.** All counts are from LPS d3f3a701:

```
find theories/LinuxProcessSem/<dir> -name '*.v' | xargs cat | wc -l
grep -cE "^\s*\(\* [a-z_0-9]+ +\*\)"    # over Sys/SyscallTable.v's spec_table
```

- **Syscall surface:** 93 syscalls, one arm each in `spec_table`
  (`theories/LinuxProcessSem/Sys/SyscallTable.v#L41`). It includes
  accept…write, `brk`, `mmap`/`munmap`/`mremap`/`mprotect`, `openat`,
  `read`/`write`/`readv`/`pwrite64`, `clone`, `futex`, signals, time,
  sockets and `getrandom`.
- **Syscall semantics:** `Sys/` is 37 files and 31,871 lines:
  - Fs: 13,883;
  - Kernel: 6,783;
  - Mm: 5,110;
  - Net: 3,241;
  - Drivers: 151.
- **Kernel and process state:** `State.v` is 10,888 lines.
  - `SyscallInput` (#L654) and `SyscallEffect` (#L719) are the interface
    between the machine and a syscall.
  - `Model` (#L4885) holds the fd table, VMAs, I/O streams, fs, creds,
    limits and time.
- **Running:**
  - `Run.v` (6,827 lines) has `apply_effect` (#L96-L226), the initial
    state and the step relation;
  - `StackLayout.v` (626) has argv/envp/auxv;
  - `Vdso*.v` covers the vDSO.
- **Conformance:** `Checks/` is 154 files and 99,491 lines.

**What we have.** `lean/NoCompiler/Env.lean` defines `Sys : State → State →
Prop` with `write` (fd-agnostic, any accepted length), `read`, and
`exit`/`exit_group`. It has no fd table, no memory map, no process start
state, and the trace has `write`/`read`/`exit` events (`Machine.lean#L22`).
It is trusted (docs/isa/trust.md) and not in my file list.

**Design: keep the trusted core, add a Linux layer beside it.**

1. **Same interface as LPS.** A syscall is a relation from a
   `SyscallInput` (a7, a0..a5, the readable and writable views of memory)
   and the kernel state to a set of allowed outcomes. An outcome is a
   `SyscallEffect`:
   - the return value;
   - writes;
   - zero-filled, unmapped and copied ranges, kept symbolic as `(base,
     size)`. LPS's comment at `State.v#L719ff` explains why: multi-megabyte
     grants stay O(1) in proofs.
   
   `applyEffect` is deterministic. Porting it arm by arm keeps each Lean
   definition next to its Rocq source, citing the same Linux v6.18.46 file
   and function.
2. **One state for the process.** It holds our `State` (machine) and a
   `Kern` record (fd table as a list, VMAs, brk, I/O streams), as LPS does.
   - Our existing `Sys` must become a theorem, not a definition: the Linux
     layer, restricted to fds 0/1/2 and to `write`/`read`/`exit`, admits
     exactly the transitions `Sys` admits.
   - Every existing proof then stays valid, by that refinement.
3. **Validation, not trust by translation.**
   - LPS ships an extraction (`theories/Riscv/Extraction.v`) and its
     `Checks/`.
   - We would run the same syscall sequences through the Lean definitions
     (`#eval`) and through LPS's extracted checker, and diff the outcome
     sets. This uses the method our ISA semantics already uses against
     qemu/Sail.
4. **Cost.**
   - Effects are applied once per syscall, symbolically, so a proof pays
     per syscall, not per byte.
   - The reflective VC generator (C) treats an `ecall` as a call into this
     relation: per syscall arm, one lemma proved once.

**Order** (each item is a chunk of at most a few hundred lines; what static
musl binaries like OVP's need first):

1. `SyscallEffect` and `applyEffect` (writes, zeros, unmaps), plus the
   `write`/`read` arms on an fd table with 0/1/2, and `exit`/`exit_group`.
   Then the theorem that this restriction is our `Sys`.
2. The process start state: argv/envp/auxv on the stack, from
   `StackLayout.v`.
3. `brk`, `mmap`/`munmap` with Linux's placement (`Mm/`), and
   `set_tid_address`, `rt_sigprocmask`, `ioctl(TIOCGWINSZ)`, `writev`: the
   calls a static musl `main` makes before and after user code.
4. `openat`/`close`/`fstat`/`read` over an in-memory file system (`Fs/`),
   for the fuzz-driver shape `<file> FILE`.

**First step (proposed, after the lead's OK on files).**
- New files: `lean/NoCompiler/Linux/Effect.lean` and
  `lean/NoCompiler/Linux/Basic.lean`. They are not in my list (R4 in
  STATUS-B).
- `Effect.lean`: `SyscallInput`, `SyscallEffect`, `applyEffect`, ported
  from `State.v#L654-L726` and `Run.v#L96-L226`.
- `Basic.lean`: `exit_group`, and `write`/`read` on fds 0/1/2.
- The theorem `Linux.basic_iff_sys : Linux.Basic s s' ↔ Sys s s'` for
  machine states whose fd table is the initial one.
- Its budget: the `#eval` differential test against LPS's extraction for
  the three arms, and `lake env lean` under 5 s per file.

### First step of the port: done (lean/NoCompiler/Linux/)

- **`Linux/Effect.lean`:**
  - `SyscallInput` (a7, a0..a5, memory) and `Effect` (`ret`, `writes`,
    `zeros`), as LPS `State.v#L654`/`#L719`;
  - `Effect.mem`: zeros, then writes, in LPS's order (`Run.v#L96-L226`);
  - `Outcome` (return with an effect and maybe an event, or exit) and
    `Outcome.apply`.
- **`Linux/Basic.lean`:**
  - `readSpec`, `writeSpec`, `exitSpec`;
  - `spec`, a dispatch on the syscall number in the place of LPS's
    `spec_table`;
  - the step relation `Basic`;
  - **`basic_iff_sys : Basic s s' ↔ Sys s s'`**: the layer admits exactly
    the transitions of the trusted `Sys` (Env.lean), so every existing proof
    holds of it;
  - the control `no_step_unmodeled`: `close` (57) has no step.
- **Axioms** (`#print axioms`): both theorems depend on `[propext]` only.
- **Cost:** `lake env lean`: Effect.lean 0.45 s, Basic.lean 0.66 s (budget
  5 s).
- **Not done:**
  - the differential test against LPS's extraction. No Rocq is installed
    here (`opam` reports "Opam has not been initialised"); it needs a Rocq
    9.2 + LPS build on /mnt/scratch;
  - `eff_unmaps` and `eff_copies`, which need partial memory;
  - an fd table;
  - errno values.

### Second step: the fd table (lean/NoCompiler/Linux/Fd.lean)

- `Kern` (the open descriptors; `Kern.init` = 0, 1, 2) and `fdSpec`:
  - `read`/`write` on an open fd behave as in Basic.lean;
  - on a closed fd the only outcome is EBADF (-9);
  - `close` (57) returns 0 and removes an open fd, or EBADF.
- `FdStep.sys`: at every syscall other than `close`, a step of this layer
  is a step of `Sys`, so existing proofs cover it.
- Control `write_closed_fd`: in a fresh process, writing fd 5 can only give
  EBADF.
- Axioms: `[propext]`. `lake env lean Fd.lean`: 0.47 s.
- Next: the process start state (argv/envp/auxv, LPS `StackLayout.v`), then
  `brk`/`mmap`.

### Third step: the process start state (lean/NoCompiler/Linux/Start.lean)

- Ported from LPS `StackLayout.v`: `wordBytes` (`word_le8`), `stringAddrs`
  (`string_addrs`) and `flattenStrings` (`flatten_strings`).
- `StartArgs` (argv, envp, auxv pairs, string base). Its head words are
  argc, the argv pointers, 0, the envp pointers, 0, the auxv pairs and
  AT_NULL, in `build_stack_bytes`'s order.
- `StartState entry a s`: pc at entry, no exit, empty trace, the head at sp,
  the strings at the string base.
- `argc_at_sp`: the word at sp is argc. `argv_at`: the word at
  sp + 8(i+1) is argv[i]'s address. Both are proved from
  `read64_of_wordBytes` and `read64_word`.
- Axioms: `[propext, Quot.sound]`. `lake env lean Start.lean`: 1.4 s.
- The string base is now computed as LPS does: `blockItems`,
  `launchStringBytes`, `stringBaseAddr`, `atExecfnPtr`. Theorem
  `envp_end_eq_execfn`: argv then envp, laid from `stringBaseAddr`, end
  exactly at AT_EXECFN's file name (`[propext, Quot.sound]`).
- The auxv entries as LPS lists them: `LaunchAuxv`, `PhdrInfo`,
  `auxvEntries` (ARCH_DLINFO's ten, the sixteen unconditional ones, the
  rseq pair; AT_NULL is appended by `headWords`).
  - `auxvEntries_count`: 27 entries with AT_NULL, 29 with CONFIG_RSEQ, as
    LPS `auxv_count`.
  - `auxv_pagesz_entry`: AT_PAGESZ = 4096 and AT_ENTRY = entry.
- Still parameters: AT_RANDOM's bytes and the alignment pads (LPS
  `at_random_bytes`, `block_pad_len`).

### Fourth step: `brk` (lean/NoCompiler/Linux/Brk.lean)

- `Kern` gains `startBrk`/`brk`. `brkSpec` follows LPS `brk_r_ok`:
  - a query, or a request below the start: the break, unchanged;
  - a grow: the new break, with [PAGE_ALIGN(old), PAGE_ALIGN(req))
    zero-filled (`brk_zeros`), or failure;
  - a shrink: NO outcome (fail closed), because our memory is total and
    cannot say "unmapped" (Linux faults on the freed pages).
- LPS's grow gates (other mappings, the memory budget) are not modelled. A
  grow here may succeed where LPS refuses it: an over-approximation, which
  is sound for proofs over every outcome.
- `procSpec`/`ProcStep` combine `brk` with the fd layer.
  - `ProcStep.sys`: at every syscall but `close` and `brk`, a step is a
    `Sys` step.
  - `brk_query`, `brk_grow`, and the control `brk_shrink_none`.
- Axioms: `[propext]` / `[propext, Quot.sound]`. `lake env lean Brk.lean`:
  0.40 s.

### Fifth step: anonymous `mmap` (lean/NoCompiler/Linux/Mmap.lean)

- `Kern.maps` records the mappings. `mmap(0, len, prot, MAP_PRIVATE |
  MAP_ANONYMOUS, -1, 0)` gives either:
  - some page-aligned range of PAGE_ALIGN(len) bytes, below TASK_SIZE,
    disjoint from every earlier mapping, zero-filled and recorded; or
  - ENOMEM.
  
  Linux picks one particular address (LPS runs its placement search). Any
  free one is allowed here, which over-approximates Linux and is sound.
- Every other `mmap` and `munmap` has no outcome (fail closed).
- `ProcStep2.sys`: at every syscall but close/brk/mmap/munmap a step is a
  `Sys` step.
- `mmap_fresh`, and the controls `munmap_none`, `mmap_file_none`.
- Axioms: `[propext]`. `lake env lean Mmap.lean`: 0.42 s.
- Not yet: `brk`'s grow is not recorded in `Kern.maps`, so an `mmap` may be
  given pages that overlap the heap.
- Open, a design question for the lead: partial memory, so that unmapped
  pages fault (`munmap`, `brk` shrink, PROT_NONE). Loads and stores are
  stepped by the trusted `Step`, which does not see `Kern`. Faulting there
  needs either a process-level step that checks accesses against
  `Kern.maps`, or a partial `State.mem` (Machine.lean, not mine).

### Sixth step: `writev` (lean/NoCompiler/Linux/Writev.lean)

- `writev(fd, iov, iovcnt)` gathers the iovecs' buffers (`gather`).
  - On an open fd with iovcnt ≤ 1024, it has `write`'s outcomes for the
    gathered bytes (`writeBytesSpec`).
  - More than 1024 iovecs: EINVAL. A closed fd: EBADF.
- `writev_one`: with one iovec, `writev` has exactly the outcomes of
  `write` of that buffer (`writeSpec`, Basic.lean).
- `ProcStep3.sys`; the control `writev_too_many`.
- Axioms: `[propext, Quot.sound]` / `[propext]`. `lake env lean
  Writev.lean`: 0.48 s.
