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
