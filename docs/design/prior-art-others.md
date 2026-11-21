# Prior art: LNSym, Vale, Islaris (machine-code proofs at scale)

Round-2 study (step 2b). It records what these projects do, with links to files and lines, and numbers with the commands that produced them. It is followed by a separate section of conclusions for nocompiler. Facts and conclusions are kept apart.

Checkouts read (under `/mnt/scratch/ec2-user/prior-art/`):

| Project | Repository | Commit | Date |
| --- | --- | --- | --- |
| LNSym | https://github.com/leanprover/LNSym | `49f8a1d9e46f8dcfc345f4bc15d35b0ba845ff5c` | 2026-11-06 |
| Vale (tool) | https://github.com/project-everest/vale | `bbae0eb89143734363b14a77642dbf8dec36e288` | 2024-02-07 |
| Vale/F* code (in HACL*) | https://github.com/hacl-star/hacl-star (`vale/code`, sparse checkout) | `f557259007db9933442dde10aa995c1b00bd3446` | 2026-10-29 |
| Islaris | https://github.com/rems-project/islaris | `c978e10f50db5c40f0fdf113f5f76a779782c6f9` | 2024-09-11 |

Links below are to these commits, written as `LNSym:Arm/State.lean:144`, which means https://github.com/leanprover/LNSym/blob/49f8a1d9e46f8dcfc345f4bc15d35b0ba845ff5c/Arm/State.lean#L144.

The nocompiler numbers this compares against are those stated in round2-C.md: nocompiler_auto spends 69% of its time on goals with byte-level memory, a goal grows to about 40k characters from unmerged register writes, and 500 instructions fails. They are not yet in docs/isa/v1-results.md, where criterion 7 is still open.

## 1. LNSym (AWS, Lean 4, Armv8)

LNSym is on the same Lean as nocompiler (`lean-toolchain`: `leanprover/lean4:v4.35.0`). It is 202 `.lean` files, 45,232 lines (`find . -name "*.lean" | xargs wc -l`).

### State and memory

- **The state is a record of total functions.** `abbrev Store α β := α → β` (LNSym:Arm/State.lean:20). `ArmState` holds `gpr : Store (BitVec 5) (BitVec 64)`, `sfp : Store (BitVec 5) (BitVec 128)`, `pc`, `pstate`, `mem : Store (BitVec 64) (BitVec 8)` (byte memory), `program` and `error` (LNSym:Arm/State.lean:144-168).
- **The program is not in memory.** "the program is always disjoint from the rest of the memory" is an assumption of the model (the docstring of `program`, same lines). This is the same choice as nocompiler's `Code` image.
- **Fields are read and written through `r`/`w` on a `StateField`** (LNSym:Arm/State.lean:268). There are four rewrite lemmas: `r_of_w_same`, `r_of_w_different`, `w_of_w_shadow` and `w_of_w_commute` (LNSym:Arm/State.lean:429-470). Memory has `read_mem_of_write_mem_same`/`_different` (:798, :802) and `r_of_write_mem` (a write to memory does not change registers, :719).
- **Byte ranges carry separation predicates.** These are `mem_legal' a n` (`a.toNat + n ≤ 2^64`), `mem_separate'` (two ranges disjoint, as `Nat` inequalities) and `mem_subset'` (LNSym:Arm/Memory/Separate.lean:226, :320, :406).
- **`simp_mem` simplifies `read_bytes` over `write_bytes`** (LNSym:Arm/Memory/SeparateAutomation.lean, header comment). For each read over a write it proves either separation or containment:
  1. from hypotheses;
  2. by transitivity of subset;
  3. by reducing the range facts to linear arithmetic and calling `omega`.
  
  It replaces the read with the old read or with an `extractLsBs` of the written value. Reads over writes are thus decided on whole ranges, not byte by byte.

### How execution is stepped

- **A step theorem is generated per program address, once.** `#genStepEqTheorems program` (LNSym:Tactics/StepThms.lean:231-262) produces one theorem `stepi_eq_0x<pc>` per address. Its statement is `stepi s` for a state at that pc, with the given program and no error, equal to an explicit chain of `w`/`write_mem` on `s`. Decoding is done by `reduce` with caching (`reduceDecodeInst`, :117).
- **The symbolic run itself (`sym_n n`, LNSym:Tactics/Sym.lean:378) never re-decodes an instruction.** Each step (`sym1`, :240-306) does the following:
  1. splits `sf = run (n+1) s` into the next state (`init_next_step`, :38);
  2. applies the pre-generated `stepi_eq_0x<pc>` (`stepiTac`, :53);
  3. runs one `simp` with the alignment fact;
  4. "explodes" the step equation (`explodeStep`, :170) into one hypothesis per changed field.
- **The current state is tracked as `AxEffects`** (LNSym:Tactics/Sym/AxEffects.lean, docstring at the top). It is a hash map from each `StateField` to its current value *in terms of the initial state*, with a proof per field, plus one `nonEffectProof`: every field not in the map reads as in the initial state. Memory is tracked separately as one chain of `write_mem` on the initial state (`MemoryEffects`, LNSym:Tactics/Sym/MemoryEffects.lean:11-30).
- **The goal never holds a chain of writes.** The symbolic state is a fresh variable per step, `s1`, `s2`, …, with per-field equations.
- **Blocks of steps are also pre-generated.** `program.blocki_eq_0x<pc>` gives `run block_size s` for a basic block as one equation, built by `sym_block` (LNSym:Tactics/SymBlock.lean). SHA-512 uses 46 of them (`grep -c "^theorem\|^private theorem" Proofs/SHA512/SHA512LoopBlocks.lean`: 46, in a 5,543-line file).
- **`bv_decide` is used for bit-vector identities, with stored LRAT certificates.** `bv_check "lrat_files/…lrat"` checks a stored certificate instead of re-running the SAT solver (LNSym:Proofs/SHA512/SHA512_block_armv8_rules.lean:36, :48; also 9 certificates for memory-separation lemmas in `Arm/Memory/lrat_files/`). Uses by file (`grep -rn "bv_check\|bv_decide" --include=*.lean | cut -d: -f1 | sort | uniq -c`): Proofs/Experiments/Max/MaxTandem.lean 29, Arm/Insts/Common.lean 19, Arm/Memory/SeparateProofs.lean 18, Proofs/Bit_twiddling.lean 12, Proofs/SHA512/SHA512_block_armv8_rules.lean 10.

### Size of what is proved

Programs, as instructions listed in the program definitions (`grep -cE '^\s*\(0x[0-9a-f]+#64\s*,' FILE`):

| Program | Instructions | Proof file | Lines | `sorry` |
| --- | --- | --- | --- | --- |
| SHA-512 block (`Tests/SHA2/SHA512Program.lean`) | 503 | Proofs/SHA512/*.lean | 6,600 in total | 11 (SHA512Loop 6, BlockSym 3, Prelude 2) |
| AES-GCM enc kernel | 718 | AESGCMEncKernelSym.lean | 54 | 1 |
| GCMGmultV8 | 27 | GCMGmultV8Sym.lean | 328 | 3 |
| GCMInitV8 | 152 | GCMInitV8Sym.lean | 106 | 0 |
| AES HW encrypt | 20 (run for 60 steps) | AESHWEncryptSym.lean | 171 | 0 |
| Popcount32 | 26 | Popcount32.lean | 128 | 0 |

(The `sorry` counts are `grep -c sorry FILE`. Some are in comments. LNSym:Proofs/SHA512/SHA512BlockSym.lean:71 says one theorem "still ends in its pre-existing `sorry`".)

- **The SHA-512 and AES-GCM-kernel proofs are not complete.**
- **GCMInitV8 is complete.** It is one theorem (LNSym:Proofs/AES-GCM/GCMInitV8Sym.lean:32): `sym_n 152` over the straight-line program, then `bv_decide`. It proves the register results of all 152 instructions against the spec (`GCMV8.GCMInitV8`). The memory conjuncts are commented out (":TODO: Commenting out memory related conjuncts").
- **The AES HW encrypt proof unrolls its loop by hand:** `sym_n 7` per round, with a comment that the branching condition is not supported (LNSym:Proofs/AES-GCM/AESHWEncryptSym.lean:36-38, "sym_n 13 fails with …motive is not type correct").

### Per-instruction cost (measured here)

These are LNSym's own benchmarks (LNSym:Benchmarks/SHA512_{50,150,400}.lean):
- `sym_n N` on the SHA-512 block, then one `simp`;
- the alignment side goals closed by `sorry` (`all_goals exact (sorry : Aligned ..)`);
- what is proved: no error, and the value of `x2` after N steps.

They measure symbolic simulation, not a whole proof.

Commands (Lean capped at 6 GB):

```
lake build Benchmarks.SHA512 -v                  # dependencies: 2:44 wall, max RSS 1.64 GB
lake build Tactics.Sym Benchmarks.Command
lake env lean -Dbenchmark=true -Dbenchmark.runs=1 Benchmarks/SHA512_N.lean
```

`Proofs.SHA512.SHA512StepLemmas`, which generates the step theorems for all 503 instructions, took 52 s of the dependency build (`grep Built lnsym-build.log`).

These are single runs on this host. The host is shared with other agents, and its load was not controlled. "Proof" is the time the benchmark command reports for elaborating and kernel-checking the theorem. "Wall" is the whole `lean` process, imports included. An imports-only file (`import Tactics.Sym`, `Benchmarks.SHA512`, `Benchmarks.Command`) took 3.99 s wall, max RSS 1.56 GB.

| Steps (instructions) | Proof (reported) | Wall | Max RSS | Proof / instruction |
| --- | --- | --- | --- | --- |
| 50 | 1 s | 9.99 s | 1.62 GB | about 20 ms |
| 150 | 6 s | 18.77 s | 1.86 GB | about 40 ms |
| 400 | 44 s | 48.17 s (50.02 s on a second run) | 3.14 GB | about 110 ms |

The time per instruction grows with N (1 → 6 → 44 s for 50 → 150 → 400), so this is not linear. The `_noKernel_noLint` variants (kernel check skipped, linters off) reported 4 s, 34 s and 69 s for 50, 150 and 400. That is *slower* than the variants with the kernel check, which I cannot explain from these runs (it may be load from other jobs). So I do not use them to split elaboration from kernel time.

## 2. Vale (Vale/F*)

### State and memory

- **The machine state is a record** with register files as functions, flags as one word, and "memory is a partial map from integer addresses to bytes" (POPL'19 paper, §4). `vale_state` holds `vs_regs`, `vs_heap`, … (hacl-star:vale/code/arch/x64/Vale.X64.State.fsti:14-23).
- **Code is not proved against bytes.** It is proved against a *lifted* view: arrays of bytes, then arrays of wider types (`mem64`, `mem128`) over Low* buffers. A `correct_simulation` relation between the views is proved once (paper, Fig. 6, §4.2). Memory is split into heaplets (`Mod_mem_heaplet`, hacl-star:vale/code/arch/x64/Vale.X64.QuickCode.fst).
- **Reads after writes are SMT facts over buffer indices** (Z3 with patterns), not byte-level rewriting.

### How execution is stepped: reflective VC generation

- **Every instruction is a procedure with a pre/postcondition, proved once against the semantics** (`Vale.X64.InsBasic.vaf`, `InsMem.vaf`, `InsVector.vaf`, …). A program's proof uses these specs, never the instruction semantics.
- **Programs are deeply embedded as `codes`, each with a "quick code".** The VC is computed by a function, `wp` (hacl-star:vale/code/arch/x64/Vale.X64.QuickCodes.fsti:115-159), and it is `wp_sound` (:164-169) that connects it to the semantics. Its conclusion includes `update_state_mods mods sN s0 == sN`: the final state *is* the initial state with only the fields in the modifies list `mods` replaced. Frames hold by construction.
- **The VC is unfolded by F*'s normaliser** (`norm [iota; zeta; delta_attr [`%qmodattr]…]`, Vale.X64.QuickCode.fst, `update_state_mods_norm`), then handed to Z3. The paper says: "use the computational power of a dependent type system's type checker to run a verified verification-condition generator during type checking" (abstract).

### Numbers (published)

From the POPL'19 paper (https://www.microsoft.com/en-us/research/wp-content/uploads/2018/12/popl19-vale.pdf, text extracted with zlib from the PDF since no pdftotext is installed here):
- **Machine:** "All measurements were taken on a single core of an Intel i7-8700 processor" (§6).
- **Procedure times:** "six procedures took more than 10 seconds with Vale/F* naive, whereas all procedures took less than 10 seconds with Vale/F*" (§6.1, Fig. 9).
- **AES-GCM size:** "339 lines of specification, 2020 lines of proof libraries, 73 Vale procedures, over 1100 lines of Low* code, and more than 4400 lines of Vale code" (§5).
- **No instruction count, total time or per-instruction time is given in the text.** Fig. 9 is a scatter plot.

Today's sources, measured: `find vale/code/crypto/aes -name "*.vaf" | xargs wc -l` is 11,493 lines in 164 procedures, and all of `vale/code/**/*.vaf` is 31,992 lines.

## 3. Islaris (Coq, Iris, Isla)

### State and memory

- **Assertions are separation-logic points-to's in Iris.** `reg_mapsto` (islaris:theories/ghost_state.v:122) is a register points-to. There is a memory points-to per address range with kinds (`mem_mapsto_kind_prop`, theories/automation.v:693). `instr a (Some t)` (ghost_state.v:112) says the instruction at `a` has Isla trace `t`.
- **Reads after writes are resolved by the frame rule.** Only the resources a spec names are in context, and the automation finds them syntactically (`find_in_context_reg_mapsto`, automation.v:804).

### How execution is stepped

- **Isla runs the Sail ISA model symbolically, with an SMT solver, once per instruction, outside Coq.** It produces a trace per instruction: the reads and writes of registers and memory, with constraints.
- **Coq steps through those traces with the Lithium automation** (`liARun`, timed by islaris:generate_data.py). The proof never unfolds the ISA model.
- **The theories are 6,111 lines** (`find theories -name "*.v" | xargs wc -l`).

### Numbers (published, in the repository)

islaris:generate_data.py holds the evaluation data. Instruction counts were "counted by hand", and the Isla time was measured "by adding `time` in front of every call to islaris". The spec and proof lines below are counted here, with the same `SPEC_START`/`PROOF_START` markers the script counts (a Python re-implementation of its loop, non-blank lines):

| Case study | Instructions | Isla time (s) | Spec lines | Proof lines |
| --- | --- | --- | --- | --- |
| pkvm_handler | 47 | 37 | 159 | 219 |
| memcpy (Arm) | 8 | 6 | 20 | 51 |
| memcpy (RISC-V) | 8 | 1 | 19 | 50 |
| binary_search (Arm) | 32 | 25 | 25 | 147 |
| binary_search (RISC-V) | 48 | 5 | 25 | 106 |
| rbit | 2 | 3 | 18 | 27 |
| simple_hvc | 13 | 10 | 93 | 5 |
| uart | 14 | 10 | 36 | 42 |
| unaligned_accesses | 1 | 2 | 89 | 29 |

- **The Coq check times are not in the repository.** The script measures them (`total`, `lithium`, `Qed`), but I could not build Coq here (no opam/Coq installed), and the paper (PLDI'22) could not be fetched: the ACM DL returns 403 and the authors' page returns 404.
- **The largest example is 48 instructions.** Isla's time ranges from about 0.1 s per instruction (RISC-V binary search: 5 s for 48) to about 1.5 s (rbit: 3 s for 2).

## 4. CakeML / HOL4: decompilation into logic (brief)

Myreen, Gordon and Slind turn machine code into HOL functions with a proved translation. The decompiler steps each instruction once, through a per-instruction theorem in a separation-logic triple ("SPEC"). It composes those theorems along the control flow and turns loops into tail-recursive functions. Not studied in detail here and no numbers measured; listed because its per-instruction theorems composed along control flow are the same structure as LNSym's step theorems and Vale's instruction specs.

## 5. What they do differently from nocompiler_auto (facts, from the above)

| Cost we measured | LNSym | Vale | Islaris |
| --- | --- | --- | --- |
| Byte-level memory in goals (69% of the time) | byte memory, but reads over writes decided on whole ranges by `simp_mem` (subset/separation, then `omega`) | lifted to typed buffers (`mem64`), SMT over indices | points-to's per range, frame rule, no read-over-write rewriting |
| Goal grows from unmerged register writes (about 40k characters) | per-field map `AxEffects` with a fresh state variable per step; no write chains in the goal | VC built by `wp`, frames by `update_state_mods`; no state term grows | only the named resources are in context |
| Instruction decoded and its semantics unfolded at every step | one step theorem per address, generated once (`stepi_eq_0x…`, 52 s for 503 instructions on SHA-512); blocks too | per-instruction spec proved once, semantics never unfolded in code proofs | per-instruction Isla trace, computed outside Coq |
| 500 instructions fails | SHA-512 symbolic simulation at 400 steps: 44 s, 3.1 GB (not a whole proof: alignment goals are `sorry`) | procedures each under 10 s (largest AES-GCM procedures) | largest example 48 instructions |

## 6. Lean-specific techniques (LNSym)

- **Pre-generated step theorems, one per address,** proved by kernel reduction at generation time and cached (`reduceDecodeInst` caches decodes). The cost is paid once per program, not once per path or per proof.
- **`sym_n` adds a fresh state variable per step, with a hypothesis per changed field.** The goal stays small. The final state's fields are equalities into the initial state, assembled from `AxEffects` and turned into simp lemmas (`toSimpTheorems`, AxEffects.lean:766).
- **`withCurrHeartbeats` resets the heartbeat budget per step** (Sym.lean:241), so a long run does not hit the per-declaration limit.
- **`bv_decide` is used for the bit-vector algebra of the spec** (SHA-512 message schedule rules), with certificates stored as files and checked by `bv_check`.
- **The proof term still contains every step**, and they skip kernel checking in some benchmark variants (`set_option debug.skipKernelTC true`, the `_noKernel_noLint` benchmarks). Our audit would not accept that.

## What this implies for nocompiler (conclusions, not facts)

1. **Never unfold `exec`/`decode` inside a proof run.** Generate one step lemma per instruction address of the image, once, as `nocompiler export` already does for `instr_` lemmas. LNSym and Vale both pay instruction semantics once per instruction, not once per path.
2. **Keep the symbolic state flat: a fresh state per step (or per block) with per-register equations, not a `setReg` chain.** This is LNSym's `AxEffects` and Vale's `update_state_mods`. It removes the 40k-character goals.
3. **Reason about memory at word or range level.** Use ranges with separation/containment decided by `omega` (LNSym), or typed views proved equal to bytes once (Vale). Byte-level `readLE`/`writeLE` should not appear in goals, which is where the measured 69% goes.
4. **Prefer per-block lemmas to per-path re-execution.** This is LNSym's `blocki_eq` and A's per-segment lemmas. At 10^5 instructions, unchanged blocks (and whole functions) should be discharged by equality of their bytes and reuse of their block lemmas.
5. **Reflective VC generation (Vale) is the one way here that makes the per-instruction cost a function evaluation rather than tactic work.** In Lean that would be a verified `vcgen : Code → Spec → Prop` evaluated by the kernel or `simp` with `decide`. Its soundness is proved once.
6. **Even LNSym's measured rate is far from the scale target, and it grows with length.** It is about 110 ms per instruction at 400 steps (44 s), against the user's target of about 1 ms per instruction amortised. So a per-path symbolic simulation, even a well-engineered one, is not the scale design by itself. Unchanged code has to be discharged without re-simulation (byte equality, reused block lemmas), and the per-instruction work has to be an evaluation.
7. **None of the three has a published whole-binary result at 10^5 instructions.** The largest measured runs are LNSym's (hundreds of instructions) and Vale's (procedures of AES-GCM). The scale target is beyond all three.

## Implementation plan (C, round 2 next: the core for scale)

Files I own: `lean/NoCompiler/Fast/*`, `lean/NoCompiler/VC/*`, `lean/NoCompiler/Auto.lean`. The trusted definitions (`Machine.lean`, `Step.lean`, `Env.lean`, `Spec.lean`) are not changed. Every existing proof keeps building; when `nocompiler_auto` moves onto the new core, each example is migrated in the same commit.

**Step 1: fast representation, proved equal to the trusted one once (`Fast/`).** These are LNSym's `AxEffects` and Vale's lifted memory, in our terms.
- `FState`: a flat register file (32 words, one slot each, so no write chains), pc, memory, trace and exit. Memory is a base `Word → Byte` plus a list of word-level writes `(addr, width, value)`, newest first.
- `FState.toState : FState → State`, the abstraction function.
- Read lemmas at word/range level: a read of `n` bytes at `a` over a write of `m` bytes at `b` is the written value when the ranges are equal, and the older read when they are disjoint. Disjointness is decided by `omega` on `toNat`, as in LNSym's `simp_mem`. A frame lemma covers memory outside every write.
- `fstep : Code → FState → Option FState`, deterministic, every instruction but `ecall`.
- `fstep_sound : fstep c S = some S' → c.instr S.pc = some i ∧ exec i S.toState = some S'.toState`. This is the only bridge to the trusted semantics, proved once by cases on the instruction.

**Step 2: reflective VC generation on it (`VC/`), from A's `VC/Straight.lean` (next-a at d61cbf7).** This is Vale's `wp` in our terms. Its milestones:
1. Straight-line ALU code. Symbolic values `Sym` (denotation = the machine's `evalI`/`evalR`/…), the flat symbolic state, `run`, and `run_sound`, proved once. The kernel evaluates `run` on closed data, by `rfl`/`decide`, not tactics.
2. Loads and stores. Symbolic word-level memory, with permission and alignment obligations emitted as formulas.
3. Branches, with cut points from the block/loop tree.
4. Calls and syscalls.

**Step 3: `nocompiler_auto` on the new core (`Auto.lean`).** A segment (cut point to cut point) is closed by the generator's soundness theorem applied to its evaluated output. Only the residual formulas become goals. One lemma per segment (A's design).

**Budget, measured, not assumed.** Before moving on from milestone 1, I measure elaboration plus kernel time, and peak memory, for a straight-line ALU chain of 10^2, 10^3 and 10^4 instructions built as closed data in a Lean file under `VC/`. The target is the user's: about 1 ms per instruction amortised. LNSym's measured rate (above) is about 110 ms per instruction at 400 steps. If the reflective run is not linear, or not near the target at 10^4, I report that and stop to rethink before step 3.

### Measured: milestone 1, kernel evaluation of the symbolic run

Straight-line chain of N `addi a0, a0, 1`. Checked statement: the run succeeds, ends at the right pc, and a0 is N additions deep. Generated by `lean/NoCompiler/VC/Bench/Gen.py`, checked with `lake env lean -Dprofiler=true` under the 6 GB cap; "kernel" is the profiler's "type checking". Single runs on the shared host. An imports-only file takes 0.36 s, 0.46 GB.

| N | Lookup per pc (`run`, `Code.instr`) | Words in order (`runW`) |
| --- | --- | --- |
| 100 | kernel 0.71 s, 0.60 GB | kernel 0.44 s, 0.51 GB |
| 200 | 2.48 s, 0.89 GB | |
| 300 | 5.02 s, 1.33 GB | 1.14 s, 0.57 GB |
| 500 | 13.2 s, 2.71 GB (lookups alone: 11.6 s, 2.56 GB) | |
| 1,000 | killed at the 6 GB cap after 30.9 s (`oom-kill`) | 3.32 s, 0.79 GB |
| 3,000 | | 10.7 s, 1.40 GB (needs `maxRecDepth 200000`) |
| 10,000 | | 29.9 s, 3.58 GB (needs `maxRecDepth 200000`) |

- **Instruction lookup is the quadratic term.** `Code.instr` walks the word list on every lookup in the kernel.
- **Words in order is linear.** `runW` gets about 3 ms per instruction of kernel time at 10^3 to 10^4. That is within about 3× of the 1 ms target, not at it. Peak memory also grows: this chain makes one 10^4-deep term. Splitting per segment (step 3) bounds it.

### Measured: milestone 2, loads and stores (`VC/Mem.lean`)

N instructions alternating `ld a3, 0(a0)` and `sd a3, 8(a0)`, run by `NoCompiler.VC.M.runW` inside the code's region. Checked statement: the run succeeds, ends at the right pc, and emits 2N obligations (alignment and permission per access). The obligations are generated and counted, not yet discharged; simplifying them is the next milestone. Same setup as above (`Gen.py OUTDIR mem N`).

| N | Kernel ("type checking") | Wall | Max RSS |
| --- | --- | --- | --- |
| 100 | 0.13 s | 0.57 s | 0.49 GB |
| 1,000 | 1.37 s | 1.76 s | 0.66 GB |
| 10,000 | 16 s | 16.4 s | 2.38 GB |

That is about 1.4 to 1.6 ms per instruction. `Reach.of_runW` (trusted `Reach` from a run whose obligations hold) and `sstep_sound` use only `propext` and `Quot.sound`.

### Measured: milestone 3, obligations discharged reflectively (`VC/Ob.lean`)

The same ld/sd chain. Every obligation is checked by `Ob.check` from the facts "a0 is 8-aligned" and "a0 starts a 16-byte writable region", all in one kernel evaluation (`Gen.py OUTDIR memchk N`). `Ob.check_sound` and `Reach.of_runW_checked` (trusted `Reach` from a checked run) are proved once.

| N | Kernel ("type checking") | Wall | Max RSS |
| --- | --- | --- | --- |
| 100 | 0.28 s | 0.65 s | 0.52 GB |
| 1,000 | 3.15 s | 3.50 s | 0.89 GB |
| 10,000 | 33.1 s | 33.5 s | 4.69 GB |

That is about 3.2 ms per instruction, linear, with no goal or tactic per instruction. Memory at 10^4 is close to the 6 GB cap: one evaluation over the whole run keeps every state alive. Splitting per segment is what bounds it.

### Measured: milestone 4a, one lemma per segment (`VC/Seg.lean`)

The memchk chain of 10,000 instructions, as `Code.ofSegs` with segments of K, with one theorem per segment (`Gen.py OUTDIR seg N K`). Run back to back on the shared host (load average 4 to 6 throughout), so these are comparable with each other but noisy. Single theorems vary from 0.33 s to 1.54 s within one file.

| Form | Kernel ("type checking", whole file) | Wall | Max RSS |
| --- | --- | --- | --- |
| one run of 10,000 (`MemChk10000`) | 34 s | 34.5 s | 4.69 GB |
| 10 segments of 1,000 | 36.6 s (3.3 to 4.1 s each) | 37.0 s | 0.92 GB |
| 100 segments of 100 | 64.8 s (0.33 to 1.54 s each) | 65.9 s | 0.72 GB |

- **Segments of 1,000 keep the time and cut peak memory by about 5×.**
- **Segments of 100 cut memory further but take about 1.9× the time.** That suggests a per-theorem overhead not yet located.
- **Earlier single-run numbers on this host varied with load:** one 100-instruction segment alone measured 0.29 s at one time and 0.43 s at another.
- **Each segment's lemma (`Reach.of_seg`) reaches its words through `ofSegs_drop`,** proved once by induction, so it never walks the code before it.

### Measured: milestone 4c and the symbolic memory (`VC/Tactic.lean`, `VC/Mem.lean`)

`vc_run` leaves the segment's end state in the goal, so the successors' conditions can be stated over it. It finds the value with compiled code and has the kernel check `runSeg … = v`. Measured on one segment of 1,000 `addi` (`Gen.py OUTDIR vcrun add 1000 1000`), single runs:

| How the kernel checks `runSeg … = v` | Kernel ("type checking") |
| --- | --- |
| `rfl`, as an auxiliary theorem | 10.7 s |
| `decide` on the derived `DecidableEq`, as an auxiliary theorem | 3.48 s in the kernel, but 202 s in the elaborator (`mkAuxTheorem` checks the proof) |
| `decide`, the proof term passed straight to `rewrite` (kept) | 3.43 s |
| for comparison: the run alone, `decide +kernel` on `(runSeg …).map …` | 1.23 s |

The compiled evaluation itself takes 11 ms.

Symbolic memory:
- Before, a load's memory was the whole write chain, and a store pushed a write. On the alternating `ld a3,0(a0)` / `sd a3,8(a0)` chain, each value then contained the memory twice. The tree `toExpr` builds doubled with every pair: 20 instructions took 0.25 s of kernel time, and 40 were killed.
- Now `symLoad` reads past disjoint writes (`rdSkip`, decided on the constants of variable-plus-constant addresses) and forwards an 8-byte store to an 8-byte load. `symStore` replaces a write of the same range, moving past disjoint writes to reach it.
- These are proved from `Fast.writeLE_apply` (a write, pointwise), `writeLE_overwrite` and `writeLE_comm`.

| Run (segments of 1,000, one `vc_run` theorem each) | Kernel | Wall | Max RSS |
| --- | --- | --- | --- |
| mem 40, before `symStore` | 0.26 s | 1.38 s | 1.59 GB |
| mem 1,000, `symLoad` only | 50.5 s | 52.3 s | 7.27 GB |
| mem 1,000 | 4.16 s | 5.30 s | 2.08 GB |
| add 10,000 | 35.3 s | 36.6 s | 2.14 GB |
| mem 10,000 | 40.4 s | 42.0 s | 2.15 GB |

The 7.27 GB figure is what `/usr/bin/time` reported under the 6 GB cap. It probably counts something the cap does not.

That is 3.5 to 4.0 ms per instruction with the end state exposed, against the 1 ms target. About a third is the kernel's own run; the rest is comparing with the value.

### Milestone 5: paths between cut points (`VC/Explore.lean`) and goals in the machine's terms

- **`explore`** follows every path from a cut point to the next cut points and returns.
  - At a conditional branch it explores both successors, recording the condition (symbolic operands and outcome) as data.
  - It follows straight-line code word by word, and `jal` to its target. `jalr` goes to its target when that is a known constant, as after `auipc ra`; a call sets the link register on the way.
  - A path ends at a cut point, or at `jalr zero, 0(ra)` (a return).
  - A call is handled by listing the callee's entry as a cut point. Its condition is then discharged with the callee's `VerifiedImg.call`, never looking at the callee's code.
- **Soundness** is `Reach.of_explore`, proved once by induction on fuel. `exploreVC` states one cut point's condition: the obligations the checker cannot discharge (an array index, say), and each end's condition under its path conditions.
- **`vc_ends`** turns each end into a goal over the cut point's registers in the machine's own operations: `u.reg 10 + 8`, `read64 u.mem (u.reg 10 + 0)`. The `symDen`/`smemDen` simprocs evaluate a closed symbolic value with compiled code and replace it by its denotation, definitionally, so the kernel checks the step on the small term.
- **Example: clang's `sum` loop** (Examples/Sum/Image.lean, 9 words). It needs two cut-point conditions. The load's alignment and read permission are the only residual obligations. `sum_reach2` is about 35 lines of arithmetic about the specification. The hand-split `sum_reach` in the same file is about 85 lines.
