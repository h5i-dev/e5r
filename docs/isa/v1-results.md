# Version 1: acceptance criteria, as measured

The criteria are those of [v1.md](v1.md), "Acceptance criteria". Each entry
is filled in by whoever finishes the criterion, with what was run and what
came out, failures included. Criterion 8 decides whether the project may
claim "easier to prove".

| # | Item | Status | Result |
| --- | --- | --- | --- |
| 1 | `sum2` proof size | passed (image-level `VerifiedImg`; see below) | below |
| 2 | syscall functions through `nocompiler_auto` | passed | below |
| 3 | relocation (two links, one proof) | partial (leaf functions) | below |
| 4 | corpus conformance levels | passed | below |
| 5 | `asm(disasm(x)) = x` | passed | below |
| 6 | negative controls | checker side passed (Rust and Lean, A); audit side passed (B) | below |
| 7 | checking cost (replaced by 7') | measured; budget not met | see 7' below |
| 8 | demo A/B with calls and frames | **not met**: no difference | below |
| 9 | LLM-written structured RV64 | open | |

## 4. Corpus conformance (Rust checker)

`cargo test -p nocompiler --test corpus -- --nocapture`, with clang 15.0.7 and
ld.lld 20 on the development host (the spec's survey used clang 18.1.3). The
corpus is every C program in the repository built with `nocompiler cc`
(examples/, examples/demo/src, crates/nocompiler/tests/cc), including tests/cc/frames.c,
24 functions written for R6: saves, spills, address-taken scalars, arrays and
structs passed to callees, sret, calls in loops, eight and nine arguments, a
variable-length array.

- 58 functions, every one with a level: 54 at L2, 2 at L1, 2 at L0.
- Below L2, each with its rule: `nine_args` L1 (R6c: it reads its ninth
  argument above the entry `sp`), `vla` L1 (R5: `sp` written by `sub`),
  `apply` L0 (R2: a call through a function pointer), `call_in_loop` L0 (R3:
  clang 15 rotates this loop into a forward jump into it despite
  `-disable-block-placement`; a clang shape, not a frame question).
- Functions with a frame: 22, of which 21 at L2; the one that is not is `vla`.
- Range lengths: on frames.c the heuristic and DWARF (`-gdwarf-4` and
  `-gdwarf-5`) give the same 10 ranges; with `-g` every range reports DWARF as
  its source, without it the heuristic.

The test asserts all of this except `call_in_loop`, whose level depends on the
clang version.

In Lean: the committed images (examples/elf/{sum,hello}.elf,
examples/demo/elf/{sum,cobs}.b.elf) state `<name>_checked : Struct.level ... = some .l2`
for all 11 of their functions, proved by `decide` against the certificate
`nocompiler export` writes (lean/NoCompiler/Frame.lean). The corpus beyond the
committed images is checked in Rust only.

## 6. Negative controls, checker side

`cargo test -p nocompiler --test levels`: mutations of `sum2` in
examples/elf/sum.elf, checked both against the partition as recorded and with
the partition inferred again from the mutant. Each is below L2 and names the
fault.

| Mutation | Level | Rule |
| --- | --- | --- |
| `ld s0, 16(sp)` replaced by a nop (a restore removed) | L1 | R6e: returns without the entry value of s0 |
| `mv s2, a0` replaced by `sd a0, 16(sp)` (a save slot written mid-function) | L1 | R6e: writes the save slot of s0 with a0 (declared); R6e (inferred) |
| `mv a0, s1` replaced by `addi a0, sp, 16` (a slot's address taken) | L1 | R6d: takes the address of the slot at 16 (declared); R6 (inferred) |
| call distance changed by 4 bytes | L0 | R2: the call no longer reaches an entry |
| `mv s0, a3` replaced by a write to `gp` | L1 | R4 |
| `sd sp, 0(a0)` (sp stored) | L1 | R6a |
| `ld ra, 40(sp)` (past the entry sp) | L1 | R6c |
| a declared partition missing s0's save slot | L1 | R6 |

lean/Examples/FrameControls.lean makes the same faults (and an unbalanced
`addi sp, sp, 16`) in `sum2`'s words and has the kernel refute L2 for each
against the recorded frame and certificate, with no help from Rust; the
unmutated code keeps L2.

tests/profile.rs `each_rule_is_enforced` adds the rules on small assembly
functions: `sp` in arithmetic or stored (R6a), a stack argument (R6c), half a
slot read with `lw` (R6c), a save without a restore and a write without a
save (R6e), and a saved-and-restored register (L2).
## 3. Relocation (agent B, 2026-11-20)

**Done for leaf functions; open for functions with calls.**

* One object, `examples/sum.c` compiled once with `-ffunction-sections`, is
  linked twice (`examples/link/build.sh`): `examples/elf/sum.link1.elf`
  (`.text` at 0x11190, order sum, sum2, _start) and `sum.link2.elf` (`.text` at
  0x40000, order _start, sum2, sum). `nocompiler module` recovers the
  relocatable module of each (words with relocated fields zero; `call`,
  `pcrelHi`, `pcrelLoI` relocations); the two are equal
  (`Examples.Link.same_module`, by kernel evaluation).
* `Examples.Link.sum_relocatable : Verified One.module "sum" Examples.Sum.spec`,
  over every layout. It is not a new proof: `Verified.of_leaf`
  (`lean/NoCompiler/Relocate.lean`) carries `Examples.Sum.sum_verified`, the
  existing proof about `examples/elf/sum.elf`, to every layout, through the
  translation theorem `VerifiedImg.shift` (`lean/NoCompiler/Shift.lean`): code
  with no relocations whose instructions neither read nor write `ra` (other
  than the return) and contain no `auipc` runs the same anywhere. `sum_link1`
  and `sum_link2` are that one theorem at the two layouts; the proof text is
  the same.
* `nocompiler-audit` reads each ELF's layout from its symbol table, checks
  `Module.Ok` there, and that the module linked there is the ELF's `.text` and
  data byte for byte: both pass. This checks `link` (calls and data addresses
  included: `sum2` and `_start` have relocated words) on both binaries.
* All axioms standard (`lean/Audit.lean`).

* T6 (`Verified.mono`, `lean/NoCompiler/Relocate.lean`): a theorem about a
  module holds in any module that extends it; `Examples.Link.sum_in_any_program`
  uses it. The ledger entry format is `docs/isa/ledger.md`
  (`nocompiler ledger`; `examples/link/ledger.jsonl`, the same for both links).

**With calls (`sum2`), at both links, the same proof text.**
`lean/Examples/LinkCalls.lean` proves `sum2` (two calls to `sum`, a 32-byte
frame) at each link with one proof block, identical in both and naming no
address (`crates/nocompiler/tests/module.rs` checks it), elaborated against
each link's image (`nocompiler export`, audited against the ELF), with `sum`
at that link taken from `sum_relocatable`. Both pass the audit.

**What this is not:** a single theorem `Verified M "sum2" spec2` over every
layout. For `sum` that theorem exists, by translation. For a function with
calls a translation argument does not apply: its call words change with the
callee's distance, the callee moves independently of it, and the return
address it saves in its frame differs between layouts. A single theorem needs
the call distance and the patched `auipc`/`jalr` reasoned about at a symbolic
layout (by the tactic, or a code-pointer-aware simulation). Open. Functions
that read data (`hello`) need a specification that names the layout; also open.

## 6. Negative controls, audit side (agent B, 2026-11-20)

`scripts/core/check-audit-controls.sh` patches a copy of a relinked binary and
requires the audit to fail for the stated reason; then the unpatched copy
must pass. All pass:

| mutation | the audit says |
| --- | --- |
| sum2's first call lands 4 bytes past sum (link2) | the module linked at the ELF's layout is not its .text |
| the same, on link1 | the same |
| _start's data address is a page off | the same |
| the symbol table moves sum by 4 | the layout is not the ELF's |
| a byte of .data changes | the module's data at the ELF's layout is not its data sections |

## 1 and 2. Calls, syscalls and frames through `nocompiler_auto`

`nocompiler_auto` (lean/NoCompiler/Auto.lean) now takes calls through the
callees' theorems (`calls [...]`), every syscall outcome, and the frame. Lines
of the proof (from `theorem` to its end, nonblank), before and after, with
the specifications unchanged:

| Proof | Before (by hand) | After (`nocompiler_auto`) | Written by hand after |
| --- | --- | --- | --- |
| `sum2_verified` (2 calls, 32-byte frame, 4 saves) | 193 | 5 | that the two sums commute |
| `write_all_verified` (syscall in a loop) | 84 | 16 | the loop invariant, its witnesses, the two outcomes |
| `hello_verified` (frame, call, exit syscall) | 102 | 18 | the message bytes in `.rodata`, the exit status |

Whole files: lean/Examples/Sum2.lean 254 to 71 lines, Hello.lean 275 to 128.
For comparison, `sum`'s automated proof on the demo (lean/Demo/SumB.lean) is
12 lines. None of the new proofs states register preservation, the frame's
saves and restores, or the stack's separation from the arrays (the
specifications still carry it as a precondition; moving it into `Entry` is
step 3's).

The proofs are at the image level (`VerifiedImg code dom entry spec`); the
module-level `Verified M f spec` of step 3 is B's.

## 5. Round trip (agent B, 2026-11-20)

`cargo test -p nocompiler --test text -- --nocapture` (clang 15.0.7, ld.lld
20 on the development host). For every function at L1 or above, the object
`nocompiler asm` makes from the text `nocompiler disasm` prints holds the same
relocatable function (words with the relocated fields zero, and the
relocations) as the binary, with the same tree, level, frame and partition:

- the committed binaries (examples/elf/{sum,hello,sum.link1,sum.link2}.elf,
  examples/demo/elf/{sum,cobs}.b.elf): 17 functions, all of them;
- the C corpus built with `nocompiler cc` (tests/cc/{frames,fnptr,loops,recur,
  structs,switch}.c, hello, cobs): 53 functions at L1 or above. Not in the
  text, being below L1: `apply` (fnptr.c, a call through a function pointer)
  and `call_in_loop` (frames.c, clang 15 rotates its loop; R3).

Byte for byte: for every program all of whose functions are at L1 or above
(the committed six, and loops, recur, structs, switch, hello, cobs), the
object linked again by ld.lld at the binary's section addresses and function
order gives the binary's `.text` and data sections exactly, and checks against
the `.nocompiler.struct` the object carried. Format: docs/isa/asm.md.

## 8. Demo A/B with calls and frames: not met

`sum2` (examples/demo/src/sum.c: two calls to `sum`, a 32-byte frame with
four saves) proved on both builds of the demo, with the same automation on
both sides: `nocompiler_auto` on B (`nocompiler cc -O2`, the profile) and
`nocompiler_auto_c` on A (plain `clang -O2 -march=rv64gc`, compressed code),
both now with calls, syscalls and frames (lean/Demo/Sum2B.lean,
lean/Demo/Sum2A.lean). Counted by examples/demo/tools/count.py:

| function | side | invariants | script | per-function lemmas |
| --- | --- | --- | --- | --- |
| sum2 | B (profile) | 0 | 4 lines, 60 tokens | 0 |
| sum2 | A (rv64gc) | 0 | 4 lines, 61 tokens | 1 line, 19 tokens |

The one extra line on A is the code region of `sum2` and its callee, which
`nocompiler export` writes for B from the metadata and the ordinary build
has no metadata for. Otherwise the proofs are the same text: what is left
after the tactic, on both sides, is that the two sums commute. The leaf
functions were already equal (sum 12 = 12 lines, cobs_decode 94 = 94).

So criterion 8 is **not met**: with equal automation, calls and frames do
not make the profile's proofs shorter either. The project does not claim
"easier to prove" on proof length. What the profile buys on these functions
is elsewhere: the checker's level and theorems (R4 to R6, T1), the frame and
callee region coming from the metadata, and the audit; on A the same
automation needed a weaker entry condition (`EntryC`: compressed code returns
to 2-aligned addresses).

Mutation controls: scripts/core/check-proof-controls.sh adds `add` becomes
`sub` and "restores s0 from the wrong slot" for `sum2` on both builds.

## 7'. Scale (replaces the 55/160/500 targets): a real rustc-built artifact

Measured 2026-11-21 on the development host (after a reboot, otherwise idle),
`nocompiler` release build, Lean 4.35.0. Artifact: examples/refine/targets
(B's pipeline, docs/isa/refine-targets.md: cobs, memchr, httparse, bytecount,
crc32fast, base64, compiler_builtins' mem, core), one ELF.

```bash
examples/refine/conformance.sh                                     # builds it
scripts/core/bench-scale-build.sh CRATE_DIR OUT.elf                # the same, paths remapped
python3 -I scripts/core/bench-scale.py A.elf B.elf --json OUT      # check, bytes, refine
python3 -I scripts/core/bench-gate.py                              # per-instruction proof cost (CI)
python3 -I scripts/core/bench-prove.py IMAGE.lean OUTDIR           # 7'(b): level check and proofs per function
python3 -I scripts/core/bench-chunk-checks.py A.elf OUTDIR --json OUT  # level check of every function, chunk image
```

| Measurement | Result |
| --- | --- |
| Size | 87242 instructions (`.text` 0x55328 bytes), 1235 functions: L2 673, L1 12, L0 527, not decoding 23 |
| Rust checker (`nocompiler check --json`, all functions) | 0.091 to 0.18 s, i.e. 1.0 to 2.1 µs per instruction |
| Lean checker / Lean image of the whole binary | **does not elaborate**: since d5e6a0b `nocompiler export` writes it (14.3 MB), but `def code`, one 87242-word array literal, and `seg_rodata` hit the heartbeat limit (78.9 s, 2.6 GB peak). Before d5e6a0b the exporter refused the binary. Smaller evidence: a 500-instruction image alone takes 140 s and 5.2 GB (one `instr_` lemma per instruction over one array of all of `.text`: quadratic) |
| Whole-binary Lean image, `nocompiler export --format chunks` (Image.lean "Code in chunks": one number literal per symbol's code and per data segment, certificates as runs, no lemma per instruction), capped at 6 GB, single runs, `-j1` | Export 0.26 s; 1.45 MB of Lean (array format: 14.3 MB). `.text` alone (1235 chunks, `Code.ofChunks`, `Chunk.contig` and the bound by `decide +kernel`): 23837 / 43779 / 87242 words: elaboration 0.57 / 1.09 / 2.34 s, kernel 55 / 111 / 241 ms, peak 1618 / 1650 / 1725 MB against 1573 MB for `import NoCompiler` alone: linear. With data segments and the 229 exported functions' definitions: 23.2 s, 2.14 GB. Plus the 229 `<f>_chunk` lemmas (the image is the chunk's code on its range): 39.4 s, 2.50 GB. Plus the 229 `<f>_checked` level checks: 146.4 s, 3.36 GB, of which kernel 111 s: the checker's cost (about 20 ms per instruction over 5132 instructions), not the format's. Before (array format): does not elaborate. The literals were the cost: 87242 `#32` literals 65.6 s / 3.3 GB, as `Nat` 37.6 s, as one number per chunk 4.6 s |
| Lean level check (`<f>_checked`, `Struct.level` by `decide +kernel` on the function's own chunk) over ALL L1+ functions of the artifact (685: 673 L2, 12 L1; 24882 instructions), `scripts/core/bench-chunk-checks.py`, capped at 6 GB, single run, host load 3-10 (shared) | The chunk format now checks every function that passed the profile check (before: only the 229 whose callees all passed; `_dom` still needs those). One module with all 685 checks: OOM-killed at the cap after 312 declarations (memory grows from one check to the next in a module). Split: the image compiled once (90.1 s, peak 3.17 GB), the checks in 27 modules of about 1000 instructions importing it. **684 of 685 pass**; checks wall 1029.9 s in total (41.4 ms per instruction), kernel 958 s (38.5 ms per instruction), peak per module 1.8-6.8 GB (max RSS, which counts the mapped .olean files; none of the 26 that passed was killed). Cost per instruction grows with function size: modules of functions averaging 11-58 instructions 16-34 ms/instr kernel at about 2 GB; averaging 85-311 instructions 46-129 ms/instr at 3-6.8 GB. **The failure:** `compiler_builtins::math::libm_math::tgamma::tgamma` (1046 instructions), alone in its module: OOM-killed at the 6 GB cap after 30.8 s (journalctl: "Failed with result 'oom-kill'"). The level checker's kernel evaluation does not fit one function of that size in 6 GB. The 12 largest functions, each alone (`--largest 12`, load 10-11): 236 / 261 / 279 / 281 / 333 / 338 / 390 / 393 / 400 / 438 / 484 instructions: peak 3.38 / 3.50 / 3.62 / 3.76 / 4.50 / 4.52 / 5.51 / 5.49 / 5.63 / 5.72 / 6.85 GB, kernel 17.2 / 31.5 / 25.1 / 42.5 / 74.9 / 82.6 / 54.2 / 93.0 / 76.0 / 55.1 / 90.0 s; tgamma (1046) killed again (117.4 s). Memory grows with the function's size, about 7.5-11 MB per instruction over the 1.6 GB of the imports: one function of about 500 instructions is the limit under the cap with this checker |
| Where the Lean level check's cost goes (`scripts/core/bench-level-parts.py`): each part alone, `decide +kernel` on the function's chunk, one module each, capped, load 6-10 | Kernel ms (peak MB) at 50 / 100 / 193 / 400 instructions: decode pass (every word decodes) 281 (1596) / 773 (1666) / 2400 (1893) / 10400 (2909); `Struct.check` 414 / 933 / 7740 / 23900 (4253); `checkL2` 1010 / 2370 / 6390 / 22100 (4370); whole `level` 1130 / 2460 / 11100 / 36200 (5648). Doubling the size multiplies the decode pass by 2.8 / 3.1 / 4.3: **quadratic**, and the decode pass alone has it, with no certificate and no `entries`: the cause is `c.instr` itself, an `Array` index the kernel reduces as a walk down the list under it (O(i) at instruction i), and every part calls it per pc (`check`, `checkL2` several times). tgamma (1046): every part alone, the decode pass too, OOM-killed at the 6 GB cap (38-100 s). Since 13:55 the Lean check is opt-in (`nocompiler export --lean-level-check`; default: the Rust checker's level as the statement `<f>_level`, a hypothesis) |
| The level check through `Struct.levelFast` (Frame.lean: the function's words decoded once into a Braun tree, the certificate in another; `levelFast_eq : levelFast = level`, so `<f>_checked` keeps its statement and is `level_of_fast (by decide +kernel)`), capped, load 5-14 | One function each (kernel ms / peak MB, current `level` vs fast): 50 instructions 1130 / 1670 vs 949 / 1650; 100: 2940 / 1854 vs 1860 / 1732; 193: 14900 / 2826 vs 10200 / 2276; 400: 55700 / 5562 vs 20100 / 3221; tgamma (1046): OOM-killed vs **44400 / 5410, passes**. Whole artifact (27 modules, the 11:00 run's partition): **685 of 685 pass**; kernel 1028.9 s (41.4 ms per instruction) at load 11-13, max peak 5.27 GB (before: 684 of 685, 958 s at load 3-10, max 6.99 GB). Peak memory is lower in every module (up to about half); kernel time is about the same for small functions (Checks13, 28 functions of 2-114 instructions, back to back: 29.7 s current vs 31.0 s fast at load 5.5, 48.2 vs 37.2 at load 10) and 2-3x lower for large ones. What remains per instruction is `check` (cbrtf, 114 instructions: 2.87 s of its 4.29 s; the tree costs 40 ms, the fast decode pass 417 ms) |
| `levelFast` with the entries by binary search (`entriesFast`, 8ebf3d9: one walk of the 1235-element entries list costs the kernel 180-220 ms, paid before at every call target; `entriesFast_eq : = entries.contains`), capped | One function each (kernel ms / peak MB, `level` vs fast): cbrtf (114) 6640 / 2148 vs 3180 / 1833; 50 instructions 1040 vs 1310 (the tree's cost); 400: 55900 / 5176 vs 8650 / 2255; tgamma (1046): OOM-killed vs 18400 / 3180. Whole artifact (15:21-15:41 UTC, load 5-13): **685 of 685 pass**, kernel 953 s (38.3 ms per instruction), max peak **3.17 GB** (the first run, 11:00, load 3-10: 684 of 685, 958 s without tgamma, max 6.99 GB); on the modules both runs passed, 868 s then vs 644 s now, up to Checks22 |
| Proof cost per instruction, current machinery (`nocompiler_auto`, fixed proofs, bench-gate.py) | SumB 344 ms total / 48 ms kernel per instruction (9 instrs); CobsB 825 / 84 (55); Sum2B 365 / 19 (21); Hello 259 / 25 (27). Target: ≤ about 1 ms. No proofs of the rustc functions exist yet. **The gate is now on chunk images** (Examples/Chunks/{SumB,CobsB,Sum2B,Hello}.lean: the same proofs, the instructions from the simproc `ImageSimp.chunkInstr` instead of a lemma per instruction), on next after 2e8455c (nocompiler_auto's explore path), host load 7-9, the budget's run: SumB 627 / 128, CobsB 980 / 171, Sum2B 739 / 41, Hello 567 / 60; the check run after it 578 / 112, 968 / 178, 646 / 36, 492 / 50. Before 2e8455c, load 4-5: 308 / 38, 992 / 133, 527 / 23, 311 / 32 (single runs on the shared host vary by up to about 2x; SumB's kernel time rose with 2e8455c in both formats: 1.0-1.3 s on the array and the chunk image alike, three runs each). Adding the simproc to `nocompiler_image` leaves the array-image proofs unchanged: the .olean files of Demo/SumB, Demo/CobsB, Demo/Sum2B and Examples/Hello are byte-identical with and without it |
| Reflective VC generator (C's milestone 3, lean/NoCompiler/VC/Bench/Gen.py `memchk`: alternating ld/sd, every obligation discharged by `Ob.check`), kernel time, capped at 6 GB, measured by A | N=100: 0.27 s kernel, 0.57 s wall, 0.52 GB; N=1000: 3.04 s, 3.34 s, 0.89 GB; N=10000: 32.4 s, 32.7 s, 4.69 GB. Linear in time, about 3 ms per instruction (target ≤ 1 ms: not met); memory about 0.42 MB per instruction above a 0.5 GB base, so 10^5 instructions in one declaration would not fit the cap. In the CI gate as `VC/MemChk1000` |
| 7'(b): Lean on the artifact's own functions (scripts/core/bench-prove.py, per-function slices of the export, capped at 6 GB; cost = a variant minus the slice alone, per instruction of the function; single runs, so small functions can come out negative) | `nocompiler export` (d5e6a0b): 229 of 685 L1+ functions; 36 skipped, their code region spans > 2048 words of `.text` (callee far away: `code` is one array). **Level check in the kernel** (`_checked`, `decide`): 193 of 193 pass; 5132 instructions; kernel median 15.7 ms/instr (7.6 to 83.9), sum 116.8 s; total (elaboration included) median 33.9 ms/instr, sum 255.9 s. **Proof** (`nocompiler_auto`, `VerifiedImg` at the safety-only spec: any entry, returns preserving the ABI, touches only its frame) on the 47 functions the tactic takes as it stands (no callees, blocks, loops or ecall; memory only through sp): 47 of 47 proved; 494 instructions, largest `__ctzdi2` (36); kernel median 3.65 ms/instr, sum 1.8 s; total median 114.8 ms/instr, sum 72.1 s. Target ≤ about 1 ms: not met; elaboration (the tactic), not the kernel, dominates |
| Identical rebuild: bytes | same directory: the ELF is byte-identical. Another directory: NOT identical (the build path is in 16 panic-location strings, so `.rodata` and everything after move); with `--remap-path-prefix` (bench-scale-build.sh): identical. Comparing every function's bytes: 0.0034 s for 2906 symbols |
| Identical rebuild: `nocompiler refine` (Rust tree diff + certificate), every L1+ function | 685 functions, 25040 instructions, 142.8 s (0.21 s per function, 5.7 ms per instruction): a per-call cost, the tool reloads the binary every time; nothing changed. Lean proofs of these refinements: not run (no images, above) |
| One small edit (`w_num_chars` returns `+ 1`): bytes | 531 of 2906 symbols change, 191 of the 685 L1+ functions: one function grows, everything after it moves, and every pc-relative `auipc`/call offset that crosses it changes. Byte equality of LINKED functions does not find unchanged code; it has to be on relocatable bytes with relocations masked (the ledger, `RFunc`) |
| One small edit: `nocompiler refine` on the 191 changed functions | 33.1 s; 17 refused ("a call or jump out of the function inside a change": a callee moved); 170 with changed intervals; 70 with a region whose registers differ (data addresses moved: a real difference at the level of the linked binary) |

Conclusions, as measured: the Rust side already meets the per-instruction
budget for checking; the proof side is 2 to 3 orders of magnitude over it
(C's fast representation and VC generator are what this gate will measure);
the Lean image format and the exporter's code regions do not scale to a whole
binary; unchanged-code reuse must key on relocatable bytes, not on the linked
image.
