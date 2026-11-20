# Demo: the same C, the same specification, two binaries

**Question.** For one C source and one property, how much shorter is the
proof about the nocompiler-format binary than the proof about an ordinary binary?

**Answer, for these two functions: it is not shorter.** With the same
automation on both sides, the per-function proofs about the ordinary binary
are the same size as the ones about the nocompiler binary (tables below). What the
nocompiler format changes is not the length of the proof but what it rests on: on
the nocompiler side the cut points come from a block/loop tree the kernel has
checked, the semantics is the profile's (no compressed-code extension in the
trusted base), and the adequacy theorems connect the result to the machine.
On the ordinary side a person read the cut points off the control-flow
graph, and an extension of the semantics had to be written, trusted and
tested.

```bash
examples/demo/run.sh     # build both, check, test, export, prove, audit, count
```

## What is compared

One source per function, compiled twice (`examples/demo/build.sh`):

| | compiler | binary |
| --- | --- | --- |
| **A**, ordinary | `clang -O2 --target=riscv64-unknown-elf -march=rv64gc` (+ `-ffreestanding -nostdlib`, static link), default layout: compressed instructions, clang's block placement | `examples/demo/elf/{sum,cobs}.a.elf` |
| **B**, nocompiler | `nocompiler cc -O2` (RV64IM+Zba+Zbb, no C, `-disable-block-placement`, checked, `.nocompiler.struct`) | `examples/demo/elf/{sum,cobs}.b.elf` |

Functions:

* `sum` (`examples/demo/src/sum.c`, the source of `examples/sum.c`): the sum of an
  array of words.
* `cobs_decode` (`examples/demo/src/cobs.c`): in-place COBS decoding, with the
  contract of the Rust `cobs` crate's `decode_in_place_report`. It returns
  `tag 1, a 0` for an empty buffer; `tag 1, a 1, b` = the bytes decoded before
  the bad block, for an invalid frame; and `tag 0, a` = the source bytes used,
  `b` = the bytes decoded, on success. The C was written so that `nocompiler cc`
  gives a conforming binary: the copy loop is `while (src < end)`, because
  with `for (i = 1; i < code; i++)` clang places the copy loop after the exit
  and jumps into the middle of the outer loop (R3). That rewrite is the only
  concession to B, and A is built from the same rewritten source.

Both builds of `cobs_decode` are tested under qemu-riscv64 against an
independent Python decoder: 20,000 buffers (valid, corrupted, random) and
2,000 encode/decode round trips (`examples/demo/test/cobs_test.py`). The bytes tested
are checked to be the bytes proved.

### The property (shared, `lean/Demo/{Sum,Cobs}Spec.lean`)

One `Spec` per function, used unchanged by both theorems:

```lean
theorem sum_b  : VerifiedImg  ImageB.code sum_dom sum_entry spec                       -- Demo/SumB.lean
theorem sum_a  : VerifiedC ImageA.code sum_dom sum_entry spec                       -- Demo/SumA.lean
theorem cobs_b : VerifiedImg  ImageB.code cobs_decode_dom cobs_decode_entry spec       -- Demo/CobsB.lean
theorem cobs_a : VerifiedC ImageA.code cobs_decode_dom cobs_decode_entry spec       -- Demo/CobsA.lean
```

For COBS, `spec.post` says that the three result words and the whole buffer
afterwards are those of `report orig`. That is defined from `decodeFrame`,
COBS decoding as a function on lists, not a transliteration of either
binary. `writes` is the buffer and the 24-byte result slot, nothing else:
there are no other reads, and no stack. `pre` requires `len < 2^63`, an
8-aligned slot, and slot and buffer disjoint. `VerifiedImg`/`VerifiedC` add
the rest: memory safety (every access inside the regions, aligned), the
calling convention (sp, gp, tp, s0–s11 preserved, return to ra), and
termination. Memory outside the regions is unchanged (`VerifiedImg.frame`).

## Proof sizes (`examples/demo/tools/count.py`; code lines and tokens, no comments or blank lines)

Per function:

| function | side | invariants + measures | proof script (call, verification conditions) | total |
| --- | --- | --- | --- | --- |
| sum | B | 4 lines, 72 tokens | 8 lines, 96 tokens | **12 lines, 168 tokens** |
| sum | A | 4 lines, 72 tokens | 8 lines, 87 tokens | **12 lines, 159 tokens** |
| cobs_decode | B | 22 lines, 388 tokens | 73 lines, 1024 tokens | **95 lines, 1412 tokens** |
| cobs_decode | A | 22 lines, 388 tokens | 73 lines, 1025 tokens | **95 lines, 1413 tokens** |

For reference, the hand proof of the same `sum` in `lean/Examples/Sum.lean`,
written with the step tactics only, is 114 code lines (1445 tokens).

Shared by A and B, counted once:

| | lines | tokens |
| --- | --- | --- |
| `SumSpec.lean`: specification | 12 | 110 |
| `SumSpec.lean`: lemmas about `sumW` | 13 | 205 |
| `CobsSpec.lean`: specification (`decodeFrame`, `report`, `spec`) | 38 | 465 |
| `CobsSpec.lean`: lemmas about it (blocks, frame length, list facts) | 132 | 1899 |

Libraries (reported separately; not per function):

| | lines | tokens | used by |
| --- | --- | --- | --- |
| core `lean/NoCompiler` (semantics, logic, adequacy, Struct, step tactics) | 1690 | 22666 | A and B |
| `lean/NoCompiler/Auto.lean`: the symbolic executor, word normal form, memory lemmas, `nocompiler_auto` | 897 | 12074 | A and B (the tree-driven front end: B only) |
| `lean/NoCompiler/Ext/Rvc.lean`: compressed-code extension, `nocompiler_auto_c` | 200 | 3058 | A only |

(`count.py --markdown` prints these tables; `examples/demo/run.sh` prints them at the end.)

**Lean check time** (wall clock per file as `examples/demo/run.sh` measures it,
dependencies built, 1.4 s of each is loading the imports; a shared machine,
so ±15%): `SumB` 3.2 s, `SumA` 3.6 s, `CobsB` 27.8 s, `CobsA` 31.8 s.
A full `lake build` of the repository is about 75 s, and `examples/demo/run.sh` about
3 minutes. Peak memory is about 1.7 GB per file, 1.5 GB of it the imports.

## How a proof goes, on both sides

Each proof is `rintro`, one call, and the verification conditions:

```lean
theorem cobs_b : VerifiedImg code cobs_decode_dom cobs_decode_entry spec := by
  rintro ⟨r, buf, orig⟩ s he ⟨ha0, ha1, ha2, hlen, hmem, hal, hdis⟩
  have hfl := frameLen_le orig
  nocompiler_auto cobs_decode_func s he                   -- A: nocompiler_auto_c cobs_decode_entry cobs_decode_size s he
    loop_inv 0x11198 (fun u => ∃ k, ...) measure (fun u => ...)    -- scan for the zero
    loop_inv 0x111cc (fun u => ∃ src dst L, ...) measure (...)      -- decode loop
    loop_inv 0x11208 (fun u => ∃ p cnt dst L c e, ...) measure (...) -- copy loop
  case «0x111cc_to_0x111cc_1» => ...                 -- 35 verification conditions
  ...
```

The tactic (`lean/NoCompiler/Auto.lean`) runs symbolically from the entry and from
each cut point to the next cut point or the return:
* **every step:** the instruction from the image, pc in the code, the
  permission from the spec's regions, the alignment, the branch split
  (infeasible branches pruned by `omega`);
* **every end:** `Same` (registers the function never writes keep their
  entry values) and hence `Preserved`, return to ra, and the measure.

What is left is the invariant or the postcondition of the state reached. It
comes in a normal form: each word is `BitVec.ofNat 64 e` or
`base + BitVec.ofNat 64 e`, and the buffer is a list. Ghost witnesses are
found by unification. These are facts about natural numbers and lists, and
the 35 COBS conditions are closed with the lemmas of `CobsSpec.lean`. The
conditions on A and B have the same shapes; the A proof text is the B text
with the case names (which carry addresses) renamed.

A and B share everything here except where the run stops:

* **B (`nocompiler_auto f`)**: the cut points are the loop heads of the function's
  block/loop tree `f : Struct.Func` (exported by `nocompiler export`; the kernel
  checks it against the code, `cobs_decode_checked`). The front end refuses
  an invariant at an address that is not a loop head, and requires one at
  every loop head. By R3 every cycle passes through a loop head, so every run
  is finite.
* **A (`nocompiler_auto_c entry size`)**: there is no tree. The cut points are the
  ones the proof gives, read off `llvm-objdump` by hand: `0x11194` (scan),
  `0x111b8` (the decode loop, which clang rotated so that its entry jumps
  past its exit test at `0x111b4` into the middle), and `0x111d8` (copy).
  Nothing checks before the run that they cut every cycle; a set that does
  not makes a run go round a loop until its step bound, and fail.

## What A needed that B did not

* **A semantics for compressed code** (`lean/NoCompiler/Ext/Rvc.lean`, an
  extension, clearly marked, imported only by the A proofs):
  * `decodeC` expands each RVC instruction into the existing `Instr`;
  * `CCode` is an image of halfwords, fetched on 2-byte boundaries;
  * `execC n` is `exec` with the next pc and the link at `pc + n` and
    2-byte jump alignment;
  * `StepC`/`ReachC`/`ExecC`/`VerifiedC` are copies of the core ones with the
    same `Spec`, `Entry`, `Perm` and `Done`, and the rules the proofs use are
    proved again.

  **Added to the trusted base, for A only:** `decodeC`, `CCode.instr`,
  `execC`, and the four definitions. **Checked:**
  * `decodeC` agrees with llvm-mc on every one of the 49,152 16-bit words
    (`examples/demo/test/rvc_decode.py`). The only deliberate difference: llvm-mc
    decodes the reserved `c.lui rd, 0` and `decodeC` rejects it (the
    conservative side).
  * The compressed `cobs_decode` run in the extension's semantics
    (`lean/RvcRun.lean`) matches qemu byte for byte on 3,000 buffers
    (`examples/demo/test/rvc_exec.py`; `run.sh` runs 500).

  **Not done:** the adequacy theorems of `NoCompiler/Adequacy.lean` (`VerifiedImg.hw`:
  what the theorem means for the machine that fetches from memory) for
  `StepC`. So A's theorem is about the proof relation over the image, not yet
  about the machine. And the extension is tested against qemu only on the
  instructions this function uses, not on random programs as the core is.
* **A new exporter** (`examples/demo/tools/ExportC.lean`; untrusted: every `instr_`
  lemma is proved by `rfl`, and `nocompiler-audit` compares the halfwords with the
  ELF).
* **Cut points chosen by hand** from the CFG, including one in the middle of
  a rotated loop (above).
* **What B has and A lacks:** a kernel-checked structure theorem
  (`Struct.cfi`: every transfer is structured).

Not needed on either side: there are no jump tables, calls or stack frames
in these functions. clang's rotated loop on A cost nothing extra once the cut
point was chosen.

## Why the difference is small here, and where it would not be

The proof effort is in the invariants and the verification conditions. The
invariants are the same on both sides: the same algorithm keeps the same
facts at its loops, in different registers. The conditions are facts about
COBS, not about the code. Everything that depends on the code (stepping,
permissions, alignment, the frame) is automatic on both sides, because the
symbolic executor needs only cut points. A has cut points too, once someone
chooses them. So for leaf functions with a few reducible loops, the nocompiler
format buys correctness of the cut-point choice and a smaller trusted base,
not a shorter proof.

The format should matter more where this demo does not go:
* **Irreducible control flow, computed jumps, jump tables:** clang emitted
  none here. A jump table would need reasoning about a computed target on A;
  B rejects it.
* **Many functions:** choosing and justifying cut points by hand scales
  badly; B reads them from the checked tree.
* **Adequacy:** B's result already reaches the machine (`VerifiedImg.hw`); A's
  needs `Adequacy.lean` redone for compressed fetch.

## The comparison is imperfect in these ways

* **Different code.** A `cobs_decode` is 57 instructions in 162 bytes, B is
  55 in 220. `sum` is 9 and 9 instructions (18 and 36 bytes). The register
  assignment and loop layout differ: A rotates the decode loop, and B keeps it
  structured, because `nocompiler cc` passes `-mllvm -disable-block-placement`.
* **The source was shaped once for B** (the copy loop, above); A uses the
  same source.
* **Trust differs** as described: A adds the RVC extension and lacks
  adequacy. The specification, the logic (`Reach` and its rules) and the
  automation are the same.
* **The automation was developed on B** and then run on A unchanged apart
  from the flavour of the step relation. A tool designed for A from the start
  (CFG recovery, automatic cut points) would not change the per-function
  counts here, since the cut points are three addresses.
* **Line counts** depend on formatting; tokens are the steadier measure.
  Both are of the same style on both sides.

## Trust and checks, both sides

* No `sorry`. Only the standard axioms (propext, Classical.choice,
  Quot.sound). No `native_decide`. `lean/Audit.lean` asserts this for all four
  theorems and fails the build otherwise.
* `lake exe nocompiler-audit` re-reads the four ELF files and checks that their
  `.text` (and, for B, the data sections) are the images the proofs use.
* **Negative controls** (`scripts/core/check-proof-controls.sh`): mutations of
  both binaries, which must each make the proof fail:
  * `sum`: add becomes sub, stride 8 becomes 4, on A and B;
  * COBS: the copy starts one byte late, the success tag is a register
    instead of 0, a separator decodes as nonzero, on A and B.
* `examples/demo/run.sh` rebuilds both binaries, compares them with the committed
  ones, checks B against the profile, and runs the qemu and llvm-mc tests.
  It also re-exports the images (they must equal the committed ones), checks
  the four proofs with timings, runs the audit, and prints the counts.

## Files

| | |
| --- | --- |
| `examples/demo/src/` | `sum.c`, `cobs.c`, the entry points and the test driver |
| `examples/demo/build.sh`, `examples/demo/elf/` | the two builds; the committed binaries |
| `examples/demo/test/` | `cobs_test.py` (qemu, both builds), `rvc_decode.py` (llvm-mc), `rvc_exec.py` (qemu vs the extension) |
| `examples/demo/tools/` | `ExportC.lean` (images of compressed code), `RvcTable.lean`, `count.py` |
| `lean/Demo/` | the specifications, the four proofs, the images |
| `lean/NoCompiler/Auto.lean` | `nocompiler_auto` |
| `lean/NoCompiler/Ext/Rvc.lean` | the extension for compressed code, `nocompiler_auto_c` |
