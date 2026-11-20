# Adversarial review: memmove contractB job and the misaligned-forward proofs (through peer `2357d61`)

Exporter/runner worker, 2026-10-29. Scope: the runner job
`jobs/rmk/rmk-memmove-contractB.json` with its wrapper `Projects/ramimage/MemmoveB.lean`,
and the peer's `Projects/rmk/MemmoveMis*.lean` at `2357d61` (start, loop, end and mid
blocks; no composed misaligned contract yet). No peer file was edited.

Evidence:
* **Execution audit (model):** `MemmoveRun.lean`, rerun with `run.sh SCRATCH` (a
  native build in a scratch package of copied sources, 35 s). It runs the emitted
  memmove in the model (`stepInstr`, QEMU-virt board, the image from the checker's
  reader applied to the runner's packed file) on concrete inputs. It compares
  every destination byte with memmove's result, and every other byte in
  [dst−16, dst+n+16) and [sp−64, sp+16) with its initial value (a non-zero
  pattern). Transcript: `memmove-run.txt`. This is execution evidence on chosen
  inputs, not a proof.
* **Disassembly** of `compiler_builtins::mem::memmove` (0x80020d9e..0x800210ba),
  read independently of the peer's instruction facts.

Nothing below is a soundness hole in what has been proved. `contractB`'s
precondition excludes every input that misbehaves here. The findings are
obligations for extending the contract beyond it.

## Findings

### M1. The full memmove uses a 34-byte stack region; `PreB`/`PostB` know only 12 bytes (main, peer)

`memmove` allocates a 48-byte frame (`addi sp,sp,-0x30`) and stores into it at
callee sp+0x0e, +0x10, +0x14..+0x17, +0x1a, +0x1c and +0x20..+0x23, as well as
the save slots +0x24..+0x2f. In caller terms that is [sp−34, sp).

`PreB.slots` (`sp ≥ rwBase+12`), `dstSep` and `srcSep` (dst and src off
[sp−12, sp)), and `PostB.ram` (all RAM outside `InSlots` = [sp−12, sp) equals
memmove's result) describe only the save slots. That is exact for the paths
`contractB` covers: the model runs of n < 16 and of aligned n ≥ 16 change only
the slots. For the paths still open:

* **Misaligned forward:** every run (o = 1, 2, 3; disjoint, overlapping, at RAM
  edges) changes caller sp−34, −32 and −28..−25. These are the temporaries the
  peer's lemmas name (sp+0x0e, +0x10, +0x14..0x17).
* **Backward n ≥ 16, misaligned** (dst = src+5): it changes sp−22, −20 and
  −16..−13.

So a contract that adds these paths must:
* (a) exclude those bytes from the RAM clause (simplest: the whole frame
  [sp−48, sp));
* (b) require them in model RAM (`Slots` lower bound at least sp−34 ≥ rwBase;
  simplest: sp−48 ≥ rwBase);
* (c) separate dst and src from them.

Reusing `PreB`/`PostB` unchanged for those paths would make the statement false.
The proof would then not go through, so this risks wasted work, not a wrong
theorem.

### M2. `Slots`' lower bound is too weak for the misaligned path (main, peer)

With sp = rwBase+12, which `Slots` admits, the misaligned path faults in the model
at 0x80020e68 (`sw zero,0x14(sp)`, i.e. caller sp−28 is below rwBase): "store to
an unmodeled address". On QEMU the same store would land in `.rodata`, which is
writable RAM there. The model's fail-closed image is what turns this into a fault
instead of a silent overwrite. The aligned path at the same sp is fine (changes
only the slots). See M1(b).

### M3. Separation from the save slots is not separation from the frame (peer)

Inputs that satisfy `PreB.dstSep`/`srcSep` but overlap the temporaries give wrong
results on the misaligned path:
* **dst over the temporaries:** dst = [sp−40, sp−20), n = 20, src misaligned
  elsewhere. 2 destination bytes differ from memmove's result.
* **src over the temporaries:** src = [sp−39, sp−19). 4 destination bytes are
  wrong.

These inputs are outside `PreB`, which needs src ≡ dst (mod 4) for n ≥ 16, so
`contractB` is unaffected. The peer's component lemmas do carry the needed
separation (`start_any.hsep`, `end_any.hsep`, and `mis_loop`'s
`dst ≤ a1 ∨ a1+8 ≤ dst`). The composed precondition must imply them, for example
dst and src disjoint from [sp−48, sp). Note that the caller's own data never
legitimately lies below its sp, so this costs callers nothing.

### Checked, no finding

* **Aliasing (forward):** `PreB`'s direction test `(dst − src) ≥ n` (unsigned)
  with RAM-bounded addresses means dst ≥ src+n or dst < src.
  * `mis_loop` needs `dst ≤ a1 ∨ a1+8 ≤ dst` (aligned words). Overlap with
    dst < src gives dst ≤ a1; a disjoint copy with n ≥ 16 gives a1+8 ≤ dst. Both
    are dischargeable.
  * Runs with dst = src−1 (o = 1, n = 40) give the exact memmove result.
* **Address wrap:**
  * `B_ram` bounds `a.toNat + n ≤ 0x81000000`, so no range wraps.
  * The wrapping subtraction in the direction test is harmless for addresses
    in [0x80029bc8, 0x81000000).
  * Destination ranges ending exactly at 0x81000000 run correctly.
* **Source-read bounds:**
  * With model RAM cut exactly at a misaligned source's first byte, or its last
    byte at 0x81000000, every case (o = 1, 2, 3) runs without a fault and with
    the correct result.
  * The same holds for destinations at both RAM edges.
  * So the misaligned path reads no byte outside [src, src+n) beyond its own
    frame, and writes none outside [dst, dst+n). This matches the peer's
    `start_any`/`end_any`/`mis_loop` hypotheses (`hsr`, `hsrc`, `inRam (a1+4)`).
* **Code separation:** the image (everything below rwBase) is read-only in the
  model, and every store there faults (M2 shows one), so any no-fault theorem,
  `contractB` included, implies memmove does not write code or `.rodata`. No run
  within `PreB` faulted.
* **contractB job:**
  * The wrapper's `img_eq` (by `rfl`) and `board_eq` (from the kernel-checked
    `image_rwBase`) tie the proofs to the runner's single image.
  * The job audits both, plus the contract and wrapper.
  * Mutations: residue, direction, stack separation, postcondition and a loop
    instruction are each rejected (`failed`), and the unmutated copy proves
    (`memmoveB-mutations.txt` in ../ram-image/rmk-qemu-riscv-rynk/).
* **Registers:** all runs, including the backward and misaligned ones `PreB` does
  not cover, preserve every ABI register `PostB` lists.

## Actions

* **Peer:** when composing the misaligned path (and backward n ≥ 16), state the
  frame as [sp−48, sp):
  * in RAM: sp−48 ≥ rwBase;
  * disjoint from [dst, dst+n) and [src, src+n);
  * excluded from the RAM clause.

  Keep `PreB`/`PostB` as they are for `contractB`; they are exact for its paths.
* **Main:** a future full-memmove contract changes `Pre`/`Post` (frame), so the
  runner job will get a new wrapper and job beside `contractB`'s rather than
  replace it.
* **Me:** add the cases above as job-level controls once the composed theorem
  exists.
