# Runner interface for a future full memmove contract (proposal; no such theorem exists)

Status: **interface only**. No full memmove contract is proved. The proved
contracts are `E5R.Rmk.Memmove.contract` (n < 16) and
`E5R.Rmk.Memmove.contractB` (n < 16 either way, or n ≥ 16 forward with
src ≡ dst mod 4). Each has its own job, and neither changes. This file says
what the runner needs when the peer (proofs) and main (specification) produce
a contract for every n, every alignment and both directions, and how it will be
checked. The names below are proposals for the peer and main to accept or
rename.

## Specification obligations (from REVIEW.md M1–M3 and MATRIX.md)

The emitted routine uses the 48-byte callee frame and writes caller bytes in
[sp−34, sp):
* misaligned forward: sp−34, −32, −28..−25;
* misaligned backward: sp−22, −20, −16..−13;
* every path: the save slots sp−12..sp−1.

A precondition `PreFull m` should therefore contain:

* `pc = 0x80020c1e` and `Quiet`, as now;
* `B.inRam dst n` and `B.inRam src n`, as now (no case split: every n, both
  directions, any residues);
* `frame`: `sp % 4 = 0`, `B.inRam (sp − 48) 48` (or at least `sp − 34`, the
  lowest byte written; the matrix's sp-boundary cases show sp = rwBase+32 faults
  on the misaligned path and rwBase+36 runs);
* `dstSep` and `srcSep` against the whole frame:
  [dst, dst+n) ∩ [sp−48, sp) = ∅, and the same for src (M3: overlap with the
  temporaries corrupts the result);
* `ra` even, as now.

A postcondition `PostFull m₀ m` should contain:
* pc = ra;
* ABI registers preserved (all but t0–t6 and a1–a7, as `PostB`);
* CSRs unchanged;
* `ram`: for every x outside [sp−48, sp), m.ram x = memmove of m₀.ram.

Frame bytes are unspecified. Exact offsets could replace the whole frame, but
the whole frame is simpler and is what callers can rely on.

## Runner job (template `rmk-memmove-full.json.template`, not a job yet)

* Same image module (`Projects.rmk.Elf`, namespace `E5R.Rmk.Image`, the runner's
  packed file) and the same `img_eq`/`board_eq` wrapper equalities as the n < 16
  and contractB jobs.
* A new wrapper `Projects/ramimage/MemmoveFull.lean` (mine, written when the
  theorem exists) restates the contract over `E5R.Rmk.Image.image.ro` and
  `QemuVirtRv32.board E5R.Rmk.Image.image.rwBase`.
* `theorems`: the peer's full contract name, `E5R.RmkMemmove.img_eq`,
  `E5R.RmkMemmove.board_eq`, and `E5R.RmkMemmoveFull.*`. All are axiom-audited,
  along with the four image bindings.
* `limits`: `rss_mib` 10240 (Fetch.lean peaks at 6.5 GB). The runner limits
  resident memory, never address space.
* Activation: rename the template to `.json` only when the theorem exists. Until
  then, a run would end `error` ("no axiom report"), which is a missing input, not
  a rejection.

## Controls the job will get (from the matrix; mine)

* Job-level mutations in the style of `scripts/test-rmk-memmoveB-job.py`: drop
  `frame`, narrow `dstSep`/`srcSep` back to the save slots (M3), or exclude only
  [sp−12, sp) in `PostFull.ram` (M1). Each must be rejected (`failed`).
* An ELF word-loop corruption, rejected at its instruction fact.
* An unmutated copy (`proved`) and a missing module (`error`, a tool problem)
  as controls.
* The model-execution matrix (`matrix.sh`) is rerun on the same image as a
  regression check. It tests chosen inputs; the theorem is the claim.
