import Examples.Refine.Diff.ImgA
import Examples.Refine.Diff.ImgC
import Examples.Sum
import NoCompiler.RefineAuto
import Examples.Refine.Diff

/-
A certificate with jump pairs (docs/isa/refine.md): A is `sum`, C is `sum`
with `xor t5, t5, t5` inserted in its loop (examples/refine/diff/sum_c.s).
The insertion moves the loop's exit and the block's end, so the `beq` and
the `bne` have different offsets in A and C. As jump pairs (same branch,
each side its own offset, the two targets a pair) they stay in the lockstep
skeleton, and the only region is the changed straight-line piece:
`xor t5, t5, t5; add a2, a3, a2` against `add a2, a3, a2`, with t5 dead.
-/
namespace Examples.Refine.Jump
open NoCompiler NoCompiler.Lockstep Examples.Refine.Diff

/-- Every register but t5 (x30). -/
abbrev live : List Reg :=
  [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28,
    29, 31]

def region0 : RRegion where
  pb := 0x1112c#64
  pa := 0x1112c#64
  pbExit := 0x11134#64
  paExit := 0x11130#64
  domB := seqDom 0x1112c#64 [.rop .xor 30 30 30, .rop .add 12 13 12]
  domA := seqDom 0x1112c#64 [.rop .add 12 13 12]
  liveIn := live
  liveOut := live

def cert : Cert where
  pairs := [⟨0x11120#64, 0x11120#64, live⟩, ⟨0x11124#64, 0x11124#64, live⟩, ⟨0x11128#64, 0x11128#64, live⟩,
    ⟨0x11134#64, 0x11130#64, live⟩, ⟨0x11138#64, 0x11134#64, live⟩, ⟨0x1113c#64, 0x11138#64, live⟩,
    ⟨0x11140#64, 0x1113c#64, live⟩, ⟨0x11144#64, 0x11140#64, live⟩]
  regions := [region0]

theorem region0_ok : region0.Ok ImgA.code ImgC.code := by
  nocompiler_region region0 [.rop .add 12 13 12] [.rop .xor 30 30 30, .rop .add 12 13 12]

theorem refines : Refines Examples.Sum.spec ImgA.code ImgA.sum_dom ImgA.sum_entry
    ImgC.code ImgC.sum_dom ImgC.sum_entry := by
  have hA := Examples.Refine.Diff.sum_a_runs
  nocompiler_refine cert [region0_ok]

/-! ## Controls -/

-- Without the pair the `beq`'s two targets (C 0x11140, A 0x1113c) form, the check fails.
example : check ImgA.code ImgC.code ImgA.sum_dom ImgC.sum_dom ImgA.sum_entry ImgC.sum_entry
    { cert with pairs := cert.pairs.filter (·.pb != 0x11140#64) } = false := by decide +kernel

-- With t5 live after the region, the two sides are not equivalent (C zeroes t5).
example : ¬ SeqEquiv [30] [30] [.rop .add 12 13 12] [.rop .xor 30 30 30, .rop .add 12 13 12] := by
  intro h
  have := h (fun _ => 1) (fun _ => 1) (fun _ _ => rfl) 30 (by simp)
  revert this; decide

end Examples.Refine.Jump
