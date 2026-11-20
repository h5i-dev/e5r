import NoCompiler.RefineStraightRegion

/-
Straight-line equivalences (spec-v1-refine.md item 6; docs/isa/refine.md),
the kinds of edit a refinement task makes inside a block: peephole,
strength reduction, a Zbb instruction for a branchless idiom. Each states
the live-in and live-out registers; registers outside the live-out set
(temporaries) may differ.

The first three are in the kernel tier (`seq_equiv`, standard axioms). The
last two need `bv_decide` (`seq_equiv_bv`): they are in the bv_decide tier
and the audit lists them separately (docs/isa/trust.md). The two refuted
ones are controls: a wrong edit is not an equivalence.
-/
namespace Examples.Refine.Straight
open NoCompiler

/-- `slli a0, a0, 3` = `sh3add a0, a0, zero`. -/
theorem slli_sh3add : SeqEquiv [10] [10] [.shift .slli 10 10 3#6] [.rop .sh3add 10 10 0] := by
  seq_equiv

/-- Strength reduction: `li t0, 8; mul a0, a0, t0` = `slli a0, a0, 3` (t0 dead). -/
theorem mul8_slli : SeqEquiv [10] [10] [.iop .addi 5 0 8#12, .rop .mul 10 10 5]
    [.shift .slli 10 10 3#6] := by
  seq_equiv

/-- Zba: `slli t0, a1, 3; add a0, a0, t0` = `sh3add a0, a1, a0` (t0 dead). -/
theorem index_sh3add : SeqEquiv [10, 11] [10] [.shift .slli 5 11 3#6, .rop .add 10 10 5]
    [.rop .sh3add 10 11 10] := by
  seq_equiv

/-- Branchless minimum = Zbb `min`: `slt t0, a0, a1; sub t0, zero, t0;
    xor t1, a0, a1; and t1, t1, t0; xor a0, a1, t1` = `min a0, a0, a1`. -/
theorem branchless_min : SeqEquiv [10, 11] [10]
    [.rop .slt 5 10 11, .rop .sub 5 0 5, .rop .xor 6 10 11, .rop .and 6 6 5, .rop .xor 10 11 6]
    [.rop .min 10 10 11] := by
  seq_equiv_bv

/-- Rounding up to a multiple of 8: `addi a0, a0, 7; srli a0, a0, 3; slli a0, a0, 3`
    = `addi a0, a0, 7; andi a0, a0, -8`. -/
theorem round8 : SeqEquiv [10] [10]
    [.iop .addi 10 10 7#12, .shift .srli 10 10 3#6, .shift .slli 10 10 3#6]
    [.iop .addi 10 10 7#12, .iop .andi 10 10 0xff8#12] := by
  seq_equiv_bv

/-! ## Controls: wrong edits are refuted (by a counterexample, in the kernel) -/

/-- `slli a0, a0, 3` is not `slli a0, a0, 2`. -/
theorem shift_refuted : ¬ SeqEquiv [10] [10] [.shift .slli 10 10 3#6] [.shift .slli 10 10 2#6] := by
  intro h
  have := h (fun _ => 1) (fun _ => 1) (fun _ _ => rfl) 10 (by simp)
  revert this; decide

/-- A temporary that is live out may not be dropped: `li t0, 8; mul a0, a0, t0`
    is not `slli a0, a0, 3` when t0 is live. -/
theorem live_temp_refuted : ¬ SeqEquiv [10, 5] [10, 5] [.iop .addi 5 0 8#12, .rop .mul 10 10 5]
    [.shift .slli 10 10 3#6] := by
  intro h
  have := h (fun _ => 0) (fun _ => 0) (fun _ _ => rfl) 5 (by simp)
  revert this; decide

/-! ## As a region (C's `RRegion.Ok`)

The strength reduction as a changed interval between two code images: A
holds `li t0, 8; mul a0, a0, t0` at 0x11000, B holds `slli a0, a0, 3` at
0x22000; live in and out: a0. -/

def codeA : Code := ⟨0x11000#64, #[0x00800293#32, 0x02550533#32]⟩
def codeB : Code := ⟨0x22000#64, #[0x00351513#32]⟩

def mulRegion : RRegion where
  pa := 0x11000#64
  pb := 0x22000#64
  paExit := 0x11008#64
  pbExit := 0x22004#64
  domA := seqDom 0x11000#64 [.iop .addi 5 0 8#12, .rop .mul 10 10 5]
  domB := seqDom 0x22000#64 [.shift .slli 10 10 3#6]
  liveIn := [10]
  liveOut := [10]

theorem mulRegion_ok : mulRegion.Ok codeA codeB :=
  RRegion.ok_of_seqEquiv (as := [.iop .addi 5 0 8#12, .rop .mul 10 10 5]) (bs := [.shift .slli 10 10 3#6])
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide +kernel) (by decide +kernel) rfl rfl (by decide) (by decide) mul8_slli

end Examples.Refine.Straight
