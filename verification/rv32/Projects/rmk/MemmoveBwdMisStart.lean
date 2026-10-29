/-
  memmove, backward direction, n ≥ 16, source and destination NOT
  congruent mod 4: the start blocks from 0x80020e00 to the loop head
  0x80021012, one per misalignment o = 1, 2, 3 (pinned RMK image). They put
  the top `o` source bytes in `a5` (through the stack temporaries at
  sp+0x1a and sp+0x1c of the callee frame) and set up the loop registers.

  Original e5r code, Apache-2.0.
-/
import Projects.rmk.MemmoveBwdMisLoop
import Projects.rmk.MemmoveMisStart

set_option maxRecDepth 100000

namespace E5R.Rmk
open E5R E5R.Rmk.MemmoveFetch

/-- The core at the loop head 0x80021012 after a start block from `g`
    (at 0x80020e00); the RAM changed only at the temporaries. -/
structure AtBL (g g' : Core) (R R' : Word → BitVec 8) (o : Nat) : Prop where
  pc : g'.pc = 0x80021012
  csr : g'.sameCsr g
  t4 : g'.get 29 = BitVec.ofNat 32 (8 * o)
  a2 : g'.get 12 = (0 - BitVec.ofNat 32 (8 * o)) &&& 0x18#32
  t3 : g'.get 28 = g.get 28 + 4#32
  t5 : g'.get 30 = g.get 12 - BitVec.ofNat 32 o + g.get 11
  prev : ∀ k, k < o → byteOf (g'.get 15) k = R' (g.get 5 - BitVec.ofNat 32 o + BitVec.ofNat 32 k)
  ram : ∀ x, ¬ ((g.get 2 + 0x1a#32).toNat ≤ x.toNat ∧ x.toNat < (g.get 2 + 0x1a#32).toNat + 4) → R' x = R x
  frame : ∀ r : Reg, r.val ∉ [8, 12, 13, 15, 28, 29, 30, 31] → g'.get r = g.get r

theorem ramWrite_b_other (R : Word → BitVec 8) (a v x : Word) (h : x ≠ a) : ramWrite R a v .b x = R x := by
  simp [ramWrite, ramPut, h]

theorem asm_byte' (x y z : Word) (hx : x.toNat < 256) (hy : y.toNat < 256) (hz : z.toNat < 256) :
    byteOf ((y <<< 8) ||| (x ||| (z <<< 16))) 0 = byteOf x 0 ∧
    byteOf ((y <<< 8) ||| (x ||| (z <<< 16))) 1 = byteOf y 0 ∧
    byteOf ((y <<< 8) ||| (x ||| (z <<< 16))) 2 = byteOf z 0 := by
  rw [BitVec.or_comm x, ← BitVec.or_assoc]; exact asm_byte x y z hx hy hz

/-- Misalignment 1: `a5` is the single source byte below `t0`. -/
theorem bstart1 (g : Core) (R : Word → BitVec 8) (hpc : g.pc = 0x80020e00) (hq : Quiet g)
    (h6 : g.get 6 = BitVec.ofNat 32 1) (hsr : B.inRam (g.get 5 - BitVec.ofNat 32 1) 1 = true)
    (hT : B.inRam (g.get 2 + 0x1a#32) 4 = true)
    (hsep : (g.get 5).toNat ≤ (g.get 2 + 0x1a#32).toNat ∨ (g.get 2 + 0x1a#32).toNat + 4 ≤ (g.get 5 - BitVec.ofNat 32 1).toNat)
    (hs1 : 1 ≤ (g.get 5).toNat)
    (hlp : (g.get 28 + 4#32).ult (g.get 7) = true) :
    ∃ g' R', QRun B img 26 ⟨g, R⟩ ⟨g', R'⟩ ∧ AtBL g g' R R' 1 := by
  have hTr := (B_ram _ _).mp hT
  have T1a : B.inRam (g.get 2 + 0x1a#32) 1 = true := (B_ram _ _).mpr (by omega)
  have T1c : B.inRam (g.get 2 + 0x1c#32) 1 = true := (B_ram _ _).mpr (by constructor <;> bv_omega)
  let b1 := g.goto 0x80020e04
  let b2 := b1.wr 30 (alu .sub (b1.get 5) (b1.get 6)) 0x80020e08
  let bR1 := ramWrite R (b2.get 2 + 0x0000001c#32) (b2.get 0) .b
  let b3 := b2.goto 0x80020e0c
  let b4 := b3.wr 13 (alu .add (b3.get 0) 0x00000001#32) 0x80020e0e
  let bR2 := ramWrite bR1 (b4.get 2 + 0x0000001a#32) (b4.get 0) .b
  let b5 := b4.goto 0x80020e12
  let b6 := b5.goto 0x80020e16
  let b7 := b6.wr 15 (alu .add (b6.get 0) 0x00000000#32) 0x80020e18
  let b8 := b7.wr 31 (alu .add (b7.get 0) 0x00000000#32) 0x80020e1a
  let b9 := b8.wr 29 (alu .add (b8.get 2) 0x0000001c#32) 0x80020e1e
  let b10 := b9.goto 0x80020fde
  let b11 := b10.wr 15 (alu .add (b10.get 15) (b10.get 30)) 0x80020fe0
  let b12 := b11.wr 13 (extend .b false (ramRead bR2 (b11.get 15 + 0x00000000#32) .b)) 0x80020fe4
  let bR3 := ramWrite bR2 (b12.get 29 + 0x00000000#32) (b12.get 13) .b
  let b13 := b12.goto 0x80020fe8
  let b14 := b13.wr 8 (extend .b false (ramRead bR3 (b13.get 2 + 0x0000001a#32) .b)) 0x80020fec
  let b15 := b14.wr 15 (extend .b false (ramRead bR3 (b14.get 2 + 0x0000001c#32) .b)) 0x80020ff0
  let b16 := b15.wr 8 (alu .sll (b15.get 8) 0x00000010#32) 0x80020ff2
  let b17 := b16.wr 29 (alu .sll (b16.get 6) 0x00000003#32) 0x80020ff6
  let b18 := b17.wr 31 (alu .sll (b17.get 31) 0x00000008#32) 0x80020ff8
  let b19 := b18.wr 15 (alu .or (b18.get 15) (b18.get 8)) 0x80020ffa
  let b20 := b19.wr 28 (alu .add (b19.get 28) 0x00000004#32) 0x80020ffc
  let b21 := b20.wr 15 (alu .or (b20.get 31) (b20.get 15)) 0x80021000
  let b22 := b21.goto 0x80021004
  let b23 := b22.wr 13 (alu .sub (b22.get 0) (b22.get 29)) 0x80021008
  let b24 := b23.wr 30 (alu .sub (b23.get 12) (b23.get 6)) 0x8002100c
  let b25 := b24.wr 12 (alu .and (b24.get 13) 0x00000018#32) 0x80021010
  let b26 := b25.wr 30 (alu .add (b25.get 30) (b25.get 11)) 0x80021012
  have HBR_1 : taken .eq (g.get 6) (g.get 0) = false := by
    rw [h6, Core.get_zero]; decide
  have HIN_3 : B.inRam (b2.get 2 + 0x0000001c#32) 1 = true := by
    rw [show b2.get 2 = g.get 2 by simp [b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, Core.wr_get_ne]]; exact T1c
  have HIN_5 : B.inRam (b4.get 2 + 0x0000001a#32) 1 = true := by
    rw [show b4.get 2 = g.get 2 by simp [b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, Core.wr_get_ne]]; exact T1a
  have HBR_6 : taken .ne (b5.get 6) (b5.get 13) = false := by
    rw [show b5.get 6 = g.get 6 by simp [b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, Core.wr_get_ne], show b5.get 13 = 1 by simp [b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, Core.wr_get_ne, Core.wr_get_self, alu], h6]; decide
  have HIN_12 : B.inRam (b11.get 15 + 0x00000000#32) 1 = true := by
    rw [show b11.get 15 + 0x00000000#32 = g.get 5 - BitVec.ofNat 32 1 by simp [b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, Core.wr_get_ne, Core.wr_get_self, alu, h6]]
    exact (B_ram _ _).mpr (by have := (B_ram _ _).mp hsr; omega)
  have HIN_13 : B.inRam (b12.get 29 + 0x00000000#32) 1 = true := by
    rw [show b12.get 29 + 0x00000000#32 = g.get 2 + 0x1c#32 by simp [b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, Core.wr_get_ne, Core.wr_get_self, alu]]; exact T1c
  have HIN_14 : B.inRam (b13.get 2 + 0x0000001a#32) 1 = true := by
    rw [show b13.get 2 = g.get 2 by simp [b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, Core.wr_get_ne]]; exact T1a
  have HIN_15 : B.inRam (b14.get 2 + 0x0000001c#32) 1 = true := by
    rw [show b14.get 2 = g.get 2 by simp [b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, Core.wr_get_ne]]; exact T1c
  have HBR_22 : taken .geu (b21.get 28) (b21.get 7) = false := by
    rw [show b21.get 28 = g.get 28 + 4#32 by simp [b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, Core.wr_get_ne, Core.wr_get_self, alu],
      show b21.get 7 = g.get 7 by simp [b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, Core.wr_get_ne]]
    simp only [taken, hlp, Bool.not_true]
  have bs1 : DetStep B img ⟨g, R⟩ ⟨b1, R⟩ := by
    refine detStep_of (by rw [hpc]; decide) (by rw [hpc]; exact f80020e00) fun o => ?_
    rw [exec_branch, HBR_1, hpc]; rfl
  have bs2 : DetStep B img ⟨b1, R⟩ ⟨b2, R⟩ := by
    refine detStep_of (by show (0x80020e04 : Word).getLsbD 0 = false; decide) f80020e04 fun o => ?_
    rw [exec_op]; rfl
  have bs3 : DetStep B img ⟨b2, R⟩ ⟨b3, bR1⟩ := by
    refine detStep_of (by show (0x80020e08 : Word).getLsbD 0 = false; decide) f80020e08 fun o => ?_
    rw [exec_store, interp_store_ram (w := .b) o (by simp only [Width.bytes, Nat.mod_one]) HIN_3]; rfl
  have bs4 : DetStep B img ⟨b3, bR1⟩ ⟨b4, bR1⟩ := by
    refine detStep_of (by show (0x80020e0c : Word).getLsbD 0 = false; decide) f80020e0c fun o => ?_
    rw [exec_opimm]; rfl
  have bs5 : DetStep B img ⟨b4, bR1⟩ ⟨b5, bR2⟩ := by
    refine detStep_of (by show (0x80020e0e : Word).getLsbD 0 = false; decide) f80020e0e fun o => ?_
    rw [exec_store, interp_store_ram (w := .b) o (by simp only [Width.bytes, Nat.mod_one]) HIN_5]; rfl
  have bs6 : DetStep B img ⟨b5, bR2⟩ ⟨b6, bR2⟩ := by
    refine detStep_of (by show (0x80020e12 : Word).getLsbD 0 = false; decide) f80020e12 fun o => ?_
    rw [exec_branch, HBR_6]; rfl
  have bs7 : DetStep B img ⟨b6, bR2⟩ ⟨b7, bR2⟩ := by
    refine detStep_of (by show (0x80020e16 : Word).getLsbD 0 = false; decide) f80020e16 fun o => ?_
    rw [exec_opimm]; rfl
  have bs8 : DetStep B img ⟨b7, bR2⟩ ⟨b8, bR2⟩ := by
    refine detStep_of (by show (0x80020e18 : Word).getLsbD 0 = false; decide) f80020e18 fun o => ?_
    rw [exec_opimm]; rfl
  have bs9 : DetStep B img ⟨b8, bR2⟩ ⟨b9, bR2⟩ := by
    refine detStep_of (by show (0x80020e1a : Word).getLsbD 0 = false; decide) f80020e1a fun o => ?_
    rw [exec_opimm]; rfl
  have bs10 : DetStep B img ⟨b9, bR2⟩ ⟨b10, bR2⟩ := by
    refine detStep_of (by show (0x80020e1e : Word).getLsbD 0 = false; decide) f80020e1e fun o => ?_
    rw [exec_jal, Core.set_zero, show b9.pc + 0x1c0#32 = 0x80020fde by rw [show b9.pc = 0x80020e1e from rfl]; decide, jump_ok _ _ (by decide)]; rfl
  have bs11 : DetStep B img ⟨b10, bR2⟩ ⟨b11, bR2⟩ := by
    refine detStep_of (by show (0x80020fde : Word).getLsbD 0 = false; decide) f80020fde fun o => ?_
    rw [exec_op]; rfl
  have bs12 : DetStep B img ⟨b11, bR2⟩ ⟨b12, bR2⟩ := by
    refine detStep_of (by show (0x80020fe0 : Word).getLsbD 0 = false; decide) f80020fe0 fun o => ?_
    rw [exec_load, interp_load_ram (w := .b) o (by simp only [Width.bytes, Nat.mod_one]) HIN_12]; rfl
  have bs13 : DetStep B img ⟨b12, bR2⟩ ⟨b13, bR3⟩ := by
    refine detStep_of (by show (0x80020fe4 : Word).getLsbD 0 = false; decide) f80020fe4 fun o => ?_
    rw [exec_store, interp_store_ram (w := .b) o (by simp only [Width.bytes, Nat.mod_one]) HIN_13]; rfl
  have bs14 : DetStep B img ⟨b13, bR3⟩ ⟨b14, bR3⟩ := by
    refine detStep_of (by show (0x80020fe8 : Word).getLsbD 0 = false; decide) f80020fe8 fun o => ?_
    rw [exec_load, interp_load_ram (w := .b) o (by simp only [Width.bytes, Nat.mod_one]) HIN_14]; rfl
  have bs15 : DetStep B img ⟨b14, bR3⟩ ⟨b15, bR3⟩ := by
    refine detStep_of (by show (0x80020fec : Word).getLsbD 0 = false; decide) f80020fec fun o => ?_
    rw [exec_load, interp_load_ram (w := .b) o (by simp only [Width.bytes, Nat.mod_one]) HIN_15]; rfl
  have bs16 : DetStep B img ⟨b15, bR3⟩ ⟨b16, bR3⟩ := by
    refine detStep_of (by show (0x80020ff0 : Word).getLsbD 0 = false; decide) f80020ff0 fun o => ?_
    rw [exec_opimm]; rfl
  have bs17 : DetStep B img ⟨b16, bR3⟩ ⟨b17, bR3⟩ := by
    refine detStep_of (by show (0x80020ff2 : Word).getLsbD 0 = false; decide) f80020ff2 fun o => ?_
    rw [exec_opimm]; rfl
  have bs18 : DetStep B img ⟨b17, bR3⟩ ⟨b18, bR3⟩ := by
    refine detStep_of (by show (0x80020ff6 : Word).getLsbD 0 = false; decide) f80020ff6 fun o => ?_
    rw [exec_opimm]; rfl
  have bs19 : DetStep B img ⟨b18, bR3⟩ ⟨b19, bR3⟩ := by
    refine detStep_of (by show (0x80020ff8 : Word).getLsbD 0 = false; decide) f80020ff8 fun o => ?_
    rw [exec_op]; rfl
  have bs20 : DetStep B img ⟨b19, bR3⟩ ⟨b20, bR3⟩ := by
    refine detStep_of (by show (0x80020ffa : Word).getLsbD 0 = false; decide) f80020ffa fun o => ?_
    rw [exec_opimm]; rfl
  have bs21 : DetStep B img ⟨b20, bR3⟩ ⟨b21, bR3⟩ := by
    refine detStep_of (by show (0x80020ffc : Word).getLsbD 0 = false; decide) f80020ffc fun o => ?_
    rw [exec_op]; rfl
  have bs22 : DetStep B img ⟨b21, bR3⟩ ⟨b22, bR3⟩ := by
    refine detStep_of (by show (0x80021000 : Word).getLsbD 0 = false; decide) f80021000 fun o => ?_
    rw [exec_branch, HBR_22]; rfl
  have bs23 : DetStep B img ⟨b22, bR3⟩ ⟨b23, bR3⟩ := by
    refine detStep_of (by show (0x80021004 : Word).getLsbD 0 = false; decide) f80021004 fun o => ?_
    rw [exec_op]; rfl
  have bs24 : DetStep B img ⟨b23, bR3⟩ ⟨b24, bR3⟩ := by
    refine detStep_of (by show (0x80021008 : Word).getLsbD 0 = false; decide) f80021008 fun o => ?_
    rw [exec_op]; rfl
  have bs25 : DetStep B img ⟨b24, bR3⟩ ⟨b25, bR3⟩ := by
    refine detStep_of (by show (0x8002100c : Word).getLsbD 0 = false; decide) f8002100c fun o => ?_
    rw [exec_opimm]; rfl
  have bs26 : DetStep B img ⟨b25, bR3⟩ ⟨b26, bR3⟩ := by
    refine detStep_of (by show (0x80021010 : Word).getLsbD 0 = false; decide) f80021010 fun o => ?_
    rw [exec_op]; rfl
  have bk1 : b1.sameCsr g := (Core.sameCsr_goto _ _)
  have bk2 : b2.sameCsr g := (Core.sameCsr_wr _ _ _ _).trans bk1
  have bk3 : b3.sameCsr g := (Core.sameCsr_goto _ _).trans bk2
  have bk4 : b4.sameCsr g := (Core.sameCsr_wr _ _ _ _).trans bk3
  have bk5 : b5.sameCsr g := (Core.sameCsr_goto _ _).trans bk4
  have bk6 : b6.sameCsr g := (Core.sameCsr_goto _ _).trans bk5
  have bk7 : b7.sameCsr g := (Core.sameCsr_wr _ _ _ _).trans bk6
  have bk8 : b8.sameCsr g := (Core.sameCsr_wr _ _ _ _).trans bk7
  have bk9 : b9.sameCsr g := (Core.sameCsr_wr _ _ _ _).trans bk8
  have bk10 : b10.sameCsr g := (Core.sameCsr_goto _ _).trans bk9
  have bk11 : b11.sameCsr g := (Core.sameCsr_wr _ _ _ _).trans bk10
  have bk12 : b12.sameCsr g := (Core.sameCsr_wr _ _ _ _).trans bk11
  have bk13 : b13.sameCsr g := (Core.sameCsr_goto _ _).trans bk12
  have bk14 : b14.sameCsr g := (Core.sameCsr_wr _ _ _ _).trans bk13
  have bk15 : b15.sameCsr g := (Core.sameCsr_wr _ _ _ _).trans bk14
  have bk16 : b16.sameCsr g := (Core.sameCsr_wr _ _ _ _).trans bk15
  have bk17 : b17.sameCsr g := (Core.sameCsr_wr _ _ _ _).trans bk16
  have bk18 : b18.sameCsr g := (Core.sameCsr_wr _ _ _ _).trans bk17
  have bk19 : b19.sameCsr g := (Core.sameCsr_wr _ _ _ _).trans bk18
  have bk20 : b20.sameCsr g := (Core.sameCsr_wr _ _ _ _).trans bk19
  have bk21 : b21.sameCsr g := (Core.sameCsr_wr _ _ _ _).trans bk20
  have bk22 : b22.sameCsr g := (Core.sameCsr_goto _ _).trans bk21
  have bk23 : b23.sameCsr g := (Core.sameCsr_wr _ _ _ _).trans bk22
  have bk24 : b24.sameCsr g := (Core.sameCsr_wr _ _ _ _).trans bk23
  have bk25 : b25.sameCsr g := (Core.sameCsr_wr _ _ _ _).trans bk24
  have bk26 : b26.sameCsr g := (Core.sameCsr_wr _ _ _ _).trans bk25
  have brun : QRun B img 26 ⟨g, R⟩ ⟨b26, bR3⟩ :=
    .step hq bs1 (.step (Quiet.of_sameCsr bk1 hq) bs2 (.step (Quiet.of_sameCsr bk2 hq) bs3 (.step (Quiet.of_sameCsr bk3 hq) bs4 (.step (Quiet.of_sameCsr bk4 hq) bs5 (.step (Quiet.of_sameCsr bk5 hq) bs6 (.step (Quiet.of_sameCsr bk6 hq) bs7 (.step (Quiet.of_sameCsr bk7 hq) bs8 (.step (Quiet.of_sameCsr bk8 hq) bs9 (.step (Quiet.of_sameCsr bk9 hq) bs10 (.step (Quiet.of_sameCsr bk10 hq) bs11 (.step (Quiet.of_sameCsr bk11 hq) bs12 (.step (Quiet.of_sameCsr bk12 hq) bs13 (.step (Quiet.of_sameCsr bk13 hq) bs14 (.step (Quiet.of_sameCsr bk14 hq) bs15 (.step (Quiet.of_sameCsr bk15 hq) bs16 (.step (Quiet.of_sameCsr bk16 hq) bs17 (.step (Quiet.of_sameCsr bk17 hq) bs18 (.step (Quiet.of_sameCsr bk18 hq) bs19 (.step (Quiet.of_sameCsr bk19 hq) bs20 (.step (Quiet.of_sameCsr bk20 hq) bs21 (.step (Quiet.of_sameCsr bk21 hq) bs22 (.step (Quiet.of_sameCsr bk22 hq) bs23 (.step (Quiet.of_sameCsr bk23 hq) bs24 (.step (Quiet.of_sameCsr bk24 hq) bs25 (.single (Quiet.of_sameCsr bk25 hq) bs26)))))))))))))))))))))))))
  -- RAM
  have hR1 : ∀ x, x ≠ g.get 2 + 0x1c#32 → bR1 x = R x := by
    intro x hx; show ramWrite R (b2.get 2 + 0x0000001c#32) (b2.get 0) .b x = R x
    rw [show b2.get 2 = g.get 2 by simp [b2, b1, Core.wr_get_ne]]; exact ramWrite_b_other _ _ _ _ hx
  have hR2 : ∀ x, x ≠ g.get 2 + 0x1a#32 → bR2 x = bR1 x := by
    intro x hx; show ramWrite bR1 (b4.get 2 + 0x0000001a#32) (b4.get 0) .b x = bR1 x
    rw [show b4.get 2 = g.get 2 by simp [b4, b3, b2, b1, Core.wr_get_ne]]; exact ramWrite_b_other _ _ _ _ hx
  have a12 : b11.get 15 + 0x00000000#32 = g.get 5 - BitVec.ofNat 32 1 := by
    simp [b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, Core.wr_get_ne, Core.wr_get_self, alu, h6]
  have a13 : b12.get 29 + 0x00000000#32 = g.get 2 + 0x1c#32 := by
    simp [b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, Core.wr_get_ne, Core.wr_get_self, alu]
  have hR3 : bR3 = ramPut bR2 (g.get 2 + 0x1c#32) (bR2 (g.get 5 - BitVec.ofNat 32 1)) := by
    show ramWrite bR2 (b12.get 29 + 0x00000000#32) (b12.get 13) .b = _
    rw [a13, show b12.get 13 = extend .b false (ramRead bR2 (g.get 5 - BitVec.ofNat 32 1) .b) by
      simp only [b12, Core.wr_get_self _ (13 : Reg) _ _ (by decide)]; rw [a12], copyByte]
  have ne1 : g.get 5 - BitVec.ofNat 32 1 ≠ g.get 2 + 0x1a#32 := by bv_omega
  have ne2 : g.get 5 - BitVec.ofNat 32 1 ≠ g.get 2 + 0x1c#32 := by bv_omega
  have src : bR2 (g.get 5 - BitVec.ofNat 32 1) = R (g.get 5 - BitVec.ofNat 32 1) := by
    rw [hR2 _ ne1, hR1 _ ne2]
  refine ⟨b26, bR3, brun, ⟨rfl, bk26, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · simp [b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6,
      b5, b4, b3, b2, b1, Core.wr_get_ne, Core.wr_get_self, alu, h6]
  · simp [b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6,
      b5, b4, b3, b2, b1, Core.wr_get_ne, Core.wr_get_self, alu, h6]
  · simp [b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6,
      b5, b4, b3, b2, b1, Core.wr_get_ne, Core.wr_get_self, alu]
  · simp [b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6,
      b5, b4, b3, b2, b1, Core.wr_get_ne, Core.wr_get_self, alu, h6]
  · intro k hk
    have hk0 : k = 0 := by omega
    subst hk0
    have e15 : b26.get 15 = ((0 : Word) <<< 8) |||
        (extend .b false (ramRead bR3 (g.get 2 + 0x1c#32) .b) |||
          (extend .b false (ramRead bR3 (g.get 2 + 0x1a#32) .b) <<< 16)) := by
      simp [b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6,
        b5, b4, b3, b2, b1, Core.wr_get_ne, Core.wr_get_self, alu]
    rw [e15, (asm_byte' _ _ _ (lbu_lt _ _) (by decide) (lbu_lt _ _)).1, lbu_byte, hR3,
      show g.get 5 - BitVec.ofNat 32 1 + BitVec.ofNat 32 0 = g.get 5 - BitVec.ofNat 32 1 by bv_omega]
    simp [ramPut, ne2]
  · intro x hx
    rw [hR3]; simp only [ramPut]
    rw [if_neg (by intro e; apply hx; subst e; constructor <;> bv_omega)]
    rw [hR2 _ (by intro e; apply hx; subst e; constructor <;> bv_omega),
      hR1 _ (by intro e; apply hx; subst e; constructor <;> bv_omega)]
  · intro r hr
    have h8 : r ≠ 8 := fun e => hr (by subst e; decide)
    have h12 : r ≠ 12 := fun e => hr (by subst e; decide)
    have h13 : r ≠ 13 := fun e => hr (by subst e; decide)
    have h15 : r ≠ 15 := fun e => hr (by subst e; decide)
    have h28 : r ≠ 28 := fun e => hr (by subst e; decide)
    have h29 : r ≠ 29 := fun e => hr (by subst e; decide)
    have h30 : r ≠ 30 := fun e => hr (by subst e; decide)
    have h31 : r ≠ 31 := fun e => hr (by subst e; decide)
    simp [b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6,
      b5, b4, b3, b2, b1, Core.wr_get_ne, h8, h12, h13, h15, h28, h29, h30, h31]

end E5R.Rmk
