/-
  The byte loops of the emitted memmove (compiler_builtins) in the pinned
  RMK image, as quiet runs that compute `fwd` / `bwd` (Copy.lean).

  Original e5r code, Apache-2.0.

    forward  0x80020fc6: lbu a4,0(a1); addi a2,a2,-1; sb a4,0(a3);
             addi a3,a3,1; addi a1,a1,1; bnez a2,0x80020fc6;  j 0x800210b0
    backward 0x8002109c: lbu a2,0(a6); addi a3,s1,-1; sb a2,-1(s1);
             addi a6,a6,-1; mv s1,a3; bltu a1,a3,0x8002109c  (falls to 0x800210b0)

  Each lemma covers every iteration (induction on the count), every
  machine of the run is quiet, every load and store is shown inside model
  RAM (so none faults or reaches a device), and the loop ends at the
  epilogue 0x800210b0.
-/
import Projects.rmk.Run
import Projects.rmk.Copy
import Projects.rmk.MemmoveFetch

set_option maxRecDepth 100000

namespace E5R.Rmk
open E5R E5R.Rmk.MemmoveFetch

/-- Model RAM of the board ends below 2^32. -/
theorem B_ram (a : Word) (n : Nat) :
    B.inRam a n = true ↔ 0x80029bc8 ≤ a.toNat ∧ a.toNat + n ≤ 0x81000000 := by
  rw [Board.inRam_iff]; simp [QemuVirtRv32.board, QemuVirtRv32.dramEnd]

theorem inRam_byte {a : Word} {n i : Nat} (h : B.inRam a n = true) (hi : i < n) :
    B.inRam (a + BitVec.ofNat 32 i) 1 = true := by
  rw [B_ram] at *; constructor <;> bv_omega

theorem inRam_succ {a : Word} {n : Nat} (h : B.inRam a (n + 1) = true) : B.inRam (a + 1) n = true := by
  rw [B_ram] at *; constructor <;> bv_omega

theorem inRam_pred {a : Word} {n : Nat} (h : B.inRam a (n + 1) = true) :
    B.inRam a n = true := by
  rw [B_ram] at *; omega

theorem inRam_one {a : Word} {n : Nat} (h : B.inRam a (n + 1) = true) : B.inRam a 1 = true := by
  rw [B_ram] at *; omega

theorem lsb_lit (x : Word) (h : x.toNat % 2 = 0) : x.getLsbD 0 = false := by
  simp [BitVec.getLsbD, Nat.testBit, h]

/-- The core after one forward iteration's five straight-line instructions. -/
def fwdBody (c : Core) (ram : Word → BitVec 8) (k : Nat) : Core :=
  ((((c.wr 14 (extend .b false (ramRead ram (c.get 11) .b)) 0x80020fca).wr 12 (BitVec.ofNat 32 k)
    0x80020fcc).goto 0x80020fd0).wr 13 (c.get 13 + 1) 0x80020fd2).wr 11 (c.get 11 + 1) 0x80020fd4

theorem fwdBody_get (c : Core) (ram) (k : Nat) (r : Reg) (h11 : r ≠ 11) (h12 : r ≠ 12) (h13 : r ≠ 13)
    (h14 : r ≠ 14) : (fwdBody c ram k).get r = c.get r := by
  simp [fwdBody, Core.wr_get_ne, h11, h12, h13, h14]

theorem fwdBody_sameCsr (c : Core) (ram) (k : Nat) : (fwdBody c ram k).sameCsr c :=
  (Core.sameCsr_wr _ _ _ _).trans ((Core.sameCsr_wr _ _ _ _).trans ((Core.sameCsr_goto _ _).trans
    ((Core.sameCsr_wr _ _ _ _).trans (Core.sameCsr_wr _ _ _ _))))

/-- One forward iteration up to the branch: five quiet deterministic steps. -/
theorem fwd_body (k : Nat) (c : Core) (ram : Word → BitVec 8) (hpc : c.pc = 0x80020fc6) (hq : Quiet c)
    (hk : c.get 12 = BitVec.ofNat 32 (k + 1)) (hs : B.inRam (c.get 11) 1 = true)
    (hd : B.inRam (c.get 13) 1 = true) :
    QRun B img 5 ⟨c, ram⟩ ⟨fwdBody c ram k, ramPut ram (c.get 13) (ram (c.get 11))⟩ := by
  let v := extend .b false (ramRead ram (c.get 11) .b)
  let c1 := c.wr 14 v 0x80020fca
  let c2 := c1.wr 12 (BitVec.ofNat 32 k) 0x80020fcc
  let c3 := c2.goto 0x80020fd0
  let c4 := c3.wr 13 (c.get 13 + 1) 0x80020fd2
  have q1 : Quiet c1 := Quiet.of_sameCsr (Core.sameCsr_wr _ _ _ _) hq
  have q2 : Quiet c2 := Quiet.of_sameCsr (Core.sameCsr_wr _ _ _ _) q1
  have q3 : Quiet c3 := Quiet.of_sameCsr (Core.sameCsr_goto _ _) q2
  have q4 : Quiet c4 := Quiet.of_sameCsr (Core.sameCsr_wr _ _ _ _) q3
  have s0 : DetStep B img ⟨c, ram⟩ ⟨c1, ram⟩ := by
    refine detStep_of (by rw [hpc]; decide) (by rw [hpc]; exact f80020fc6) fun o => ?_
    rw [exec_load, BitVec.add_zero, interp_load_ram o (by simp only [Width.bytes, Nat.mod_one]) hs, hpc]; rfl
  have s1 : DetStep B img ⟨c1, ram⟩ ⟨c2, ram⟩ := by
    refine detStep_of (by show (0x80020fca : Word).getLsbD 0 = false; decide) f80020fca fun o => ?_
    rw [exec_opimm]
    have : c1.get 12 = BitVec.ofNat 32 (k + 1) := by simp [c1, Core.wr_get_ne, hk]
    rw [this]
    have e : alu .add (BitVec.ofNat 32 (k + 1)) 0xffffffff#32 = BitVec.ofNat 32 k := by
      simp only [alu]; bv_omega
    rw [e]; rfl
  have s2 : DetStep B img ⟨c2, ram⟩ ⟨c3, ramPut ram (c.get 13) (ram (c.get 11))⟩ := by
    refine detStep_of (by show (0x80020fcc : Word).getLsbD 0 = false; decide) f80020fcc fun o => ?_
    rw [exec_store, BitVec.add_zero]
    have e13 : c2.get 13 = c.get 13 := by simp [c2, c1, Core.wr_get_ne]
    have e14 : c2.get 14 = v := by simp [c2, c1, Core.wr_get_ne, Core.wr_get_self]
    rw [e13, e14, interp_store_ram o (by simp only [Width.bytes, Nat.mod_one]) hd, copyByte]; rfl
  have s3 : DetStep B img ⟨c3, ramPut ram (c.get 13) (ram (c.get 11))⟩
      ⟨c4, ramPut ram (c.get 13) (ram (c.get 11))⟩ := by
    refine detStep_of (by show (0x80020fd0 : Word).getLsbD 0 = false; decide) f80020fd0 fun o => ?_
    rw [exec_opimm]
    have : c3.get 13 = c.get 13 := by simp [c3, c2, c1, Core.wr_get_ne]
    rw [this]; rfl
  have s4 : DetStep B img ⟨c4, ramPut ram (c.get 13) (ram (c.get 11))⟩
      ⟨fwdBody c ram k, ramPut ram (c.get 13) (ram (c.get 11))⟩ := by
    refine detStep_of (by show (0x80020fd2 : Word).getLsbD 0 = false; decide) f80020fd2 fun o => ?_
    rw [exec_opimm]
    have : c4.get 11 = c.get 11 := by simp [c4, c3, c2, c1, Core.wr_get_ne]
    rw [this]; rfl
  exact .step hq s0 (.step q1 s1 (.step q2 s2 (.step q3 s3 (.single q4 s4))))

/-- The forward byte loop: from 0x80020fc6 with `a2 = k+1` bytes left, it
    copies them upward from `a1` to `a3` and ends at the epilogue. -/
theorem fwd_loop : ∀ (k : Nat) (c : Core) (ram : Word → BitVec 8),
    c.pc = 0x80020fc6 → Quiet c → c.get 12 = BitVec.ofNat 32 (k + 1) → k + 1 < 2 ^ 32 →
    B.inRam (c.get 11) (k + 1) = true → B.inRam (c.get 13) (k + 1) = true →
    ∃ n c', QRun B img n ⟨c, ram⟩ ⟨c', fwd ram (c.get 11) (c.get 13) (k + 1)⟩ ∧
      c'.pc = 0x800210b0 ∧ c'.sameCsr c ∧
      ∀ r : Reg, r ≠ 11 → r ≠ 12 → r ≠ 13 → r ≠ 14 → c'.get r = c.get r := by
  intro k
  induction k with
  | zero =>
    intro c ram hpc hq hk _ hs hd
    have hb := fwd_body 0 c ram hpc hq hk (by simpa using hs) (by simpa using hd)
    let c5 := fwdBody c ram 0
    have q5 : Quiet c5 := Quiet.of_sameCsr (fwdBody_sameCsr c ram 0) hq
    let r1 := ramPut ram (c.get 13) (ram (c.get 11))
    have s5 : DetStep B img ⟨c5, r1⟩ ⟨c5.goto 0x80020fd6, r1⟩ := by
      refine detStep_of (by show (0x80020fd4 : Word).getLsbD 0 = false; decide) f80020fd4 fun o => ?_
      rw [exec_branch]
      have : c5.get 12 = BitVec.ofNat 32 0 := by simp [c5, fwdBody, Core.wr_get_ne, Core.wr_get_self]
      rw [this]; simp [taken]; rfl
    have q6 : Quiet (c5.goto 0x80020fd6) := Quiet.of_sameCsr (Core.sameCsr_goto _ _) q5
    have s6 : DetStep B img ⟨c5.goto 0x80020fd6, r1⟩ ⟨c5.goto 0x800210b0, r1⟩ := by
      refine detStep_of (by show (0x80020fd6 : Word).getLsbD 0 = false; decide) f80020fd6 fun o => ?_
      rw [exec_jal, Core.set_zero, jump_ok _ _ (by show (0x800210b0 : Word).getLsbD 0 = false; decide)]; rfl
    refine ⟨7, c5.goto 0x800210b0, ?_, rfl, ?_, ?_⟩
    · have := hb.trans (.step q5 s5 (.single q6 s6))
      simpa [fwd] using this
    · exact (Core.sameCsr_goto _ _).trans (fwdBody_sameCsr c ram 0)
    · intro r a b d e; simp only [Core.goto_get]; exact fwdBody_get c ram 0 r a b d e
  | succ k ih =>
    intro c ram hpc hq hk hk32 hs hd
    have hb := fwd_body (k + 1) c ram hpc hq hk (inRam_one hs) (inRam_one hd)
    let c5 := fwdBody c ram (k + 1)
    have cs5 : c5.sameCsr c := fwdBody_sameCsr c ram (k + 1)
    have q5 : Quiet c5 := Quiet.of_sameCsr cs5 hq
    let r1 := ramPut ram (c.get 13) (ram (c.get 11))
    have s5 : DetStep B img ⟨c5, r1⟩ ⟨c5.goto 0x80020fc6, r1⟩ := by
      refine detStep_of (by show (0x80020fd4 : Word).getLsbD 0 = false; decide) f80020fd4 fun o => ?_
      rw [exec_branch]
      have : c5.get 12 = BitVec.ofNat 32 (k + 1) := by simp [c5, fwdBody, Core.wr_get_ne, Core.wr_get_self]
      have hne : (BitVec.ofNat 32 (k + 1) != (0 : Word)) = true := by
        simp only [bne_iff_ne, ne_eq]; bv_omega
      rw [this]; simp only [taken, Core.get_zero, hne, if_true]
      have hp5 : c5.pc + 0xfffffff2#32 = 0x80020fc6 := by
        rw [show c5.pc = 0x80020fd4 from rfl]; decide
      rw [hp5, jump_ok _ _ (by decide)]; rfl
    have q6 : Quiet (c5.goto 0x80020fc6) := Quiet.of_sameCsr (Core.sameCsr_goto _ _) q5
    have g11 : (c5.goto 0x80020fc6).get 11 = c.get 11 + 1 := by
      simp [c5, fwdBody, Core.wr_get_self]
    have g13 : (c5.goto 0x80020fc6).get 13 = c.get 13 + 1 := by
      simp [c5, fwdBody, Core.wr_get_ne, Core.wr_get_self]
    have g12 : (c5.goto 0x80020fc6).get 12 = BitVec.ofNat 32 (k + 1) := by
      simp [c5, fwdBody, Core.wr_get_ne, Core.wr_get_self]
    obtain ⟨n, c', hr, hpc', hcs, hfr⟩ := ih (c5.goto 0x80020fc6) r1 rfl q6 g12 (by omega)
      (by rw [g11]; exact inRam_succ hs) (by rw [g13]; exact inRam_succ hd)
    refine ⟨5 + 1 + n, c', ?_, hpc', ?_, ?_⟩
    · rw [g11, g13] at hr
      exact (hb.trans (.single q5 s5)).trans hr
    · exact hcs.trans ((Core.sameCsr_goto _ _).trans cs5)
    · intro r a b d e
      rw [hfr r a b d e, Core.goto_get]; exact fwdBody_get c ram (k + 1) r a b d e

/-- The core after one backward iteration's five straight-line instructions. -/
def bwdBody (c : Core) (ram : Word → BitVec 8) : Core :=
  ((((c.wr 12 (extend .b false (ramRead ram (c.get 16) .b)) 0x800210a0).wr 13 (c.get 9 + 0xffffffff#32)
    0x800210a4).goto 0x800210a8).wr 16 (c.get 16 + 0xffffffff#32) 0x800210aa).wr 9
    (alu .add 0 (c.get 9 + 0xffffffff#32)) 0x800210ac

theorem bwdBody_sameCsr (c : Core) (ram) : (bwdBody c ram).sameCsr c :=
  (Core.sameCsr_wr _ _ _ _).trans ((Core.sameCsr_wr _ _ _ _).trans ((Core.sameCsr_goto _ _).trans
    ((Core.sameCsr_wr _ _ _ _).trans (Core.sameCsr_wr _ _ _ _))))

theorem bwdBody_get (c : Core) (ram) (r : Reg) (h9 : r ≠ 9) (h12 : r ≠ 12) (h13 : r ≠ 13)
    (h16 : r ≠ 16) : (bwdBody c ram).get r = c.get r := by
  simp [bwdBody, Core.wr_get_ne, h9, h12, h13, h16]

/-- One backward iteration up to the branch: five quiet deterministic steps. -/
theorem bwd_body (c : Core) (ram : Word → BitVec 8) (hpc : c.pc = 0x8002109c) (hq : Quiet c)
    (hs : B.inRam (c.get 16) 1 = true) (hd : B.inRam (c.get 9 + 0xffffffff#32) 1 = true) :
    QRun B img 5 ⟨c, ram⟩ ⟨bwdBody c ram, ramPut ram (c.get 9 + 0xffffffff#32) (ram (c.get 16))⟩ := by
  let v := extend .b false (ramRead ram (c.get 16) .b)
  let c1 := c.wr 12 v 0x800210a0
  let c2 := c1.wr 13 (c.get 9 + 0xffffffff#32) 0x800210a4
  let c3 := c2.goto 0x800210a8
  let c4 := c3.wr 16 (c.get 16 + 0xffffffff#32) 0x800210aa
  let r1 := ramPut ram (c.get 9 + 0xffffffff#32) (ram (c.get 16))
  have q1 : Quiet c1 := Quiet.of_sameCsr (Core.sameCsr_wr _ _ _ _) hq
  have q2 : Quiet c2 := Quiet.of_sameCsr (Core.sameCsr_wr _ _ _ _) q1
  have q3 : Quiet c3 := Quiet.of_sameCsr (Core.sameCsr_goto _ _) q2
  have q4 : Quiet c4 := Quiet.of_sameCsr (Core.sameCsr_wr _ _ _ _) q3
  have s0 : DetStep B img ⟨c, ram⟩ ⟨c1, ram⟩ := by
    refine detStep_of (by rw [hpc]; decide) (by rw [hpc]; exact f8002109c) fun o => ?_
    rw [exec_load, BitVec.add_zero, interp_load_ram o (by simp only [Width.bytes, Nat.mod_one]) hs, hpc]; rfl
  have s1 : DetStep B img ⟨c1, ram⟩ ⟨c2, ram⟩ := by
    refine detStep_of (by show (0x800210a0 : Word).getLsbD 0 = false; decide) f800210a0 fun o => ?_
    rw [exec_opimm]
    have : c1.get 9 = c.get 9 := by simp [c1, Core.wr_get_ne]
    rw [this]; rfl
  have s2 : DetStep B img ⟨c2, ram⟩ ⟨c3, r1⟩ := by
    refine detStep_of (by show (0x800210a4 : Word).getLsbD 0 = false; decide) f800210a4 fun o => ?_
    rw [exec_store]
    have e9 : c2.get 9 = c.get 9 := by simp [c2, c1, Core.wr_get_ne]
    have e12 : c2.get 12 = v := by simp [c2, c1, Core.wr_get_ne, Core.wr_get_self]
    rw [e9, e12, interp_store_ram (w := .b) (a := c.get 9 + 0xffffffff#32) o
      (by simp only [Width.bytes, Nat.mod_one]) hd, copyByte]; rfl
  have s3 : DetStep B img ⟨c3, r1⟩ ⟨c4, r1⟩ := by
    refine detStep_of (by show (0x800210a8 : Word).getLsbD 0 = false; decide) f800210a8 fun o => ?_
    rw [exec_opimm]
    have : c3.get 16 = c.get 16 := by simp [c3, c2, c1, Core.wr_get_ne]
    rw [this]; rfl
  have s4 : DetStep B img ⟨c4, r1⟩ ⟨bwdBody c ram, r1⟩ := by
    refine detStep_of (by show (0x800210aa : Word).getLsbD 0 = false; decide) f800210aa fun o => ?_
    rw [exec_op]
    have : c4.get 13 = c.get 9 + 0xffffffff#32 := by simp [c4, c3, c2, c1, Core.wr_get_ne, Core.wr_get_self]
    rw [this, Core.get_zero]; rfl
  exact .step hq s0 (.step q1 s1 (.step q2 s2 (.step q3 s3 (.single q4 s4))))

/-- The backward byte loop: from 0x8002109c with `s1 = a1 + (k+1)`, it
    copies `k+1` bytes downward (reading from `a6` down, writing from
    `s1 - 1` down) and falls through to the epilogue. -/
theorem bwd_loop : ∀ (k : Nat) (c : Core) (ram : Word → BitVec 8),
    c.pc = 0x8002109c → Quiet c → c.get 9 = c.get 11 + BitVec.ofNat 32 (k + 1) →
    (c.get 11).toNat + (k + 1) < 2 ^ 32 → k ≤ (c.get 16).toNat →
    B.inRam (c.get 11) (k + 1) = true → B.inRam (c.get 16 - BitVec.ofNat 32 k) (k + 1) = true →
    ∃ n c', QRun B img n ⟨c, ram⟩ ⟨c', bwd ram (c.get 16) (c.get 9) (k + 1)⟩ ∧
      c'.pc = 0x800210b0 ∧ c'.sameCsr c ∧
      ∀ r : Reg, r ≠ 9 → r ≠ 12 → r ≠ 13 → r ≠ 16 → c'.get r = c.get r := by
  intro k
  induction k with
  | zero =>
    intro c ram hpc hq h9 hlo hp hd hs
    have hs0 : B.inRam (c.get 16) 1 = true := by
      have := inRam_one hs; rwa [show c.get 16 - BitVec.ofNat 32 0 = c.get 16 by bv_omega] at this
    have hd0 : B.inRam (c.get 9 + 0xffffffff#32) 1 = true := by
      rw [h9, show c.get 11 + BitVec.ofNat 32 (0 + 1) + 0xffffffff#32 = c.get 11 by bv_omega]
      exact inRam_one hd
    have hb := bwd_body c ram hpc hq hs0 hd0
    let c5 := bwdBody c ram
    have q5 : Quiet c5 := Quiet.of_sameCsr (bwdBody_sameCsr c ram) hq
    let r1 := ramPut ram (c.get 9 + 0xffffffff#32) (ram (c.get 16))
    have s5 : DetStep B img ⟨c5, r1⟩ ⟨c5.goto 0x800210b0, r1⟩ := by
      refine detStep_of (by show (0x800210ac : Word).getLsbD 0 = false; decide) f800210ac fun o => ?_
      rw [exec_branch]
      have e11 : c5.get 11 = c.get 11 := by simp [c5, bwdBody, Core.wr_get_ne]
      have e13 : c5.get 13 = c.get 9 + 0xffffffff#32 := by simp [c5, bwdBody, Core.wr_get_ne, Core.wr_get_self]
      have hnt : (c.get 11).ult (c.get 9 + 0xffffffff#32) = false := by
        rw [h9]; simp only [BitVec.ult, decide_eq_false_iff_not]; bv_omega
      rw [e11, e13]; simp only [taken, hnt, Bool.false_eq_true, if_false]; rfl
    refine ⟨6, c5.goto 0x800210b0, ?_, rfl, ?_, ?_⟩
    · have := hb.trans (.single q5 s5)
      simpa [bwd] using this
    · exact (Core.sameCsr_goto _ _).trans (bwdBody_sameCsr c ram)
    · intro r a b d e; simp only [Core.goto_get]; exact bwdBody_get c ram r a b d e
  | succ k ih =>
    intro c ram hpc hq h9 hlo hp hd hs
    have hsrc : B.inRam (c.get 16) 1 = true := by
      have := inRam_byte (i := k + 1) hs (by omega)
      rwa [show c.get 16 - BitVec.ofNat 32 (k + 1) + BitVec.ofNat 32 (k + 1) = c.get 16 by bv_omega] at this
    have hdst : B.inRam (c.get 9 + 0xffffffff#32) 1 = true := by
      have := inRam_byte (i := k + 1) hd (by omega)
      rwa [show c.get 11 + BitVec.ofNat 32 (k + 1) = c.get 9 + 0xffffffff#32 by rw [h9]; bv_omega] at this
    have hb := bwd_body c ram hpc hq hsrc hdst
    let c5 := bwdBody c ram
    have cs5 : c5.sameCsr c := bwdBody_sameCsr c ram
    have q5 : Quiet c5 := Quiet.of_sameCsr cs5 hq
    let r1 := ramPut ram (c.get 9 + 0xffffffff#32) (ram (c.get 16))
    have s5 : DetStep B img ⟨c5, r1⟩ ⟨c5.goto 0x8002109c, r1⟩ := by
      refine detStep_of (by show (0x800210ac : Word).getLsbD 0 = false; decide) f800210ac fun o => ?_
      rw [exec_branch]
      have e11 : c5.get 11 = c.get 11 := by simp [c5, bwdBody, Core.wr_get_ne]
      have e13 : c5.get 13 = c.get 9 + 0xffffffff#32 := by simp [c5, bwdBody, Core.wr_get_ne, Core.wr_get_self]
      have ht : (c.get 11).ult (c.get 9 + 0xffffffff#32) = true := by
        rw [h9]; simp only [BitVec.ult, decide_eq_true_iff]; bv_omega
      rw [e11, e13]; simp only [taken, ht, if_true]
      have hp5 : c5.pc + 0xfffffff0#32 = 0x8002109c := by
        rw [show c5.pc = 0x800210ac from rfl]; decide
      rw [hp5, jump_ok _ _ (by decide)]; rfl
    have q6 : Quiet (c5.goto 0x8002109c) := Quiet.of_sameCsr (Core.sameCsr_goto _ _) q5
    have g11 : (c5.goto 0x8002109c).get 11 = c.get 11 := by simp [c5, bwdBody, Core.wr_get_ne]
    have g16 : (c5.goto 0x8002109c).get 16 = c.get 16 + 0xffffffff#32 := by
      simp [c5, bwdBody, Core.wr_get_ne, Core.wr_get_self]
    have g9 : (c5.goto 0x8002109c).get 9 = c.get 9 + 0xffffffff#32 := by
      simp [c5, bwdBody, Core.wr_get_self, alu]
    obtain ⟨n, c', hr, hpc', hcs, hfr⟩ := ih (c5.goto 0x8002109c) r1 rfl q6
      (by rw [g9, g11, h9]; bv_omega) (by rw [g11]; omega) (by rw [g16]; bv_omega)
      (by rw [g11]; exact inRam_pred hd)
      (by rw [g16, show c.get 16 + 0xffffffff#32 - BitVec.ofNat 32 k = c.get 16 - BitVec.ofNat 32 (k + 1) by
            bv_omega]; exact inRam_pred hs)
    refine ⟨5 + 1 + n, c', ?_, hpc', ?_, ?_⟩
    · rw [g16, g9] at hr
      have e : bwd ram (c.get 16) (c.get 9) (k + 1 + 1) =
          bwd r1 (c.get 16 + 0xffffffff#32) (c.get 9 + 0xffffffff#32) (k + 1) := by simp only [bwd]; rfl
      rw [e]
      exact (hb.trans (.single q5 s5)).trans hr
    · exact hcs.trans ((Core.sameCsr_goto _ _).trans cs5)
    · intro r a b d e
      rw [hfr r a b d e, Core.goto_get]; exact bwdBody_get c ram r a b d e

end E5R.Rmk
