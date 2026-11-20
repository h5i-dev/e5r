/-
  The loops of the emitted memmove's n ≥ 16 backward path (pinned RMK
  image), as quiet runs that compute `bwd` / `wordsB` (Copy.lean).

  Original e5r code, Apache-2.0.

    head  0x80020dd4: lbu s0,0(a5); addi a4,a3,-1; sb s0,-1(a3); addi a5,a5,-1;
          mv a3,a4; bltu t2,a4,0x80020dd4             (falls to 0x80020de8)
    words 0x80020ea8: lw a3,0(a1); addi a4,a2,-4; sw a3,-4(a2); addi a1,a1,-4;
          mv a2,a4; bltu t3,a4,0x80020ea8; j 0x80021088
-/
import Projects.rmk.MemmoveLoops

set_option maxRecDepth 100000

namespace E5R.Rmk
open E5R E5R.Rmk.MemmoveFetch

/-! ## Backward head loop -/

def bheadBody (c : Core) (ram : Word → BitVec 8) : Core :=
  ((((c.wr 8 (extend .b false (ramRead ram (c.get 15) .b)) 0x80020dd8).wr 14 (c.get 13 + 0xffffffff#32)
    0x80020ddc).goto 0x80020de0).wr 15 (c.get 15 + 0xffffffff#32) 0x80020de2).wr 13
    (alu .add 0 (c.get 13 + 0xffffffff#32)) 0x80020de4

theorem bheadBody_sameCsr (c : Core) (ram) : (bheadBody c ram).sameCsr c :=
  (Core.sameCsr_wr _ _ _ _).trans ((Core.sameCsr_wr _ _ _ _).trans ((Core.sameCsr_goto _ _).trans
    ((Core.sameCsr_wr _ _ _ _).trans (Core.sameCsr_wr _ _ _ _))))

theorem bheadBody_get (c : Core) (ram) (r : Reg) (h8 : r ≠ 8) (h13 : r ≠ 13) (h14 : r ≠ 14)
    (h15 : r ≠ 15) : (bheadBody c ram).get r = c.get r := by
  simp [bheadBody, Core.wr_get_ne, h8, h13, h14, h15]

theorem bhead_body (c : Core) (ram : Word → BitVec 8) (hpc : c.pc = 0x80020dd4) (hq : Quiet c)
    (hs : B.inRam (c.get 15) 1 = true) (hd : B.inRam (c.get 13 + 0xffffffff#32) 1 = true) :
    QRun B img 5 ⟨c, ram⟩ ⟨bheadBody c ram, ramPut ram (c.get 13 + 0xffffffff#32) (ram (c.get 15))⟩ := by
  let v := extend .b false (ramRead ram (c.get 15) .b)
  let c1 := c.wr 8 v 0x80020dd8
  let c2 := c1.wr 14 (c.get 13 + 0xffffffff#32) 0x80020ddc
  let c3 := c2.goto 0x80020de0
  let c4 := c3.wr 15 (c.get 15 + 0xffffffff#32) 0x80020de2
  let r1 := ramPut ram (c.get 13 + 0xffffffff#32) (ram (c.get 15))
  have q1 : Quiet c1 := Quiet.of_sameCsr (Core.sameCsr_wr _ _ _ _) hq
  have q2 : Quiet c2 := Quiet.of_sameCsr (Core.sameCsr_wr _ _ _ _) q1
  have q3 : Quiet c3 := Quiet.of_sameCsr (Core.sameCsr_goto _ _) q2
  have q4 : Quiet c4 := Quiet.of_sameCsr (Core.sameCsr_wr _ _ _ _) q3
  have s0 : DetStep B img ⟨c, ram⟩ ⟨c1, ram⟩ := by
    refine detStep_of (by rw [hpc]; decide) (by rw [hpc]; exact f80020dd4) fun o => ?_
    rw [exec_load, BitVec.add_zero, interp_load_ram o (by simp only [Width.bytes, Nat.mod_one]) hs, hpc]; rfl
  have s1 : DetStep B img ⟨c1, ram⟩ ⟨c2, ram⟩ := by
    refine detStep_of (by show (0x80020dd8 : Word).getLsbD 0 = false; decide) f80020dd8 fun o => ?_
    rw [exec_opimm, show c1.get 13 = c.get 13 by simp [c1, Core.wr_get_ne]]; rfl
  have s2 : DetStep B img ⟨c2, ram⟩ ⟨c3, r1⟩ := by
    refine detStep_of (by show (0x80020ddc : Word).getLsbD 0 = false; decide) f80020ddc fun o => ?_
    rw [exec_store, show c2.get 13 = c.get 13 by simp [c2, c1, Core.wr_get_ne],
      show c2.get 8 = v by simp [c2, c1, Core.wr_get_ne, Core.wr_get_self],
      interp_store_ram (w := .b) (a := c.get 13 + 0xffffffff#32) o
        (by simp only [Width.bytes, Nat.mod_one]) hd, copyByte]; rfl
  have s3 : DetStep B img ⟨c3, r1⟩ ⟨c4, r1⟩ := by
    refine detStep_of (by show (0x80020de0 : Word).getLsbD 0 = false; decide) f80020de0 fun o => ?_
    rw [exec_opimm, show c3.get 15 = c.get 15 by simp [c3, c2, c1, Core.wr_get_ne]]; rfl
  have s4 : DetStep B img ⟨c4, r1⟩ ⟨bheadBody c ram, r1⟩ := by
    refine detStep_of (by show (0x80020de2 : Word).getLsbD 0 = false; decide) f80020de2 fun o => ?_
    rw [exec_op, Core.get_zero,
      show c4.get 14 = c.get 13 + 0xffffffff#32 by simp [c4, c3, c2, c1, Core.wr_get_ne, Core.wr_get_self]]; rfl
  exact .step hq s0 (.step q1 s1 (.step q2 s2 (.step q3 s3 (.single q4 s4))))

/-- The backward head loop: `k+1` bytes from the top, down to `t2`, falls to 0x80020de8. -/
theorem bhead_loop : ∀ (k : Nat) (c : Core) (ram : Word → BitVec 8),
    c.pc = 0x80020dd4 → Quiet c → c.get 13 = c.get 7 + BitVec.ofNat 32 (k + 1) →
    (c.get 7).toNat + (k + 1) < 2 ^ 32 → k ≤ (c.get 15).toNat →
    B.inRam (c.get 7) (k + 1) = true → B.inRam (c.get 15 - BitVec.ofNat 32 k) (k + 1) = true →
    ∃ n c', QRun B img n ⟨c, ram⟩ ⟨c', bwd ram (c.get 15) (c.get 13) (k + 1)⟩ ∧
      c'.pc = 0x80020de8 ∧ c'.sameCsr c ∧
      ∀ r : Reg, r ≠ 8 → r ≠ 13 → r ≠ 14 → r ≠ 15 → c'.get r = c.get r := by
  intro k
  induction k with
  | zero =>
    intro c ram hpc hq h13 hlo hp hd hs
    have hs0 : B.inRam (c.get 15) 1 = true := by
      have := inRam_one hs; rwa [show c.get 15 - BitVec.ofNat 32 0 = c.get 15 by bv_omega] at this
    have hd0 : B.inRam (c.get 13 + 0xffffffff#32) 1 = true := by
      rw [h13, show c.get 7 + BitVec.ofNat 32 (0 + 1) + 0xffffffff#32 = c.get 7 by bv_omega]
      exact inRam_one hd
    have hb := bhead_body c ram hpc hq hs0 hd0
    let c5 := bheadBody c ram
    have q5 : Quiet c5 := Quiet.of_sameCsr (bheadBody_sameCsr c ram) hq
    let r1 := ramPut ram (c.get 13 + 0xffffffff#32) (ram (c.get 15))
    have s5 : DetStep B img ⟨c5, r1⟩ ⟨c5.goto 0x80020de8, r1⟩ := by
      refine detStep_of (by show (0x80020de4 : Word).getLsbD 0 = false; decide) f80020de4 fun o => ?_
      rw [exec_branch]
      have e7 : c5.get 7 = c.get 7 := by simp [c5, bheadBody, Core.wr_get_ne]
      have e14 : c5.get 14 = c.get 13 + 0xffffffff#32 := by
        simp [c5, bheadBody, Core.wr_get_ne, Core.wr_get_self]
      have hnt : (c.get 7).ult (c.get 13 + 0xffffffff#32) = false := by
        rw [h13]; simp only [BitVec.ult, decide_eq_false_iff_not]; bv_omega
      rw [e7, e14]; simp only [taken, hnt, Bool.false_eq_true, ite_false]; rfl
    refine ⟨6, c5.goto 0x80020de8, ?_, rfl, (Core.sameCsr_goto _ _).trans (bheadBody_sameCsr c ram), ?_⟩
    · have := hb.trans (.single q5 s5)
      simpa [bwd] using this
    · intro r a b d e; simp only [Core.goto_get]; exact bheadBody_get c ram r a b d e
  | succ k ih =>
    intro c ram hpc hq h13 hlo hp hd hs
    have hsrc : B.inRam (c.get 15) 1 = true := by
      have := inRam_byte (i := k + 1) hs (by omega)
      rwa [show c.get 15 - BitVec.ofNat 32 (k + 1) + BitVec.ofNat 32 (k + 1) = c.get 15 by bv_omega] at this
    have hdst : B.inRam (c.get 13 + 0xffffffff#32) 1 = true := by
      have := inRam_byte (i := k + 1) hd (by omega)
      rwa [show c.get 7 + BitVec.ofNat 32 (k + 1) = c.get 13 + 0xffffffff#32 by rw [h13]; bv_omega] at this
    have hb := bhead_body c ram hpc hq hsrc hdst
    let c5 := bheadBody c ram
    have cs5 : c5.sameCsr c := bheadBody_sameCsr c ram
    have q5 : Quiet c5 := Quiet.of_sameCsr cs5 hq
    let r1 := ramPut ram (c.get 13 + 0xffffffff#32) (ram (c.get 15))
    have s5 : DetStep B img ⟨c5, r1⟩ ⟨c5.goto 0x80020dd4, r1⟩ := by
      refine detStep_of (by show (0x80020de4 : Word).getLsbD 0 = false; decide) f80020de4 fun o => ?_
      rw [exec_branch]
      have e7 : c5.get 7 = c.get 7 := by simp [c5, bheadBody, Core.wr_get_ne]
      have e14 : c5.get 14 = c.get 13 + 0xffffffff#32 := by
        simp [c5, bheadBody, Core.wr_get_ne, Core.wr_get_self]
      have ht : (c.get 7).ult (c.get 13 + 0xffffffff#32) = true := by
        rw [h13]; simp only [BitVec.ult, decide_eq_true_iff]; bv_omega
      rw [e7, e14]; simp only [taken, ht, ite_true]
      have hp5 : c5.pc + 0xfffffff0#32 = 0x80020dd4 := by
        rw [show c5.pc = 0x80020de4 from rfl]; decide
      rw [hp5, jump_ok _ _ (by decide)]; rfl
    have q6 : Quiet (c5.goto 0x80020dd4) := Quiet.of_sameCsr (Core.sameCsr_goto _ _) q5
    have g7 : (c5.goto 0x80020dd4).get 7 = c.get 7 := by simp [c5, bheadBody, Core.wr_get_ne]
    have g15 : (c5.goto 0x80020dd4).get 15 = c.get 15 + 0xffffffff#32 := by
      simp [c5, bheadBody, Core.wr_get_ne, Core.wr_get_self]
    have g13 : (c5.goto 0x80020dd4).get 13 = c.get 13 + 0xffffffff#32 := by
      simp [c5, bheadBody, Core.wr_get_self, alu]
    obtain ⟨n, c', hr, hpc', hcs, hfr⟩ := ih (c5.goto 0x80020dd4) r1 rfl q6
      (by rw [g13, g7, h13]; bv_omega) (by rw [g7]; omega) (by rw [g15]; bv_omega)
      (by rw [g7]; exact inRam_pred hd)
      (by rw [g15, show c.get 15 + 0xffffffff#32 - BitVec.ofNat 32 k = c.get 15 - BitVec.ofNat 32 (k + 1) by
            bv_omega]; exact inRam_pred hs)
    refine ⟨5 + 1 + n, c', ?_, hpc', hcs.trans ((Core.sameCsr_goto _ _).trans cs5), ?_⟩
    · rw [g15, g13] at hr
      have e : bwd ram (c.get 15) (c.get 13) (k + 1 + 1) =
          bwd r1 (c.get 15 + 0xffffffff#32) (c.get 13 + 0xffffffff#32) (k + 1) := by simp only [bwd]; rfl
      rw [e]
      exact (hb.trans (.single q5 s5)).trans hr
    · intro r a b d e
      rw [hfr r a b d e, Core.goto_get]; exact bheadBody_get c ram r a b d e

/-! ## Backward word loop -/

def bwordBody (c : Core) (ram : Word → BitVec 8) : Core :=
  ((((c.wr 13 (ramRead ram (c.get 11) .w) 0x80020eaa).wr 14 (c.get 12 + 0xfffffffc#32) 0x80020eae).goto
    0x80020eb2).wr 11 (c.get 11 + 0xfffffffc#32) 0x80020eb4).wr 12 (alu .add 0 (c.get 12 + 0xfffffffc#32))
    0x80020eb6

theorem bwordBody_sameCsr (c : Core) (ram) : (bwordBody c ram).sameCsr c :=
  (Core.sameCsr_wr _ _ _ _).trans ((Core.sameCsr_wr _ _ _ _).trans ((Core.sameCsr_goto _ _).trans
    ((Core.sameCsr_wr _ _ _ _).trans (Core.sameCsr_wr _ _ _ _))))

theorem bwordBody_get (c : Core) (ram) (r : Reg) (h11 : r ≠ 11) (h12 : r ≠ 12) (h13 : r ≠ 13)
    (h14 : r ≠ 14) : (bwordBody c ram).get r = c.get r := by
  simp [bwordBody, Core.wr_get_ne, h11, h12, h13, h14]

theorem bword_body (c : Core) (ram : Word → BitVec 8) (hpc : c.pc = 0x80020ea8) (hq : Quiet c)
    (has : (c.get 11).toNat % 4 = 0) (had : (c.get 12 + 0xfffffffc#32).toNat % 4 = 0)
    (hs : B.inRam (c.get 11) 4 = true) (hd : B.inRam (c.get 12 + 0xfffffffc#32) 4 = true) :
    QRun B img 5 ⟨c, ram⟩ ⟨bwordBody c ram,
      ramWrite ram (c.get 12 + 0xfffffffc#32) (ramRead ram (c.get 11) .w) .w⟩ := by
  let v := ramRead ram (c.get 11) .w
  let c1 := c.wr 13 v 0x80020eaa
  let c2 := c1.wr 14 (c.get 12 + 0xfffffffc#32) 0x80020eae
  let c3 := c2.goto 0x80020eb2
  let c4 := c3.wr 11 (c.get 11 + 0xfffffffc#32) 0x80020eb4
  let r1 := ramWrite ram (c.get 12 + 0xfffffffc#32) v .w
  have q1 : Quiet c1 := Quiet.of_sameCsr (Core.sameCsr_wr _ _ _ _) hq
  have q2 : Quiet c2 := Quiet.of_sameCsr (Core.sameCsr_wr _ _ _ _) q1
  have q3 : Quiet c3 := Quiet.of_sameCsr (Core.sameCsr_goto _ _) q2
  have q4 : Quiet c4 := Quiet.of_sameCsr (Core.sameCsr_wr _ _ _ _) q3
  have s0 : DetStep B img ⟨c, ram⟩ ⟨c1, ram⟩ := by
    refine detStep_of (by rw [hpc]; decide) (by rw [hpc]; exact f80020ea8) fun o => ?_
    rw [exec_load, BitVec.add_zero, interp_load_ram (w := .w) o has hs, hpc]; rfl
  have s1 : DetStep B img ⟨c1, ram⟩ ⟨c2, ram⟩ := by
    refine detStep_of (by show (0x80020eaa : Word).getLsbD 0 = false; decide) f80020eaa fun o => ?_
    rw [exec_opimm, show c1.get 12 = c.get 12 by simp [c1, Core.wr_get_ne]]; rfl
  have s2 : DetStep B img ⟨c2, ram⟩ ⟨c3, r1⟩ := by
    refine detStep_of (by show (0x80020eae : Word).getLsbD 0 = false; decide) f80020eae fun o => ?_
    rw [exec_store, show c2.get 12 = c.get 12 by simp [c2, c1, Core.wr_get_ne],
      show c2.get 13 = v by simp [c2, c1, Core.wr_get_ne, Core.wr_get_self],
      interp_store_ram (w := .w) (a := c.get 12 + 0xfffffffc#32) o had hd]; rfl
  have s3 : DetStep B img ⟨c3, r1⟩ ⟨c4, r1⟩ := by
    refine detStep_of (by show (0x80020eb2 : Word).getLsbD 0 = false; decide) f80020eb2 fun o => ?_
    rw [exec_opimm, show c3.get 11 = c.get 11 by simp [c3, c2, c1, Core.wr_get_ne]]; rfl
  have s4 : DetStep B img ⟨c4, r1⟩ ⟨bwordBody c ram, r1⟩ := by
    refine detStep_of (by show (0x80020eb4 : Word).getLsbD 0 = false; decide) f80020eb4 fun o => ?_
    rw [exec_op, Core.get_zero,
      show c4.get 14 = c.get 12 + 0xfffffffc#32 by simp [c4, c3, c2, c1, Core.wr_get_ne, Core.wr_get_self]]; rfl
  exact .step hq s0 (.step q1 s1 (.step q2 s2 (.step q3 s3 (.single q4 s4))))

/-- The backward word loop: `j+1` words down from `a2 = t3 + 4(j+1)`, source word at `a1`
    and below; then the jump to 0x80021088. -/
theorem bword_loop : ∀ (j : Nat) (c : Core) (ram : Word → BitVec 8),
    c.pc = 0x80020ea8 → Quiet c → c.get 12 = c.get 28 + BitVec.ofNat 32 (4 * (j + 1)) →
    (c.get 28).toNat + 4 * (j + 1) < 2 ^ 32 → 4 * j ≤ (c.get 11).toNat →
    (c.get 11).toNat % 4 = 0 → (c.get 28).toNat % 4 = 0 →
    B.inRam (c.get 11 - BitVec.ofNat 32 (4 * j)) (4 * (j + 1)) = true →
    B.inRam (c.get 28) (4 * (j + 1)) = true →
    ∃ n c', QRun B img n ⟨c, ram⟩ ⟨c', wordsB ram (c.get 11) (c.get 12) (j + 1)⟩ ∧
      c'.pc = 0x80021088 ∧ c'.sameCsr c ∧
      ∀ r : Reg, r ≠ 11 → r ≠ 12 → r ≠ 13 → r ≠ 14 → c'.get r = c.get r := by
  intro j
  induction j with
  | zero =>
    intro c ram hpc hq h12 hlim hp has had hs hd
    have hs4 : B.inRam (c.get 11) 4 = true := by
      rw [B_ram] at *; simp only [Nat.mul_zero, BitVec.sub_zero] at hs; omega
    have hd4 : B.inRam (c.get 12 + 0xfffffffc#32) 4 = true := by
      rw [h12, show c.get 28 + BitVec.ofNat 32 (4 * (0 + 1)) + 0xfffffffc#32 = c.get 28 by bv_omega]
      simpa using hd
    have hb := bword_body c ram hpc hq has
      (by rw [h12, show c.get 28 + BitVec.ofNat 32 (4 * (0 + 1)) + 0xfffffffc#32 = c.get 28 by bv_omega]
          exact had) hs4 hd4
    let c5 := bwordBody c ram
    have q5 : Quiet c5 := Quiet.of_sameCsr (bwordBody_sameCsr c ram) hq
    let r1 := ramWrite ram (c.get 12 + 0xfffffffc#32) (ramRead ram (c.get 11) .w) .w
    have s5 : DetStep B img ⟨c5, r1⟩ ⟨c5.goto 0x80020eba, r1⟩ := by
      refine detStep_of (by show (0x80020eb6 : Word).getLsbD 0 = false; decide) f80020eb6 fun o => ?_
      rw [exec_branch]
      have e28 : c5.get 28 = c.get 28 := by simp [c5, bwordBody, Core.wr_get_ne]
      have e14 : c5.get 14 = c.get 12 + 0xfffffffc#32 := by
        simp [c5, bwordBody, Core.wr_get_ne, Core.wr_get_self]
      have hnt : (c.get 28).ult (c.get 12 + 0xfffffffc#32) = false := by
        rw [h12]; simp only [BitVec.ult, decide_eq_false_iff_not]; bv_omega
      rw [e28, e14]; simp only [taken, hnt, Bool.false_eq_true, ite_false]; rfl
    have q6 : Quiet (c5.goto 0x80020eba) := Quiet.of_sameCsr (Core.sameCsr_goto _ _) q5
    have s6 : DetStep B img ⟨c5.goto 0x80020eba, r1⟩ ⟨c5.goto 0x80021088, r1⟩ := by
      refine detStep_of (by show (0x80020eba : Word).getLsbD 0 = false; decide) f80020eba fun o => ?_
      rw [exec_jal, Core.set_zero,
        show (c5.goto 0x80020eba).pc + 0x1ce#32 = 0x80021088 by
          rw [show (c5.goto 0x80020eba).pc = 0x80020eba from rfl]; decide,
        jump_ok _ _ (by decide)]; rfl
    refine ⟨7, c5.goto 0x80021088, ?_, rfl, (Core.sameCsr_goto _ _).trans (bwordBody_sameCsr c ram), ?_⟩
    · have := hb.trans (.step q5 s5 (.single q6 s6))
      simpa [wordsB] using this
    · intro r a b d e; simp only [Core.goto_get]; exact bwordBody_get c ram r a b d e
  | succ j ih =>
    intro c ram hpc hq h12 hlim hp has had hs hd
    have hs4 : B.inRam (c.get 11) 4 = true := by rw [B_ram] at *; bv_omega
    have hd4 : B.inRam (c.get 12 + 0xfffffffc#32) 4 = true := by rw [B_ram] at *; rw [h12]; bv_omega
    have hb := bword_body c ram hpc hq has (by rw [h12]; bv_omega) hs4 hd4
    let c5 := bwordBody c ram
    have cs5 : c5.sameCsr c := bwordBody_sameCsr c ram
    have q5 : Quiet c5 := Quiet.of_sameCsr cs5 hq
    let r1 := ramWrite ram (c.get 12 + 0xfffffffc#32) (ramRead ram (c.get 11) .w) .w
    have s5 : DetStep B img ⟨c5, r1⟩ ⟨c5.goto 0x80020ea8, r1⟩ := by
      refine detStep_of (by show (0x80020eb6 : Word).getLsbD 0 = false; decide) f80020eb6 fun o => ?_
      rw [exec_branch]
      have e28 : c5.get 28 = c.get 28 := by simp [c5, bwordBody, Core.wr_get_ne]
      have e14 : c5.get 14 = c.get 12 + 0xfffffffc#32 := by
        simp [c5, bwordBody, Core.wr_get_ne, Core.wr_get_self]
      have ht : (c.get 28).ult (c.get 12 + 0xfffffffc#32) = true := by
        rw [h12]; simp only [BitVec.ult, decide_eq_true_iff]; bv_omega
      rw [e28, e14]; simp only [taken, ht, ite_true]
      have hp5 : c5.pc + 0xfffffff2#32 = 0x80020ea8 := by
        rw [show c5.pc = 0x80020eb6 from rfl]; decide
      rw [hp5, jump_ok _ _ (by decide)]; rfl
    have q6 : Quiet (c5.goto 0x80020ea8) := Quiet.of_sameCsr (Core.sameCsr_goto _ _) q5
    have g28 : (c5.goto 0x80020ea8).get 28 = c.get 28 := by simp [c5, bwordBody, Core.wr_get_ne]
    have g11 : (c5.goto 0x80020ea8).get 11 = c.get 11 + 0xfffffffc#32 := by
      simp [c5, bwordBody, Core.wr_get_ne, Core.wr_get_self]
    have g12 : (c5.goto 0x80020ea8).get 12 = c.get 12 + 0xfffffffc#32 := by
      simp [c5, bwordBody, Core.wr_get_self, alu]
    obtain ⟨n, c', hr, hpc', hcs, hfr⟩ := ih (c5.goto 0x80020ea8) r1 rfl q6
      (by rw [g12, g28, h12]; bv_omega) (by rw [g28]; omega) (by rw [g11]; bv_omega)
      (by rw [g11]; bv_omega) (by rw [g28]; exact had)
      (by rw [g11, B_ram] at *; constructor <;> bv_omega)
      (by rw [g28, B_ram] at *; constructor <;> bv_omega)
    refine ⟨5 + 1 + n, c', ?_, hpc', hcs.trans ((Core.sameCsr_goto _ _).trans cs5), ?_⟩
    · rw [g11, g12] at hr
      have e : wordsB ram (c.get 11) (c.get 12) (j + 1 + 1) =
          wordsB r1 (c.get 11 + 0xfffffffc#32) (c.get 12 + 0xfffffffc#32) (j + 1) := by simp only [wordsB]; rfl
      rw [e]
      exact (hb.trans (.single q5 s5)).trans hr
    · intro r a b d e
      rw [hfr r a b d e, Core.goto_get]; exact bwordBody_get c ram r a b d e

end E5R.Rmk
