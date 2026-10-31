/-
  The loops of the emitted memmove's n ≥ 16 forward path (pinned RMK
  image), as quiet runs that compute `fwd` / `words` (Copy.lean).

  Original e5r code, Apache-2.0.

    head  0x80020e3c: lbu s1,0(a4); addi a5,a5,-1; sb s1,0(a3); addi a3,a3,1;
          addi a4,a4,1; bnez a5,0x80020e3c        (falls to 0x80020e4c)
    words 0x80020ec2: lw a2,0(a1); sw a2,0(t5); addi t5,t5,4; addi a1,a1,4;
          bltu t5,a3,0x80020ec2;  j 0x80020fb6
-/
import Projects.rmk.MemmoveLoops

set_option maxRecDepth 100000

namespace E5R.Rmk
open E5R E5R.Rmk.MemmoveFetch

/-! ## Head byte loop -/

def headBody (c : Core) (ram : Word → BitVec 8) (k : Nat) : Core :=
  ((((c.wr 9 (extend .b false (ramRead ram (c.get 14) .b)) 0x80020e40).wr 15 (BitVec.ofNat 32 k)
    0x80020e42).goto 0x80020e46).wr 13 (c.get 13 + 1) 0x80020e48).wr 14 (c.get 14 + 1) 0x80020e4a

theorem headBody_sameCsr (c : Core) (ram) (k : Nat) : (headBody c ram k).sameCsr c :=
  (Core.sameCsr_wr _ _ _ _).trans ((Core.sameCsr_wr _ _ _ _).trans ((Core.sameCsr_goto _ _).trans
    ((Core.sameCsr_wr _ _ _ _).trans (Core.sameCsr_wr _ _ _ _))))

theorem headBody_get (c : Core) (ram) (k : Nat) (r : Reg) (h9 : r ≠ 9) (h13 : r ≠ 13) (h14 : r ≠ 14)
    (h15 : r ≠ 15) : (headBody c ram k).get r = c.get r := by
  simp [headBody, Core.wr_get_ne, h9, h13, h14, h15]

theorem head_body (k : Nat) (c : Core) (ram : Word → BitVec 8) (hpc : c.pc = 0x80020e3c) (hq : Quiet c)
    (hk : c.get 15 = BitVec.ofNat 32 (k + 1)) (hs : B.inRam (c.get 14) 1 = true)
    (hd : B.inRam (c.get 13) 1 = true) :
    QRun B img 5 ⟨c, ram⟩ ⟨headBody c ram k, ramPut ram (c.get 13) (ram (c.get 14))⟩ := by
  let v := extend .b false (ramRead ram (c.get 14) .b)
  let c1 := c.wr 9 v 0x80020e40
  let c2 := c1.wr 15 (BitVec.ofNat 32 k) 0x80020e42
  let c3 := c2.goto 0x80020e46
  let c4 := c3.wr 13 (c.get 13 + 1) 0x80020e48
  let r1 := ramPut ram (c.get 13) (ram (c.get 14))
  have q1 : Quiet c1 := Quiet.of_sameCsr (Core.sameCsr_wr _ _ _ _) hq
  have q2 : Quiet c2 := Quiet.of_sameCsr (Core.sameCsr_wr _ _ _ _) q1
  have q3 : Quiet c3 := Quiet.of_sameCsr (Core.sameCsr_goto _ _) q2
  have q4 : Quiet c4 := Quiet.of_sameCsr (Core.sameCsr_wr _ _ _ _) q3
  have s0 : DetStep B img ⟨c, ram⟩ ⟨c1, ram⟩ := by
    refine detStep_of (by rw [hpc]; decide) (by rw [hpc]; exact f80020e3c) fun o => ?_
    rw [exec_load, BitVec.add_zero, interp_load_ram o (by simp only [Width.bytes, Nat.mod_one]) hs, hpc]; rfl
  have s1 : DetStep B img ⟨c1, ram⟩ ⟨c2, ram⟩ := by
    refine detStep_of (by show (0x80020e40 : Word).getLsbD 0 = false; decide) f80020e40 fun o => ?_
    rw [exec_opimm]
    have : c1.get 15 = BitVec.ofNat 32 (k + 1) := by simp [c1, Core.wr_get_ne, hk]
    rw [this]
    have e : alu .add (BitVec.ofNat 32 (k + 1)) 0xffffffff#32 = BitVec.ofNat 32 k := by
      simp only [alu]; bv_omega
    rw [e]; rfl
  have s2 : DetStep B img ⟨c2, ram⟩ ⟨c3, r1⟩ := by
    refine detStep_of (by show (0x80020e42 : Word).getLsbD 0 = false; decide) f80020e42 fun o => ?_
    rw [exec_store, BitVec.add_zero]
    have e13 : c2.get 13 = c.get 13 := by simp [c2, c1, Core.wr_get_ne]
    have e9 : c2.get 9 = v := by simp [c2, c1, Core.wr_get_ne, Core.wr_get_self]
    rw [e13, e9, interp_store_ram (w := .b) o (by simp only [Width.bytes, Nat.mod_one]) hd, copyByte]; rfl
  have s3 : DetStep B img ⟨c3, r1⟩ ⟨c4, r1⟩ := by
    refine detStep_of (by show (0x80020e46 : Word).getLsbD 0 = false; decide) f80020e46 fun o => ?_
    rw [exec_opimm]
    have : c3.get 13 = c.get 13 := by simp [c3, c2, c1, Core.wr_get_ne]
    rw [this]; rfl
  have s4 : DetStep B img ⟨c4, r1⟩ ⟨headBody c ram k, r1⟩ := by
    refine detStep_of (by show (0x80020e48 : Word).getLsbD 0 = false; decide) f80020e48 fun o => ?_
    rw [exec_opimm]
    have : c4.get 14 = c.get 14 := by simp [c4, c3, c2, c1, Core.wr_get_ne]
    rw [this]; rfl
  exact .step hq s0 (.step q1 s1 (.step q2 s2 (.step q3 s3 (.single q4 s4))))

/-- The head loop copies `k+1` bytes upward from `a4` to `a3` and falls to 0x80020e4c. -/
theorem head_loop : ∀ (k : Nat) (c : Core) (ram : Word → BitVec 8),
    c.pc = 0x80020e3c → Quiet c → c.get 15 = BitVec.ofNat 32 (k + 1) → k + 1 < 2 ^ 32 →
    B.inRam (c.get 14) (k + 1) = true → B.inRam (c.get 13) (k + 1) = true →
    ∃ n c', QRun B img n ⟨c, ram⟩ ⟨c', fwd ram (c.get 14) (c.get 13) (k + 1)⟩ ∧
      c'.pc = 0x80020e4c ∧ c'.sameCsr c ∧
      c'.get 13 = c.get 13 + BitVec.ofNat 32 (k + 1) ∧ c'.get 14 = c.get 14 + BitVec.ofNat 32 (k + 1) ∧
      ∀ r : Reg, r ≠ 9 → r ≠ 13 → r ≠ 14 → r ≠ 15 → c'.get r = c.get r := by
  intro k
  induction k with
  | zero =>
    intro c ram hpc hq hk _ hs hd
    have hb := head_body 0 c ram hpc hq hk (inRam_one hs) (inRam_one hd)
    let c5 := headBody c ram 0
    have q5 : Quiet c5 := Quiet.of_sameCsr (headBody_sameCsr c ram 0) hq
    let r1 := ramPut ram (c.get 13) (ram (c.get 14))
    have s5 : DetStep B img ⟨c5, r1⟩ ⟨c5.goto 0x80020e4c, r1⟩ := by
      refine detStep_of (by show (0x80020e4a : Word).getLsbD 0 = false; decide) f80020e4a fun o => ?_
      rw [exec_branch]
      have : c5.get 15 = BitVec.ofNat 32 0 := by simp [c5, headBody, Core.wr_get_ne, Core.wr_get_self]
      rw [this]; simp [taken]; rfl
    refine ⟨6, c5.goto 0x80020e4c, ?_, rfl, (Core.sameCsr_goto _ _).trans (headBody_sameCsr c ram 0), ?_, ?_, ?_⟩
    · have := hb.trans (.single q5 s5)
      simpa [fwd] using this
    · simp [c5, headBody, Core.wr_get_ne, Core.wr_get_self]
    · simp [c5, headBody, Core.wr_get_self]
    · intro r a b d e; simp only [Core.goto_get]; exact headBody_get c ram 0 r a b d e
  | succ k ih =>
    intro c ram hpc hq hk hk32 hs hd
    have hb := head_body (k + 1) c ram hpc hq hk (inRam_one hs) (inRam_one hd)
    let c5 := headBody c ram (k + 1)
    have cs5 : c5.sameCsr c := headBody_sameCsr c ram (k + 1)
    have q5 : Quiet c5 := Quiet.of_sameCsr cs5 hq
    let r1 := ramPut ram (c.get 13) (ram (c.get 14))
    have s5 : DetStep B img ⟨c5, r1⟩ ⟨c5.goto 0x80020e3c, r1⟩ := by
      refine detStep_of (by show (0x80020e4a : Word).getLsbD 0 = false; decide) f80020e4a fun o => ?_
      rw [exec_branch]
      have : c5.get 15 = BitVec.ofNat 32 (k + 1) := by simp [c5, headBody, Core.wr_get_ne, Core.wr_get_self]
      have hne : (BitVec.ofNat 32 (k + 1) != (0 : Word)) = true := by
        simp only [bne_iff_ne, ne_eq]; bv_omega
      rw [this]; simp only [taken, Core.get_zero, hne, if_true]
      have hp5 : c5.pc + 0xfffffff2#32 = 0x80020e3c := by
        rw [show c5.pc = 0x80020e4a from rfl]; decide
      rw [hp5, jump_ok _ _ (by decide)]; rfl
    have q6 : Quiet (c5.goto 0x80020e3c) := Quiet.of_sameCsr (Core.sameCsr_goto _ _) q5
    have g14 : (c5.goto 0x80020e3c).get 14 = c.get 14 + 1 := by simp [c5, headBody, Core.wr_get_self]
    have g13 : (c5.goto 0x80020e3c).get 13 = c.get 13 + 1 := by
      simp [c5, headBody, Core.wr_get_ne, Core.wr_get_self]
    have g15 : (c5.goto 0x80020e3c).get 15 = BitVec.ofNat 32 (k + 1) := by
      simp [c5, headBody, Core.wr_get_ne, Core.wr_get_self]
    obtain ⟨n, c', hr, hpc', hcs, h13, h14, hfr⟩ := ih (c5.goto 0x80020e3c) r1 rfl q6 g15 (by omega)
      (by rw [g14]; exact inRam_succ hs) (by rw [g13]; exact inRam_succ hd)
    refine ⟨5 + 1 + n, c', ?_, hpc', hcs.trans ((Core.sameCsr_goto _ _).trans cs5), ?_, ?_, ?_⟩
    · rw [g14, g13] at hr
      exact (hb.trans (.single q5 s5)).trans hr
    · rw [h13, g13]; bv_omega
    · rw [h14, g14]; bv_omega
    · intro r a b d e
      rw [hfr r a b d e, Core.goto_get]; exact headBody_get c ram (k + 1) r a b d e

/-! ## Aligned word loop -/

def wordBody (c : Core) (ram : Word → BitVec 8) : Core :=
  (((c.wr 12 (ramRead ram (c.get 11) .w) 0x80020ec4).goto 0x80020ec8).wr 30 (c.get 30 + 4) 0x80020eca).wr 11
    (c.get 11 + 4) 0x80020ecc

theorem wordBody_sameCsr (c : Core) (ram) : (wordBody c ram).sameCsr c :=
  (Core.sameCsr_wr _ _ _ _).trans ((Core.sameCsr_wr _ _ _ _).trans ((Core.sameCsr_goto _ _).trans
    (Core.sameCsr_wr _ _ _ _)))

theorem wordBody_get (c : Core) (ram) (r : Reg) (h11 : r ≠ 11) (h12 : r ≠ 12) (h30 : r ≠ 30) :
    (wordBody c ram).get r = c.get r := by
  simp [wordBody, Core.wr_get_ne, h11, h12, h30]

theorem word_body (c : Core) (ram : Word → BitVec 8) (hpc : c.pc = 0x80020ec2) (hq : Quiet c)
    (has : (c.get 11).toNat % 4 = 0) (had : (c.get 30).toNat % 4 = 0)
    (hs : B.inRam (c.get 11) 4 = true) (hd : B.inRam (c.get 30) 4 = true) :
    QRun B img 4 ⟨c, ram⟩ ⟨wordBody c ram, ramWrite ram (c.get 30) (ramRead ram (c.get 11) .w) .w⟩ := by
  let v := ramRead ram (c.get 11) .w
  let c1 := c.wr 12 v 0x80020ec4
  let c2 := c1.goto 0x80020ec8
  let c3 := c2.wr 30 (c.get 30 + 4) 0x80020eca
  let r1 := ramWrite ram (c.get 30) v .w
  have q1 : Quiet c1 := Quiet.of_sameCsr (Core.sameCsr_wr _ _ _ _) hq
  have q2 : Quiet c2 := Quiet.of_sameCsr (Core.sameCsr_goto _ _) q1
  have q3 : Quiet c3 := Quiet.of_sameCsr (Core.sameCsr_wr _ _ _ _) q2
  have s0 : DetStep B img ⟨c, ram⟩ ⟨c1, ram⟩ := by
    refine detStep_of (by rw [hpc]; decide) (by rw [hpc]; exact f80020ec2) fun o => ?_
    rw [exec_load, BitVec.add_zero, interp_load_ram (w := .w) o has hs, hpc]; rfl
  have s1 : DetStep B img ⟨c1, ram⟩ ⟨c2, r1⟩ := by
    refine detStep_of (by show (0x80020ec4 : Word).getLsbD 0 = false; decide) f80020ec4 fun o => ?_
    rw [exec_store, BitVec.add_zero]
    have e30 : c1.get 30 = c.get 30 := by simp [c1, Core.wr_get_ne]
    have e12 : c1.get 12 = v := by simp [c1, Core.wr_get_self]
    rw [e30, e12, interp_store_ram (w := .w) o had hd]; rfl
  have s2 : DetStep B img ⟨c2, r1⟩ ⟨c3, r1⟩ := by
    refine detStep_of (by show (0x80020ec8 : Word).getLsbD 0 = false; decide) f80020ec8 fun o => ?_
    rw [exec_opimm]
    have : c2.get 30 = c.get 30 := by simp [c2, c1, Core.wr_get_ne]
    rw [this]; rfl
  have s3 : DetStep B img ⟨c3, r1⟩ ⟨wordBody c ram, r1⟩ := by
    refine detStep_of (by show (0x80020eca : Word).getLsbD 0 = false; decide) f80020eca fun o => ?_
    rw [exec_opimm]
    have : c3.get 11 = c.get 11 := by simp [c3, c2, c1, Core.wr_get_ne]
    rw [this]; rfl
  exact .step hq s0 (.step q1 s1 (.step q2 s2 (.single q3 s3)))

theorem al_add4 {x : Word} (h : x.toNat % 4 = 0) (hx : x.toNat + 4 < 2 ^ 32) : (x + 4).toNat % 4 = 0 := by
  bv_omega

/-- The aligned word loop: `j+1` words from `a1` to `t5` (`a3 = t5 + 4(j+1)`), then `j` to 0x80020fb6. -/
theorem word_loop : ∀ (j : Nat) (c : Core) (ram : Word → BitVec 8),
    c.pc = 0x80020ec2 → Quiet c → c.get 13 = c.get 30 + BitVec.ofNat 32 (4 * (j + 1)) →
    (c.get 30).toNat + 4 * (j + 1) < 2 ^ 32 →
    (c.get 11).toNat % 4 = 0 → (c.get 30).toNat % 4 = 0 →
    B.inRam (c.get 11) (4 * (j + 1)) = true → B.inRam (c.get 30) (4 * (j + 1)) = true →
    ∃ n c', QRun B img n ⟨c, ram⟩ ⟨c', words ram (c.get 11) (c.get 30) (j + 1)⟩ ∧
      c'.pc = 0x80020fb6 ∧ c'.sameCsr c ∧
      ∀ r : Reg, r ≠ 11 → r ≠ 12 → r ≠ 30 → c'.get r = c.get r := by
  intro j
  induction j with
  | zero =>
    intro c ram hpc hq h13 hlim has had hs hd
    have hb := word_body c ram hpc hq has had (by simpa using hs) (by simpa using hd)
    let c4 := wordBody c ram
    have q4 : Quiet c4 := Quiet.of_sameCsr (wordBody_sameCsr c ram) hq
    let r1 := ramWrite ram (c.get 30) (ramRead ram (c.get 11) .w) .w
    have s4 : DetStep B img ⟨c4, r1⟩ ⟨c4.goto 0x80020ed0, r1⟩ := by
      refine detStep_of (by show (0x80020ecc : Word).getLsbD 0 = false; decide) f80020ecc fun o => ?_
      rw [exec_branch]
      have e30 : c4.get 30 = c.get 30 + 4 := by simp [c4, wordBody, Core.wr_get_ne, Core.wr_get_self]
      have e13 : c4.get 13 = c.get 13 := by simp [c4, wordBody, Core.wr_get_ne]
      have hnt : (c.get 30 + 4).ult (c.get 13) = false := by
        rw [h13]; simp only [BitVec.ult, decide_eq_false_iff_not]; bv_omega
      rw [e30, e13]; simp only [taken, hnt, Bool.false_eq_true, if_false]; rfl
    have q5 : Quiet (c4.goto 0x80020ed0) := Quiet.of_sameCsr (Core.sameCsr_goto _ _) q4
    have s5 : DetStep B img ⟨c4.goto 0x80020ed0, r1⟩ ⟨c4.goto 0x80020fb6, r1⟩ := by
      refine detStep_of (by show (0x80020ed0 : Word).getLsbD 0 = false; decide) f80020ed0 fun o => ?_
      rw [exec_jal, Core.set_zero,
        show (c4.goto 0x80020ed0).pc + 0xe6#32 = 0x80020fb6 by
          rw [show (c4.goto 0x80020ed0).pc = 0x80020ed0 from rfl]; decide,
        jump_ok _ _ (by decide)]; rfl
    refine ⟨6, c4.goto 0x80020fb6, ?_, rfl, (Core.sameCsr_goto _ _).trans (wordBody_sameCsr c ram), ?_⟩
    · have := hb.trans (.step q4 s4 (.single q5 s5))
      simpa [words] using this
    · intro r a b d; simp only [Core.goto_get]; exact wordBody_get c ram r a b d
  | succ j ih =>
    intro c ram hpc hq h13 hlim has had hs hd
    have hs4 : B.inRam (c.get 11) 4 = true := by rw [B_ram] at *; omega
    have hd4 : B.inRam (c.get 30) 4 = true := by rw [B_ram] at *; omega
    have hb := word_body c ram hpc hq has had hs4 hd4
    let c4 := wordBody c ram
    have cs4 : c4.sameCsr c := wordBody_sameCsr c ram
    have q4 : Quiet c4 := Quiet.of_sameCsr cs4 hq
    let r1 := ramWrite ram (c.get 30) (ramRead ram (c.get 11) .w) .w
    have s4 : DetStep B img ⟨c4, r1⟩ ⟨c4.goto 0x80020ec2, r1⟩ := by
      refine detStep_of (by show (0x80020ecc : Word).getLsbD 0 = false; decide) f80020ecc fun o => ?_
      rw [exec_branch]
      have e30 : c4.get 30 = c.get 30 + 4 := by simp [c4, wordBody, Core.wr_get_ne, Core.wr_get_self]
      have e13 : c4.get 13 = c.get 13 := by simp [c4, wordBody, Core.wr_get_ne]
      have ht : (c.get 30 + 4).ult (c.get 13) = true := by
        rw [h13]; simp only [BitVec.ult, decide_eq_true_iff]; bv_omega
      rw [e30, e13]; simp only [taken, ht, if_true]
      have hp : c4.pc + 0xfffffff6#32 = 0x80020ec2 := by rw [show c4.pc = 0x80020ecc from rfl]; decide
      rw [hp, jump_ok _ _ (by decide)]; rfl
    have q5 : Quiet (c4.goto 0x80020ec2) := Quiet.of_sameCsr (Core.sameCsr_goto _ _) q4
    have g11 : (c4.goto 0x80020ec2).get 11 = c.get 11 + 4 := by simp [c4, wordBody, Core.wr_get_self]
    have g30 : (c4.goto 0x80020ec2).get 30 = c.get 30 + 4 := by
      simp [c4, wordBody, Core.wr_get_ne, Core.wr_get_self]
    have g13 : (c4.goto 0x80020ec2).get 13 = c.get 13 := by simp [c4, wordBody, Core.wr_get_ne]
    obtain ⟨n, c', hr, hpc', hcs, hfr⟩ := ih (c4.goto 0x80020ec2) r1 rfl q5
      (by rw [g13, g30, h13]; bv_omega) (by rw [g30]; bv_omega)
      (by rw [g11]; bv_omega) (by rw [g30]; bv_omega)
      (by rw [g11, B_ram] at *; constructor <;> bv_omega) (by rw [g30, B_ram] at *; constructor <;> bv_omega)
    refine ⟨4 + 1 + n, c', ?_, hpc', hcs.trans ((Core.sameCsr_goto _ _).trans cs4), ?_⟩
    · rw [g11, g30] at hr
      exact (hb.trans (.single q4 s4)).trans hr
    · intro r a b d
      rw [hfr r a b d, Core.goto_get]; exact wordBody_get c ram r a b d

end E5R.Rmk
