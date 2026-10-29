/-
  memmove, backward direction (dst - src < n unsigned: dst inside the
  source, above it), n ≥ 16 (pinned RMK image): entry and top head bytes,
  the aligned word path, and the shared byte tail at 0x80021088.

  Original e5r code, Apache-2.0.

    0x80020dae  s1 = a0+a2; a3 = 16; a6 = a1+a2; bltu a2,a3 (small: not here)
    0x80020dbc  a7 = s1&3; t2 = s1&-4; s2 = -a7; bgeu t2,s1 -> de8
    0x80020dcc  head loop (MemmoveBwdLoops.bhead_loop), top a7 bytes
    0x80020de8  t0 = a6+s2; a7 = a2-a7; a3 = a7&-4; t1 = t0&3; a6 = -a3;
                t3 = t2-a3; beqz t1 -> e9e (aligned)
    0x80020e9e  bgeu t3,t2; a1 = a1+a7-4; a2 = t2; word loop; j 1088
    0x80021088  s1 = t2+a6; a6 = a6+t0; a2 = a7&3; a1 = s1-a2;
                bgeu a1,s1 -> epilogue; a6 -= 1; byte loop (bwd_loop)
-/
import Projects.rmk.MemmoveBwdLoops
import Projects.rmk.MemmoveFull

set_option maxRecDepth 100000

namespace E5R.Rmk.Memmove
open E5R E5R.Rmk E5R.Rmk.MemmoveFetch

/-! ## The byte tail from 0x80021088 -/

/-- From 0x80021088 with `t2 = X`, `a6 = -W`, `t0 = S`, `a7 = m`: the last
    `m & 3` bytes below `X - W`, read from below `S - W`, then the epilogue. -/
theorem btail (c : Core) (ram : Word → BitVec 8) (X W S m : Word) (hpc : c.pc = 0x80021088) (hq : Quiet c)
    (h7 : c.get 7 = X) (h16 : c.get 16 = 0 - W) (h5 : c.get 5 = S) (h17 : c.get 17 = m)
    (hX : (m &&& 3#32).toNat ≤ (X - W).toNat) (hS : (m &&& 3#32).toNat ≤ (S - W).toNat)
    (hd : B.inRam (X - W - (m &&& 3#32)) (m &&& 3#32).toNat = true)
    (hs : B.inRam (S - W - (m &&& 3#32)) (m &&& 3#32).toNat = true) :
    ∃ k e, QRun B img k ⟨c, ram⟩ ⟨e, bwd ram (S - W + 0xffffffff#32) (X - W) (m &&& 3#32).toNat⟩ ∧
      e.pc = 0x800210b0 ∧ e.sameCsr c ∧
      ∀ r : Reg, r ≠ 9 → r ≠ 11 → r ≠ 12 → r ≠ 13 → r ≠ 16 → e.get r = c.get r := by
  have hT4 := and3 m
  let e1 := c.wr 9 (alu .add X (0 - W)) 0x8002108c
  let e2 := e1.wr 16 (alu .add (0 - W) S) 0x8002108e
  let e3 := e2.wr 12 (alu .and m 3#32) 0x80021092
  let e4 := e3.wr 11 (alu .sub (alu .add X (0 - W)) (alu .and m 3#32)) 0x80021096
  have q1 : Quiet e1 := Quiet.of_sameCsr (Core.sameCsr_wr _ _ _ _) hq
  have q2 : Quiet e2 := Quiet.of_sameCsr (Core.sameCsr_wr _ _ _ _) q1
  have q3 : Quiet e3 := Quiet.of_sameCsr (Core.sameCsr_wr _ _ _ _) q2
  have q4 : Quiet e4 := Quiet.of_sameCsr (Core.sameCsr_wr _ _ _ _) q3
  have cs4 : e4.sameCsr c := (Core.sameCsr_wr _ _ _ _).trans ((Core.sameCsr_wr _ _ _ _).trans
    ((Core.sameCsr_wr _ _ _ _).trans (Core.sameCsr_wr _ _ _ _)))
  have s0 : DetStep B img ⟨c, ram⟩ ⟨e1, ram⟩ := by
    refine detStep_of (by rw [hpc]; decide) (by rw [hpc]; exact f80021088) fun o => ?_
    rw [exec_op, h7, h16, hpc]; rfl
  have s1 : DetStep B img ⟨e1, ram⟩ ⟨e2, ram⟩ := by
    refine detStep_of (by show (0x8002108c : Word).getLsbD 0 = false; decide) f8002108c fun o => ?_
    rw [exec_op]
    have a : e1.get 16 = 0 - W := by simp [e1, Core.wr_get_ne, h16]
    have b : e1.get 5 = S := by simp [e1, Core.wr_get_ne, h5]
    rw [a, b]; rfl
  have s2 : DetStep B img ⟨e2, ram⟩ ⟨e3, ram⟩ := by
    refine detStep_of (by show (0x8002108e : Word).getLsbD 0 = false; decide) f8002108e fun o => ?_
    rw [exec_opimm]
    have a : e2.get 17 = m := by simp [e2, e1, Core.wr_get_ne, h17]
    rw [a]; rfl
  have s3 : DetStep B img ⟨e3, ram⟩ ⟨e4, ram⟩ := by
    refine detStep_of (by show (0x80021092 : Word).getLsbD 0 = false; decide) f80021092 fun o => ?_
    rw [exec_op]
    have a : e3.get 9 = alu .add X (0 - W) := by simp [e3, e2, e1, Core.wr_get_ne, Core.wr_get_self]
    have b : e3.get 12 = alu .and m 3#32 := by simp [e3, Core.wr_get_self]
    rw [a, b]; rfl
  have l9 : e4.get 9 = X - W := by simp [e4, e3, e2, e1, Core.wr_get_ne, Core.wr_get_self, alu_add]; bv_omega
  have l11 : e4.get 11 = X - W - (m &&& 3#32) := by
    simp [e4, Core.wr_get_self, alu_add, alu_sub, alu_and]; bv_omega
  have hpre : QRun B img 4 ⟨c, ram⟩ ⟨e4, ram⟩ := .step hq s0 (.step q1 s1 (.step q2 s2 (.single q3 s3)))
  have f4 : ∀ r : Reg, r ≠ 9 → r ≠ 11 → r ≠ 12 → r ≠ 16 → e4.get r = c.get r := by
    intro r a b d e; simp [e4, e3, e2, e1, Core.wr_get_ne, a, b, d, e]
  by_cases hz : (m &&& 3#32).toNat = 0
  · have s4 : DetStep B img ⟨e4, ram⟩ ⟨e4.goto 0x800210b0, ram⟩ := by
      refine detStep_of (by show (0x80021096 : Word).getLsbD 0 = false; decide) f80021096 fun o => ?_
      rw [exec_branch, l9, l11]
      have hnt : (X - W - (m &&& 3#32)).ult (X - W) = false := by
        simp only [BitVec.ult, decide_eq_false_iff_not]; bv_omega
      simp only [taken, hnt, Bool.not_false, ite_true]
      rw [show e4.pc + 0x1a#32 = 0x800210b0 by rw [show e4.pc = 0x80021096 from rfl]; decide,
        jump_ok _ _ (by decide)]; rfl
    refine ⟨5, e4.goto 0x800210b0, ?_, rfl, (Core.sameCsr_goto _ _).trans cs4, ?_⟩
    · rw [hz]; exact hpre.trans (.single q4 s4)
    · intro r a b d e f; rw [Core.goto_get]; exact f4 r a b d f
  · let e5 := e4.goto 0x8002109a
    let e6 := e5.wr 16 (alu .add (alu .add (0 - W) S) 0xffffffff#32) 0x8002109c
    have q5 : Quiet e5 := Quiet.of_sameCsr (Core.sameCsr_goto _ _) q4
    have q6 : Quiet e6 := Quiet.of_sameCsr (Core.sameCsr_wr _ _ _ _) q5
    have s4 : DetStep B img ⟨e4, ram⟩ ⟨e5, ram⟩ := by
      refine detStep_of (by show (0x80021096 : Word).getLsbD 0 = false; decide) f80021096 fun o => ?_
      rw [exec_branch, l9, l11]
      have ht : (X - W - (m &&& 3#32)).ult (X - W) = true := by
        simp only [BitVec.ult, decide_eq_true_iff]; bv_omega
      simp only [taken, ht, Bool.not_true, Bool.false_eq_true, ite_false]; rfl
    have s5 : DetStep B img ⟨e5, ram⟩ ⟨e6, ram⟩ := by
      refine detStep_of (by show (0x8002109a : Word).getLsbD 0 = false; decide) f8002109a fun o => ?_
      rw [exec_opimm]
      have a : e5.get 16 = alu .add (0 - W) S := by simp [e5, e4, e3, e2, Core.wr_get_ne, Core.wr_get_self]
      rw [a]; rfl
    let k := (m &&& 3#32).toNat - 1
    have hk : k + 1 = (m &&& 3#32).toNat := by omega
    have g9 : e6.get 9 = X - W := by
      simp only [e6, e5, Core.wr_get_ne _ _ _ _ _ (show (9 : Reg) ≠ 16 by decide), Core.goto_get]
      exact l9
    have g11 : e6.get 11 = X - W - (m &&& 3#32) := by
      simp only [e6, e5, Core.wr_get_ne _ _ _ _ _ (show (11 : Reg) ≠ 16 by decide), Core.goto_get]; exact l11
    have g16 : e6.get 16 = S - W + 0xffffffff#32 := by
      simp [e6, Core.wr_get_self, alu_add]; bv_omega
    obtain ⟨n, e, hr, hpe, hcs, hfr⟩ := bwd_loop k e6 ram rfl q6
      (by rw [g9, g11, hk]; bv_omega) (by rw [g11, hk]; bv_omega) (by rw [g16]; bv_omega)
      (by rw [g11, hk]; exact hd)
      (by rw [g16, hk, show S - W + 0xffffffff#32 - BitVec.ofNat 32 k = S - W - (m &&& 3#32) by bv_omega]; exact hs)
    rw [g16, g9, hk] at hr
    refine ⟨4 + 1 + 1 + n, e, (hpre.trans (.step q4 s4 (.single q5 s5))).trans hr, hpe,
      hcs.trans ((Core.sameCsr_wr _ _ _ _).trans ((Core.sameCsr_goto _ _).trans cs4)), ?_⟩
    intro r a b d e f
    rw [hfr r a d e f]
    simp only [e6, e5, Core.wr_get_ne _ _ _ _ _ f, Core.goto_get]
    exact f4 r a b d f

/-! ## 0x80020daa (backward) to 0x80020de8: the top head bytes -/

/-- Head bytes: the destination end's misalignment. -/
def bH (c : Core) : Word := (c.get 10 + c.get 12) &&& 3#32
/-- The aligned destination end below the head. -/
def bA (c : Core) : Word := (c.get 10 + c.get 12) &&& 0xfffffffc#32

structure AtB (c g : Core) : Prop where
  pc : g.pc = 0x80020de8
  csr : g.sameCsr c
  r10 : g.get 10 = c.get 10
  r11 : g.get 11 = c.get 11
  r12 : g.get 12 = c.get 12
  r7 : g.get 7 = bA c
  r16 : g.get 16 = c.get 11 + c.get 12
  r17 : g.get 17 = bH c
  r18 : g.get 18 = 0 - bH c
  sp : g.get 2 = c.get 2 + 0xffffffd0#32
  frame : ∀ r : Reg, r.val ∉ [2, 6, 7, 8, 9, 13, 14, 15, 16, 17, 18] → g.get r = c.get r

theorem bwd_entry (c : Core) (R0 : Word → BitVec 8) (hq : Quiet c)
    (hn : 16 ≤ (c.get 12).toNat) (hdir : (c.get 10 - c.get 11).ult (c.get 12) = true)
    (hd : B.inRam (c.get 10) (c.get 12).toNat = true) (hs : B.inRam (c.get 11) (c.get 12).toNat = true) :
    ∃ k g, QRun B img k ⟨pro c, R0⟩
      ⟨g, bwd R0 (c.get 11 + c.get 12 + 0xffffffff#32) (c.get 10 + c.get 12) (bH c).toNat⟩ ∧ AtB c g := by
  let P := pro c
  have qP : Quiet P := Quiet.of_sameCsr (pro_sameCsr c) hq
  have g10 : P.get 10 = c.get 10 := pro_get c 10 (by decide) (by decide) (by decide)
  have g11 : P.get 11 = c.get 11 := pro_get c 11 (by decide) (by decide) (by decide)
  have g12 : P.get 12 = c.get 12 := pro_get c 12 (by decide) (by decide) (by decide)
  have hdr := (B_ram _ _).mp hd
  have hsr := (B_ram _ _).mp hs
  have hH : (bH c).toNat = (c.get 10 + c.get 12).toNat % 4 := and3 _
  have hA : (bA c).toNat = (c.get 10 + c.get 12).toNat - (c.get 10 + c.get 12).toNat % 4 := andm4 _
  let e1 := P.goto 0x80020dae
  let e2 := e1.wr 9 (alu .add (c.get 10) (c.get 12)) 0x80020db2
  let e3 := e2.wr 13 (alu .add 0 0x10#32) 0x80020db4
  let e4 := e3.wr 16 (alu .add (c.get 11) (c.get 12)) 0x80020db8
  let e5 := e4.goto 0x80020dbc
  let e6 := e5.wr 17 (bH c) 0x80020dc0
  let e7 := e6.wr 7 (bA c) 0x80020dc4
  let e8 := e7.wr 18 (alu .sub 0 (bH c)) 0x80020dc8
  have q1 : Quiet e1 := Quiet.of_sameCsr (Core.sameCsr_goto _ _) qP
  have q2 : Quiet e2 := Quiet.of_sameCsr (Core.sameCsr_wr _ _ _ _) q1
  have q3 : Quiet e3 := Quiet.of_sameCsr (Core.sameCsr_wr _ _ _ _) q2
  have q4 : Quiet e4 := Quiet.of_sameCsr (Core.sameCsr_wr _ _ _ _) q3
  have q5 : Quiet e5 := Quiet.of_sameCsr (Core.sameCsr_goto _ _) q4
  have q6 : Quiet e6 := Quiet.of_sameCsr (Core.sameCsr_wr _ _ _ _) q5
  have q7 : Quiet e7 := Quiet.of_sameCsr (Core.sameCsr_wr _ _ _ _) q6
  have q8 : Quiet e8 := Quiet.of_sameCsr (Core.sameCsr_wr _ _ _ _) q7
  have cs8 : e8.sameCsr c := (Core.sameCsr_wr _ _ _ _).trans ((Core.sameCsr_wr _ _ _ _).trans
    ((Core.sameCsr_wr _ _ _ _).trans ((Core.sameCsr_goto _ _).trans ((Core.sameCsr_wr _ _ _ _).trans
      ((Core.sameCsr_wr _ _ _ _).trans ((Core.sameCsr_wr _ _ _ _).trans ((Core.sameCsr_goto _ _).trans
        (pro_sameCsr c))))))))
  have s0 : DetStep B img ⟨P, R0⟩ ⟨e1, R0⟩ := by
    refine detStep_of (by show (0x80020daa : Word).getLsbD 0 = false; decide) f80020daa fun o => ?_
    rw [exec_branch, pro_get13, g12]
    simp only [taken, alu_sub, hdir, Bool.not_true, Bool.false_eq_true, ite_false]
    rfl
  have s1 : DetStep B img ⟨e1, R0⟩ ⟨e2, R0⟩ := by
    refine detStep_of (by show (0x80020dae : Word).getLsbD 0 = false; decide) f80020dae fun o => ?_
    rw [exec_op]
    have h10 : e1.get 10 = (c.get 10) := by simp [e1, g10]
    have h12 : e1.get 12 = (c.get 12) := by simp [e1, g12]
    rw [h10, h12]; rfl
  have s2 : DetStep B img ⟨e2, R0⟩ ⟨e3, R0⟩ := by
    refine detStep_of (by show (0x80020db2 : Word).getLsbD 0 = false; decide) f80020db2 fun o => ?_
    rw [exec_opimm, Core.get_zero]; rfl
  have s3 : DetStep B img ⟨e3, R0⟩ ⟨e4, R0⟩ := by
    refine detStep_of (by show (0x80020db4 : Word).getLsbD 0 = false; decide) f80020db4 fun o => ?_
    rw [exec_op]
    have h11 : e3.get 11 = (c.get 11) := by simp [e3, e2, e1, Core.wr_get_ne, g11]
    have h12 : e3.get 12 = (c.get 12) := by simp [e3, e2, e1, Core.wr_get_ne, g12]
    rw [h11, h12]; rfl
  have s4 : DetStep B img ⟨e4, R0⟩ ⟨e5, R0⟩ := by
    refine detStep_of (by show (0x80020db8 : Word).getLsbD 0 = false; decide) f80020db8 fun o => ?_
    rw [exec_branch]
    have h12 : e4.get 12 = (c.get 12) := by simp [e4, e3, e2, e1, Core.wr_get_ne, g12]
    have h13 : e4.get 13 = alu .add 0 0x10#32 := by simp [e4, e3, Core.wr_get_ne, Core.wr_get_self]
    have hnt : (c.get 12).ult (alu .add 0 0x10#32) = false := by
      rw [alu_add]; simp only [BitVec.ult, decide_eq_false_iff_not]; bv_omega
    rw [h12, h13]; simp only [taken, hnt, Bool.false_eq_true, ite_false]; rfl
  have s5 : DetStep B img ⟨e5, R0⟩ ⟨e6, R0⟩ := by
    refine detStep_of (by show (0x80020dbc : Word).getLsbD 0 = false; decide) f80020dbc fun o => ?_
    rw [exec_opimm]
    have h9 : e5.get 9 = alu .add (c.get 10) (c.get 12) := by
      simp [e5, e4, e3, e2, Core.wr_get_ne, Core.wr_get_self]
    rw [h9]; rfl
  have s6 : DetStep B img ⟨e6, R0⟩ ⟨e7, R0⟩ := by
    refine detStep_of (by show (0x80020dc0 : Word).getLsbD 0 = false; decide) f80020dc0 fun o => ?_
    rw [exec_opimm]
    have h9 : e6.get 9 = alu .add (c.get 10) (c.get 12) := by
      simp [e6, e5, e4, e3, e2, Core.wr_get_ne, Core.wr_get_self]
    rw [h9]; rfl
  have s7 : DetStep B img ⟨e7, R0⟩ ⟨e8, R0⟩ := by
    refine detStep_of (by show (0x80020dc4 : Word).getLsbD 0 = false; decide) f80020dc4 fun o => ?_
    rw [exec_op, Core.get_zero]
    have h17 : e7.get 17 = bH c := by simp [e7, e6, Core.wr_get_ne, Core.wr_get_self]
    rw [h17]; rfl
  have hpre : QRun B img 8 ⟨P, R0⟩ ⟨e8, R0⟩ :=
    .step qP s0 (.step q1 s1 (.step q2 s2 (.step q3 s3 (.step q4 s4 (.step q5 s5 (.step q6 s6
      (.single q7 s7)))))))
  have f8 : ∀ r : Reg, r.val ∉ [2, 6, 7, 9, 13, 16, 17, 18] → e8.get r = c.get r := by
    intro r hr
    have h2 : r ≠ 2 := fun e => hr (by subst e; decide)
    have h6 : r ≠ 6 := fun e => hr (by subst e; decide)
    have h7 : r ≠ 7 := fun e => hr (by subst e; decide)
    have h9 : r ≠ 9 := fun e => hr (by subst e; decide)
    have h13 : r ≠ 13 := fun e => hr (by subst e; decide)
    have h16 : r ≠ 16 := fun e => hr (by subst e; decide)
    have h17 : r ≠ 17 := fun e => hr (by subst e; decide)
    have h18 : r ≠ 18 := fun e => hr (by subst e; decide)
    simp only [e8, e7, e6, e5, e4, e3, e2, e1, Core.wr_get_ne _ _ _ _ _ h18, Core.wr_get_ne _ _ _ _ _ h7,
      Core.wr_get_ne _ _ _ _ _ h17, Core.wr_get_ne _ _ _ _ _ h16, Core.wr_get_ne _ _ _ _ _ h13,
      Core.wr_get_ne _ _ _ _ _ h9, Core.goto_get]
    exact pro_get c r h2 h6 h13
  have e8sp : e8.get 2 = c.get 2 + 0xffffffd0#32 := by
    simp only [e8, e7, e6, e5, e4, e3, e2, e1, Core.wr_get_ne _ _ _ _ _ (show (2 : Reg) ≠ 18 by decide),
      Core.wr_get_ne _ _ _ _ _ (show (2 : Reg) ≠ 7 by decide),
      Core.wr_get_ne _ _ _ _ _ (show (2 : Reg) ≠ 17 by decide),
      Core.wr_get_ne _ _ _ _ _ (show (2 : Reg) ≠ 16 by decide),
      Core.wr_get_ne _ _ _ _ _ (show (2 : Reg) ≠ 13 by decide),
      Core.wr_get_ne _ _ _ _ _ (show (2 : Reg) ≠ 9 by decide), Core.goto_get]
    exact pro_get2 c
  have e8_7 : e8.get 7 = bA c := by simp [e8, e7, Core.wr_get_ne, Core.wr_get_self]
  have e8_9 : e8.get 9 = c.get 10 + c.get 12 := by
    simp [e8, e7, e6, e5, e4, e3, e2, Core.wr_get_ne, Core.wr_get_self, alu_add]
  have e8_16 : e8.get 16 = c.get 11 + c.get 12 := by
    simp [e8, e7, e6, e5, e4, Core.wr_get_ne, Core.wr_get_self, alu_add]
  have e8_17 : e8.get 17 = bH c := by simp [e8, e7, e6, Core.wr_get_ne, Core.wr_get_self]
  have e8_18 : e8.get 18 = 0 - bH c := by simp [e8, Core.wr_get_self, alu_sub]
  by_cases hz : (bH c).toNat = 0
  · have s8 : DetStep B img ⟨e8, R0⟩ ⟨e8.goto 0x80020de8, R0⟩ := by
      refine detStep_of (by show (0x80020dc8 : Word).getLsbD 0 = false; decide) f80020dc8 fun o => ?_
      rw [exec_branch, e8_7, e8_9]
      have hnt : (bA c).ult (c.get 10 + c.get 12) = false := by
        simp only [BitVec.ult, decide_eq_false_iff_not]; omega
      simp only [taken, hnt, Bool.not_false, ite_true]
      rw [show e8.pc + 0x20#32 = 0x80020de8 by rw [show e8.pc = 0x80020dc8 from rfl]; decide,
        jump_ok _ _ (by decide)]; rfl
    refine ⟨9, e8.goto 0x80020de8, ?_, ⟨rfl, (Core.sameCsr_goto _ _).trans cs8,
      by rw [Core.goto_get]; exact f8 10 (by decide), by rw [Core.goto_get]; exact f8 11 (by decide),
      by rw [Core.goto_get]; exact f8 12 (by decide), by rw [Core.goto_get]; exact e8_7,
      by rw [Core.goto_get]; exact e8_16, by rw [Core.goto_get]; exact e8_17,
      by rw [Core.goto_get]; exact e8_18, by rw [Core.goto_get]; exact e8sp,
      fun r hr => by rw [Core.goto_get]; exact f8 r (fun h => hr (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at h ⊢; omega))⟩⟩
    rw [hz]; exact hpre.trans (.single q8 s8)
  · let e9 := e8.goto 0x80020dcc
    let e10 := e9.wr 15 (alu .add (c.get 11) (c.get 12)) 0x80020dd0
    let e11 := e10.wr 15 (alu .add (alu .add (c.get 11) (c.get 12)) 0xffffffff#32) 0x80020dd2
    let e12 := e11.wr 13 (alu .add 0 (c.get 10 + c.get 12)) 0x80020dd4
    have r9 : Quiet e9 := Quiet.of_sameCsr (Core.sameCsr_goto _ _) q8
    have r10 : Quiet e10 := Quiet.of_sameCsr (Core.sameCsr_wr _ _ _ _) r9
    have r11 : Quiet e11 := Quiet.of_sameCsr (Core.sameCsr_wr _ _ _ _) r10
    have r12 : Quiet e12 := Quiet.of_sameCsr (Core.sameCsr_wr _ _ _ _) r11
    have s8 : DetStep B img ⟨e8, R0⟩ ⟨e9, R0⟩ := by
      refine detStep_of (by show (0x80020dc8 : Word).getLsbD 0 = false; decide) f80020dc8 fun o => ?_
      rw [exec_branch, e8_7, e8_9]
      have ht : (bA c).ult (c.get 10 + c.get 12) = true := by
        simp only [BitVec.ult, decide_eq_true_iff]; omega
      simp only [taken, ht, Bool.not_true, Bool.false_eq_true, ite_false]; rfl
    have s9 : DetStep B img ⟨e9, R0⟩ ⟨e10, R0⟩ := by
      refine detStep_of (by show (0x80020dcc : Word).getLsbD 0 = false; decide) f80020dcc fun o => ?_
      rw [exec_op, show e9.get 11 = c.get 11 from f8 11 (by decide), show e9.get 12 = c.get 12 from f8 12 (by decide)]
      rfl
    have s10 : DetStep B img ⟨e10, R0⟩ ⟨e11, R0⟩ := by
      refine detStep_of (by show (0x80020dd0 : Word).getLsbD 0 = false; decide) f80020dd0 fun o => ?_
      rw [exec_opimm, show e10.get 15 = alu .add (c.get 11) (c.get 12) by simp [e10, Core.wr_get_self]]; rfl
    have s11 : DetStep B img ⟨e11, R0⟩ ⟨e12, R0⟩ := by
      refine detStep_of (by show (0x80020dd2 : Word).getLsbD 0 = false; decide) f80020dd2 fun o => ?_
      rw [exec_op, Core.get_zero, show e11.get 9 = c.get 10 + c.get 12 by
        simp only [e11, e10, e9, Core.wr_get_ne _ _ _ _ _ (show (9 : Reg) ≠ 15 by decide), Core.goto_get]; exact e8_9]
      rfl
    let k := (bH c).toNat - 1
    have hk : k + 1 = (bH c).toNat := by omega
    have l7 : e12.get 7 = bA c := by simp [e12, e11, e10, e9, Core.wr_get_ne, e8_7]
    have l13 : e12.get 13 = c.get 10 + c.get 12 := by simp [e12, Core.wr_get_self, alu_add]
    have l15 : e12.get 15 = c.get 11 + c.get 12 + 0xffffffff#32 := by
      simp [e12, e11, Core.wr_get_ne, Core.wr_get_self, alu_add]
    obtain ⟨m, g, hr, hpc, hcs, hfr⟩ := bhead_loop k e12 R0 rfl r12
      (by rw [l13, l7, hk]; bv_omega) (by rw [l7]; omega) (by rw [l15]; bv_omega)
      (by rw [l7, hk, B_ram]; constructor <;> bv_omega)
      (by rw [l15, hk, B_ram]; constructor <;> bv_omega)
    have ge : ∀ r : Reg, r ≠ 8 → r ≠ 13 → r ≠ 14 → r ≠ 15 → g.get r = e8.get r := by
      intro r a b d e
      rw [hfr r a b d e]
      simp [e12, e11, e10, e9, Core.wr_get_ne, b, e]
    refine ⟨8 + 1 + 3 + m, g, ?_, ⟨hpc, hcs.trans ((Core.sameCsr_wr _ _ _ _).trans
      ((Core.sameCsr_wr _ _ _ _).trans ((Core.sameCsr_wr _ _ _ _).trans ((Core.sameCsr_goto _ _).trans cs8)))),
      by rw [ge 10 (by decide) (by decide) (by decide) (by decide)]; exact f8 10 (by decide),
      by rw [ge 11 (by decide) (by decide) (by decide) (by decide)]; exact f8 11 (by decide),
      by rw [ge 12 (by decide) (by decide) (by decide) (by decide)]; exact f8 12 (by decide),
      by rw [ge 7 (by decide) (by decide) (by decide) (by decide), e8_7],
      by rw [ge 16 (by decide) (by decide) (by decide) (by decide), e8_16],
      by rw [ge 17 (by decide) (by decide) (by decide) (by decide), e8_17],
      by rw [ge 18 (by decide) (by decide) (by decide) (by decide), e8_18],
      by rw [ge 2 (by decide) (by decide) (by decide) (by decide), e8sp], ?_⟩⟩
    · rw [l15, l13, hk] at hr
      exact (hpre.trans (.step q8 s8 (.step r9 s9 (.step r10 s10 (.single r11 s11))))).trans hr
    · intro r hr
      have h8 : r ≠ 8 := fun e => hr (by subst e; decide)
      have h13 : r ≠ 13 := fun e => hr (by subst e; decide)
      have h14 : r ≠ 14 := fun e => hr (by subst e; decide)
      have h15 : r ≠ 15 := fun e => hr (by subst e; decide)
      rw [ge r h8 h13 h14 h15]
      exact f8 r (fun h => hr (by simp only [List.mem_cons, List.not_mem_nil, or_false] at h ⊢; omega))

/-! ## 0x80020de8 to 0x80020e00: word and tail counts -/

/-- Word bytes below the head. -/
def bW (c : Core) : Word := (c.get 12 - bH c) &&& 0xfffffffc#32

structure AtB2 (c g : Core) : Prop where
  pc : g.pc = 0x80020e00
  csr : g.sameCsr c
  r10 : g.get 10 = c.get 10
  r11 : g.get 11 = c.get 11
  r12 : g.get 12 = c.get 12
  r5 : g.get 5 = c.get 11 + c.get 12 - bH c
  r6 : g.get 6 = (c.get 11 + c.get 12 - bH c) &&& 3#32
  r7 : g.get 7 = bA c
  r13 : g.get 13 = bW c
  r16 : g.get 16 = 0 - bW c
  r17 : g.get 17 = c.get 12 - bH c
  r18 : g.get 18 = 0 - bH c
  r28 : g.get 28 = bA c - bW c
  sp : g.get 2 = c.get 2 + 0xffffffd0#32
  frame : ∀ r : Reg, r.val ∉ [2, 5, 6, 7, 8, 9, 13, 14, 15, 16, 17, 18, 28] → g.get r = c.get r

theorem bwd_mid (c g : Core) (R : Word → BitVec 8) (hq : Quiet c) (h : AtB c g) :
    ∃ g', QRun B img 6 ⟨g, R⟩ ⟨g', R⟩ ∧ AtB2 c g' := by
  have qg : Quiet g := Quiet.of_sameCsr h.csr hq
  let g1 := g.wr 5 (alu .add (c.get 11 + c.get 12) (0 - bH c)) 0x80020dec
  let g2 := g1.wr 17 (alu .sub (c.get 12) (bH c)) 0x80020df0
  let g3 := g2.wr 13 (bW c) 0x80020df4
  let g4 := g3.wr 6 (alu .and (alu .add (c.get 11 + c.get 12) (0 - bH c)) 3#32) 0x80020df8
  let g5 := g4.wr 16 (alu .sub 0 (bW c)) 0x80020dfc
  let g6 := g5.wr 28 (alu .sub (bA c) (bW c)) 0x80020e00
  have q1 : Quiet g1 := Quiet.of_sameCsr (Core.sameCsr_wr _ _ _ _) qg
  have q2 : Quiet g2 := Quiet.of_sameCsr (Core.sameCsr_wr _ _ _ _) q1
  have q3 : Quiet g3 := Quiet.of_sameCsr (Core.sameCsr_wr _ _ _ _) q2
  have q4 : Quiet g4 := Quiet.of_sameCsr (Core.sameCsr_wr _ _ _ _) q3
  have q5 : Quiet g5 := Quiet.of_sameCsr (Core.sameCsr_wr _ _ _ _) q4
  have s0 : DetStep B img ⟨g, R⟩ ⟨g1, R⟩ := by
    refine detStep_of (by rw [h.pc]; decide) (by rw [h.pc]; exact f80020de8) fun o => ?_
    rw [exec_op, h.r16, h.r18, h.pc]; rfl
  have s1 : DetStep B img ⟨g1, R⟩ ⟨g2, R⟩ := by
    refine detStep_of (by show (0x80020dec : Word).getLsbD 0 = false; decide) f80020dec fun o => ?_
    rw [exec_op, show g1.get 12 = c.get 12 by simp [g1, Core.wr_get_ne, h.r12],
      show g1.get 17 = bH c by simp [g1, Core.wr_get_ne, h.r17]]; rfl
  have s2 : DetStep B img ⟨g2, R⟩ ⟨g3, R⟩ := by
    refine detStep_of (by show (0x80020df0 : Word).getLsbD 0 = false; decide) f80020df0 fun o => ?_
    rw [exec_opimm, show g2.get 17 = alu .sub (c.get 12) (bH c) by simp [g2, Core.wr_get_self]]; rfl
  have s3 : DetStep B img ⟨g3, R⟩ ⟨g4, R⟩ := by
    refine detStep_of (by show (0x80020df4 : Word).getLsbD 0 = false; decide) f80020df4 fun o => ?_
    rw [exec_opimm, show g3.get 5 = alu .add (c.get 11 + c.get 12) (0 - bH c) by
      simp [g3, g2, g1, Core.wr_get_ne, Core.wr_get_self]]; rfl
  have s4 : DetStep B img ⟨g4, R⟩ ⟨g5, R⟩ := by
    refine detStep_of (by show (0x80020df8 : Word).getLsbD 0 = false; decide) f80020df8 fun o => ?_
    rw [exec_op, Core.get_zero, show g4.get 13 = bW c by simp [g4, g3, Core.wr_get_ne, Core.wr_get_self]]; rfl
  have s5 : DetStep B img ⟨g5, R⟩ ⟨g6, R⟩ := by
    refine detStep_of (by show (0x80020dfc : Word).getLsbD 0 = false; decide) f80020dfc fun o => ?_
    rw [exec_op, show g5.get 7 = bA c by simp [g5, g4, g3, g2, g1, Core.wr_get_ne, h.r7],
      show g5.get 13 = bW c by simp [g5, g4, g3, Core.wr_get_ne, Core.wr_get_self]]; rfl
  have fr : ∀ r : Reg, r ≠ 5 → r ≠ 6 → r ≠ 13 → r ≠ 16 → r ≠ 17 → r ≠ 28 → g6.get r = g.get r := by
    intro r a b d e f i; simp [g6, g5, g4, g3, g2, g1, Core.wr_get_ne, a, b, d, e, f, i]
  refine ⟨g6, .step qg s0 (.step q1 s1 (.step q2 s2 (.step q3 s3 (.step q4 s4 (.single q5 s5))))), rfl,
    (Core.sameCsr_wr _ _ _ _).trans ((Core.sameCsr_wr _ _ _ _).trans ((Core.sameCsr_wr _ _ _ _).trans
      ((Core.sameCsr_wr _ _ _ _).trans ((Core.sameCsr_wr _ _ _ _).trans ((Core.sameCsr_wr _ _ _ _).trans h.csr))))),
    by rw [fr 10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h.r10],
    by rw [fr 11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h.r11],
    by rw [fr 12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h.r12],
    by simp [g6, g5, g4, g3, g2, g1, Core.wr_get_ne, Core.wr_get_self, alu_add]; bv_omega,
    by simp [g6, g5, g4, Core.wr_get_ne, Core.wr_get_self, alu_add, alu_and]; congr 1; bv_omega,
    by rw [fr 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h.r7],
    by simp [g6, g5, g4, g3, Core.wr_get_ne, Core.wr_get_self],
    by simp [g6, g5, Core.wr_get_ne, Core.wr_get_self, alu_sub],
    by simp [g6, g5, g4, g3, g2, Core.wr_get_ne, Core.wr_get_self, alu_sub],
    by rw [fr 18 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h.r18],
    by simp [g6, Core.wr_get_self, alu_sub],
    by rw [fr 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h.sp], ?_⟩
  intro r hr
  rw [fr r (fun e => hr (by subst e; decide)) (fun e => hr (by subst e; decide)) (fun e => hr (by subst e; decide))
    (fun e => hr (by subst e; decide)) (fun e => hr (by subst e; decide)) (fun e => hr (by subst e; decide))]
  exact h.frame r (fun h => hr (by simp only [List.mem_cons, List.not_mem_nil, or_false] at h ⊢; omega))

theorem bwd_congr {R : Word → BitVec 8} {s s' d d' : Word} {k : Nat} (hs : s = s') (hd : d = d') :
    bwd R s d k = bwd R s' d' k := by rw [hs, hd]

/-! ## Backward, n ≥ 16, source and destination congruent mod 4 -/

/-- The arithmetic of the aligned backward path, kept out of the big proof
    context (`bv_omega` there sees every hypothesis). -/
structure BArith (d s n H A W T : Word) : Prop where
  sh0 : (s + n - H) &&& 3#32 = 0
  ult : (A - W).ult A = true
  w0 : 4 ≤ W.toNat ∧ W.toNat % 4 = 0
  w1 : A = A - W + BitVec.ofNat 32 W.toNat
  w2 : (A - W).toNat + W.toNat < 2 ^ 32
  w3 : W.toNat ≤ (s + (n - H) + 0xfffffffc#32).toNat + 4
  w4 : (s + (n - H) + 0xfffffffc#32).toNat % 4 = 0
  w5 : (A - W).toNat % 4 = 0
  w6 : ∀ j : Nat, 4 * (j + 1) = W.toNat →
    0x80029bc8 ≤ (s + (n - H) + 0xfffffffc#32 - BitVec.ofNat 32 (4 * j)).toNat ∧
    (s + (n - H) + 0xfffffffc#32 - BitVec.ofNat 32 (4 * j)).toNat + 4 * (j + 1) ≤ 0x81000000
  w7 : 0x80029bc8 ≤ (A - W).toNat ∧ (A - W).toNat + W.toNat ≤ 0x81000000
  t1 : T.toNat ≤ (A - W).toNat
  t2 : T.toNat ≤ (s + n - H - W).toNat
  t3 : 0x80029bc8 ≤ (A - W - T).toNat ∧ (A - W - T).toNat + T.toNat ≤ 0x81000000
  t4 : 0x80029bc8 ≤ (s + n - H - W - T).toNat ∧ (s + n - H - W - T).toNat + T.toNat ≤ 0x81000000
  g1 : W.toNat ≤ A.toNat
  g2 : W.toNat ≤ (s + (n - H) + 0xfffffffc#32).toNat + 3
  g3 : (s + (n - H) + 0xfffffffc#32).toNat + 4 < 2 ^ 32
  g4 : (s + (n - H) + 0xfffffffc#32).toNat + 4 ≤ A.toNat
  g5 : s + (n - H) + 0xfffffffc#32 + 3 = s + n + 0xffffffff#32 - BitVec.ofNat 32 H.toNat
  g6 : A = d + n - BitVec.ofNat 32 H.toNat
  g7 : s + n - H - W + 0xffffffff#32 = s + n + 0xffffffff#32 - BitVec.ofNat 32 (H.toNat + W.toNat)
  g8 : A - W = d + n - BitVec.ofNat 32 (H.toNat + W.toNat)
  g9 : n.toNat = H.toNat + W.toNat + T.toNat

theorem bwd_arith (d s n H A W T : Word)
    (hdr : 0x80029bc8 ≤ d.toNat ∧ d.toNat + n.toNat ≤ 0x81000000)
    (hsr : 0x80029bc8 ≤ s.toNat ∧ s.toNat + n.toNat ≤ 0x81000000)
    (hn : 16 ≤ n.toNat) (hle : s.toNat ≤ d.toNat) (hcong : s.toNat % 4 = d.toNat % 4)
    (hH : H.toNat = (d + n).toNat % 4) (hA : A.toNat = (d + n).toNat - (d + n).toNat % 4)
    (hW : W.toNat = (n - H).toNat - (n - H).toNat % 4) (hT : T.toNat = (n - H).toNat % 4) :
    BArith d s n H A W T := by
  have hD : (d + n).toNat = d.toNat + n.toNat := by bv_omega
  have hH4 : H.toNat < 4 := by omega
  have hM : (n - H).toNat = n.toNat - H.toNat := by bv_omega
  have kH : H.toNat = (d.toNat + n.toNat) % 4 := by omega
  have kA : A.toNat + H.toNat = d.toNat + n.toNat := by omega
  have kW : W.toNat + T.toNat + H.toNat = n.toNat := by omega
  have kT : T.toNat < 4 := by omega
  have kW4 : W.toNat % 4 = 0 := by omega
  have kA4 : A.toNat % 4 = 0 := by omega
  clear hH hA hW hT hD hM
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · apply BitVec.eq_of_toNat_eq; rw [and3]; bv_omega
  · simp only [BitVec.ult, decide_eq_true_iff]; bv_omega
  · omega
  · bv_omega
  · bv_omega
  · bv_omega
  · bv_omega
  · bv_omega
  · intro j hj; constructor <;> bv_omega
  · constructor <;> bv_omega
  · bv_omega
  · bv_omega
  · constructor <;> bv_omega
  · constructor <;> bv_omega
  · omega
  · bv_omega
  · bv_omega
  · bv_omega
  · bv_omega
  · bv_omega
  · bv_omega
  · bv_omega
  · omega

theorem bwd_aligned (c : Core) (R0 : Word → BitVec 8) (hq : Quiet c)
    (hn : 16 ≤ (c.get 12).toNat) (hdir : (c.get 10 - c.get 11).ult (c.get 12) = true)
    (hd : B.inRam (c.get 10) (c.get 12).toNat = true) (hs : B.inRam (c.get 11) (c.get 12).toNat = true)
    (hcong : (c.get 11).toNat % 4 = (c.get 10).toNat % 4) :
    ∃ k e, QRun B img k ⟨pro c, R0⟩
      ⟨e, bwd R0 (c.get 11 + c.get 12 + 0xffffffff#32) (c.get 10 + c.get 12) (c.get 12).toNat⟩ ∧
      e.pc = 0x800210b0 ∧ Frame c e [5, 7, 8, 9, 11, 12, 13, 14, 15, 16, 17, 18, 28] := by
  have hdr := (B_ram _ _).mp hd
  have hsr := (B_ram _ _).mp hs
  have hle : (c.get 11).toNat ≤ (c.get 10).toNat := by
    simp only [BitVec.ult, decide_eq_true_iff] at hdir; bv_omega
  have ar := bwd_arith (c.get 10) (c.get 11) (c.get 12) (bH c) (bA c) (bW c) ((c.get 12 - bH c) &&& 3#32)
    hdr hsr hn hle hcong (and3 _) (andm4 _) (andm4 _) (and3 _)
  obtain ⟨k1, g, hr1, hb⟩ := bwd_entry c R0 hq hn hdir hd hs
  obtain ⟨g6, hr2, hm⟩ := bwd_mid c g _ hq hb
  let R1 := bwd R0 (c.get 11 + c.get 12 + 0xffffffff#32) (c.get 10 + c.get 12) (bH c).toNat
  have q6 : Quiet g6 := Quiet.of_sameCsr hm.csr hq
  let a1 := c.get 11 + (c.get 12 - bH c) + 0xfffffffc#32
  let h1 := g6.goto 0x80020e9e
  let h2 := h1.goto 0x80020ea2
  let h3 := h2.wr 11 (alu .add (c.get 11) (c.get 12 - bH c)) 0x80020ea4
  let h4 := h3.wr 11 (alu .add (alu .add (c.get 11) (c.get 12 - bH c)) 0xfffffffc#32) 0x80020ea6
  let h5 := h4.wr 12 (alu .add 0 (bA c)) 0x80020ea8
  have p1 : Quiet h1 := Quiet.of_sameCsr (Core.sameCsr_goto _ _) q6
  have p2 : Quiet h2 := Quiet.of_sameCsr (Core.sameCsr_goto _ _) p1
  have p3 : Quiet h3 := Quiet.of_sameCsr (Core.sameCsr_wr _ _ _ _) p2
  have p4 : Quiet h4 := Quiet.of_sameCsr (Core.sameCsr_wr _ _ _ _) p3
  have p5 : Quiet h5 := Quiet.of_sameCsr (Core.sameCsr_wr _ _ _ _) p4
  have u0 : DetStep B img ⟨g6, R1⟩ ⟨h1, R1⟩ := by
    refine detStep_of (by rw [hm.pc]; decide) (by rw [hm.pc]; exact f80020e00) fun o => ?_
    rw [exec_branch, hm.r6, Core.get_zero, ar.sh0]; simp only [taken, beq_self_eq_true, ite_true]
    rw [show g6.pc + 0x9e#32 = 0x80020e9e by rw [hm.pc]; decide, jump_ok _ _ (by decide)]; rfl
  have u1 : DetStep B img ⟨h1, R1⟩ ⟨h2, R1⟩ := by
    refine detStep_of (by show (0x80020e9e : Word).getLsbD 0 = false; decide) f80020e9e fun o => ?_
    rw [exec_branch, show h1.get 28 = bA c - bW c from hm.r28, show h1.get 7 = bA c from hm.r7]
    simp only [taken, ar.ult, Bool.not_true, Bool.false_eq_true, ite_false]; rfl
  have u2 : DetStep B img ⟨h2, R1⟩ ⟨h3, R1⟩ := by
    refine detStep_of (by show (0x80020ea2 : Word).getLsbD 0 = false; decide) f80020ea2 fun o => ?_
    rw [exec_op, show h2.get 11 = c.get 11 from hm.r11, show h2.get 17 = c.get 12 - bH c from hm.r17]; rfl
  have u3 : DetStep B img ⟨h3, R1⟩ ⟨h4, R1⟩ := by
    refine detStep_of (by show (0x80020ea4 : Word).getLsbD 0 = false; decide) f80020ea4 fun o => ?_
    rw [exec_opimm, show h3.get 11 = alu .add (c.get 11) (c.get 12 - bH c) by simp [h3, Core.wr_get_self]]; rfl
  have u4 : DetStep B img ⟨h4, R1⟩ ⟨h5, R1⟩ := by
    refine detStep_of (by show (0x80020ea6 : Word).getLsbD 0 = false; decide) f80020ea6 fun o => ?_
    rw [exec_op, Core.get_zero, show h4.get 7 = bA c by simp [h4, h3, h2, h1, Core.wr_get_ne, hm.r7]]; rfl
  have hpre : QRun B img (k1 + 6 + 5) ⟨pro c, R0⟩ ⟨h5, R1⟩ :=
    (hr1.trans hr2).trans (.step q6 u0 (.step p1 u1 (.step p2 u2 (.step p3 u3 (.single p4 u4)))))
  have l11 : h5.get 11 = a1 := by
    simp only [h5, h4, Core.wr_get_ne _ _ _ _ _ (show (11 : Reg) ≠ 12 by decide),
      Core.wr_get_self _ (11 : Reg) _ _ (by decide)]; rfl
  have l12 : h5.get 12 = bA c := by simp [h5, Core.wr_get_self, alu_add]
  have l28 : h5.get 28 = bA c - bW c := by simp [h5, h4, h3, h2, h1, Core.wr_get_ne, hm.r28]
  let j := (bW c).toNat / 4 - 1
  have hj : 4 * (j + 1) = (bW c).toNat := by have := ar.w0; omega
  obtain ⟨m2, g9, hr3, hpc9, hcs9, hfr9⟩ := bword_loop j h5 R1 rfl p5
    (by rw [l12, l28, hj]; exact ar.w1) (by rw [l28, hj]; exact ar.w2) (by rw [l11]; show 4 * j ≤ (c.get 11 + (c.get 12 - bH c) + 0xfffffffc#32).toNat; have := ar.w3; omega)
    (by rw [l11]; exact ar.w4) (by rw [l28]; exact ar.w5)
    (by rw [l11, B_ram]; exact ar.w6 j hj) (by rw [l28, hj, B_ram]; exact ar.w7)
  rw [l11, l12] at hr3
  let R2 := wordsB R1 a1 (bA c) (j + 1)
  have qg9 : Quiet g9 := Quiet.of_sameCsr hcs9 p5
  have f5 : ∀ r : Reg, r ≠ 11 → r ≠ 12 → r ≠ 13 → r ≠ 14 → g9.get r = g6.get r := by
    intro r a b d e; rw [hfr9 r a b d e]; simp [h5, h4, h3, h2, h1, Core.wr_get_ne, a, b]
  obtain ⟨m3, e, hr4, hpe, hcse, hfre⟩ := btail g9 R2 (bA c) (bW c) (c.get 11 + c.get 12 - bH c)
    (c.get 12 - bH c) hpc9 qg9
    (by rw [f5 7 (by decide) (by decide) (by decide) (by decide), hm.r7])
    (by rw [f5 16 (by decide) (by decide) (by decide) (by decide), hm.r16])
    (by rw [f5 5 (by decide) (by decide) (by decide) (by decide), hm.r5])
    (by rw [f5 17 (by decide) (by decide) (by decide) (by decide), hm.r17])
    ar.t1 ar.t2 (by rw [B_ram]; exact ar.t3) (by rw [B_ram]; exact ar.t4)
  -- the RAM: head, words, tail are one backward copy
  have hfin : bwd R2 (c.get 11 + c.get 12 - bH c - bW c + 0xffffffff#32) (bA c - bW c)
      ((c.get 12 - bH c) &&& 3#32).toNat =
      bwd R0 (c.get 11 + c.get 12 + 0xffffffff#32) (c.get 10 + c.get 12) (c.get 12).toNat := by
    have hR2 : R2 = bwd R0 (c.get 11 + c.get 12 + 0xffffffff#32) (c.get 10 + c.get 12)
        ((bH c).toNat + (bW c).toNat) := by
      show wordsB R1 a1 (bA c) (j + 1) = _
      rw [wordsB_eq_bwd (j + 1) R1 _ _ (by rw [hj]; exact ar.g1) (by rw [hj]; exact ar.g2) ar.g3 ar.g4,
        hj, bwd_add]
      exact bwd_congr ar.g5 ar.g6
    rw [hR2, ar.g9, bwd_add ((bH c).toNat + (bW c).toNat)]
    exact bwd_congr ar.g7 ar.g8
  refine ⟨k1 + 6 + 5 + m2 + m3, e, ?_, hpe, ?_⟩
  · rw [← hfin]; exact (hpre.trans hr3).trans hr4
  have cs : e.sameCsr c := hcse.trans (hcs9.trans ((Core.sameCsr_wr _ _ _ _).trans ((Core.sameCsr_wr _ _ _ _).trans
    ((Core.sameCsr_wr _ _ _ _).trans ((Core.sameCsr_goto _ _).trans ((Core.sameCsr_goto _ _).trans hm.csr))))))
  refine ⟨cs, ?_, ?_⟩
  · rw [hfre 2 (by decide) (by decide) (by decide) (by decide) (by decide),
      f5 2 (by decide) (by decide) (by decide) (by decide), hm.sp]
  · intro r hr
    have h9 : r ≠ 9 := fun e => hr (by subst e; decide)
    have h11 : r ≠ 11 := fun e => hr (by subst e; decide)
    have h12 : r ≠ 12 := fun e => hr (by subst e; decide)
    have h13 : r ≠ 13 := fun e => hr (by subst e; decide)
    have h14 : r ≠ 14 := fun e => hr (by subst e; decide)
    have h16 : r ≠ 16 := fun e => hr (by subst e; decide)
    rw [hfre r h9 h11 h12 h13 h16, f5 r h11 h12 h13 h14]
    exact hm.frame r (fun h => hr (by simp only [List.mem_cons, List.not_mem_nil, or_false] at h ⊢; omega))

/-! ## Contract: everything but backward n ≥ 16 with src, dst not congruent mod 4 -/

structure PreG (m : Machine) : Prop where
  pc : m.core.pc = 0x80020c1e
  quiet : Quiet m.core
  case : (m.core.get 12).toNat < 16 ∨ (m.core.get 10 - m.core.get 11).ult (m.core.get 12) = false ∨
    (m.core.get 11).toNat % 4 = (m.core.get 10).toNat % 4
  dst : B.inRam (m.core.get 10) (m.core.get 12).toNat = true
  src : B.inRam (m.core.get 11) (m.core.get 12).toNat = true
  spAl : (m.core.get 2).toNat % 4 = 0
  stack : 0x80029bc8 + 48 ≤ (m.core.get 2).toNat ∧ (m.core.get 2).toNat ≤ 0x81000000
  dstSep : (m.core.get 10).toNat + (m.core.get 12).toNat + 48 ≤ (m.core.get 2).toNat ∨
    (m.core.get 2).toNat ≤ (m.core.get 10).toNat
  srcSep : (m.core.get 11).toNat + (m.core.get 12).toNat + 48 ≤ (m.core.get 2).toNat ∨
    (m.core.get 2).toNat ≤ (m.core.get 11).toNat
  ra : (m.core.get 1).getLsbD 0 = false

/-- The backward copy is the memmove result (dst above src, overlapping or not). -/
theorem bwd_moved (R : Word → BitVec 8) (d s n : Word) (hdir : (d - s).ult n = true)
    (hd : 0x80029bc8 ≤ d.toNat ∧ d.toNat + n.toNat ≤ 0x81000000)
    (hs : 0x80029bc8 ≤ s.toNat ∧ s.toNat + n.toNat ≤ 0x81000000) (x : Word) :
    bwd R (s + n + 0xffffffff#32) (d + n) n.toNat x = moved R d s n.toNat x := by
  have hle : s.toNat ≤ d.toNat := by
    simp only [BitVec.ult, decide_eq_true_iff] at hdir; bv_omega
  have hpos : 0 < n.toNat := by simp only [BitVec.ult, decide_eq_true_iff] at hdir; omega
  rw [bwd_spec _ _ _ _ _ (by bv_omega) (by bv_omega)]
  unfold moved
  have hq : (d + n).toNat = d.toNat + n.toNat := by bv_omega
  rw [hq, show d.toNat + n.toNat - n.toNat = d.toNat by omega]
  split
  · exact congrArg _ (by bv_omega)
  · rfl

/-- **memmove, all but one case**: n < 16 either way; n ≥ 16 forward; n ≥ 16
    backward with src ≡ dst (mod 4). -/
theorem contractG (m₀ : Machine) (h : PreG m₀) : ∃ k m, QRun B img k m₀ m ∧ PostF m₀ m := by
  by_cases hF : (m₀.core.get 12).toNat < 16 ∨ (m₀.core.get 10 - m₀.core.get 11).ult (m₀.core.get 12) = false
  · exact contractF m₀ ⟨h.pc, h.quiet, hF, h.dst, h.src, h.spAl, h.stack, h.dstSep, h.srcSep, h.ra⟩
  obtain ⟨c, ram⟩ := m₀
  obtain ⟨hpc, hq, hcase, hd, hs, hspal, hst, hdsep, hssep, hra⟩ := h
  simp only at hpc hq hcase hd hs hspal hst hdsep hssep hra hF ⊢
  have hn : 16 ≤ (c.get 12).toNat := by omega
  have hdir : (c.get 10 - c.get 11).ult (c.get 12) = true := by
    cases h : (c.get 10 - c.get 11).ult (c.get 12)
    · exact absurd (Or.inr h) hF
    · rfl
  have hcong : (c.get 11).toNat % 4 = (c.get 10).toNat % 4 := by
    rcases hcase with h | h | h
    · omega
    · rw [hdir] at h; cases h
    · exact h
  have hsl : Slots (c.get 2) := ⟨hspal, by omega⟩
  have hpro := prologue c ram hpc hq hsl
  have hdr := (B_ram _ _).mp hd
  have hsr := (B_ram _ _).mp hs
  obtain ⟨k, e, hr, he, hfr⟩ := bwd_aligned c (saved c ram) hq hn hdir hd hs hcong
  obtain ⟨m, hm, hpost⟩ := finishC c ram
    (bwd (saved c ram) (c.get 11 + c.get 12 + 0xffffffff#32) (c.get 10 + c.get 12) (c.get 12).toNat) e
    [5, 7, 8, 9, 11, 12, 13, 14, 15, 16, 17, 18, 28] hq hd hs hsl hst.1 (by omega) (by omega) hra he hfr
    (by intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; omega)
    (fun x _ => bwd_moved _ _ _ _ hdir hdr hsr x)
  exact ⟨7 + k + 5, m, (hpro.trans hr).trans hm, hpost⟩

end E5R.Rmk.Memmove
