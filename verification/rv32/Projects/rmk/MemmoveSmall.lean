/-
  The emitted memmove of the pinned RMK firmware, for copies of fewer than
  16 bytes (BOUNDED SPECIALIZATION: the word-copy and misaligned paths the
  code takes for 16 bytes or more are not covered here).

  Original e5r code, Apache-2.0.

  Entry is the call target every caller uses, the trampoline
  `memmove` at 0x80020c1e (`auipc t1,0; jr 0x180(t1)`), which jumps to
  `compiler_builtins::mem::memmove` at 0x80020d9e. ABI: a0 = dst, a1 = src,
  a2 = n, ra = return address, sp = stack pointer. The function saves s0,
  s1, s2 at sp-4, sp-8, sp-12 (its frame is sp-48..sp), picks the copy
  direction from `dst - src < n` (unsigned), copies bytewise for n < 16
  (forward, or backward from the top when dst lies inside the source),
  restores s0..s2 and returns to ra with a0 = dst.

  `contract`: from every machine meeting `Pre`, a quiet run (no interrupt
  enabled at any machine of it, every step deterministic: no fault, no
  event) reaches a machine meeting `Post`: at `ra`, every register but
  t1, a1..a4, a6 as at entry (s0..s2 and sp restored), CSRs unchanged, and
  RAM outside the three save slots equal to the memmove of the entry RAM
  (overlap in either direction included; zero length leaves RAM alone).
-/
import Projects.rmk.MemmoveLoops
import Theories.AbsintSound

set_option maxRecDepth 100000

namespace E5R.Rmk.Memmove
open E5R E5R.Rmk E5R.Rmk.MemmoveFetch

/-! ## Epilogue: 0x800210b0 lw s0..s2, addi sp, ret -/

theorem and_not_one (x : Word) (h : x.getLsbD 0 = false) : x &&& ~~~1 = x := by
  apply BitVec.eq_of_getElem_eq
  intro i hi
  rw [BitVec.getElem_and, BitVec.getElem_not]
  rcases i with _ | i
  · rw [← BitVec.getLsbD_eq_getElem, h]; simp
  · have : (1 : Word)[i + 1] = false := by
      rw [← BitVec.getLsbD_eq_getElem]; simp [BitVec.getLsbD_one]
    rw [this]; simp

/-- The epilogue's last core. -/
def epi (e : Core) (R : Word → BitVec 8) (sp' : Word) : Core :=
  ((((e.wr 8 (ramRead R (sp' + 0x2c#32) .w) 0x800210b2).wr 9 (ramRead R (sp' + 0x28#32) .w)
    0x800210b4).wr 18 (ramRead R (sp' + 0x24#32) .w) 0x800210b6).wr 2 (sp' + 0x30#32) 0x800210b8).goto
    (e.get 1)

theorem epilogue (e : Core) (R : Word → BitVec 8) (sp' : Word) (hpc : e.pc = 0x800210b0) (hq : Quiet e)
    (hsp : e.get 2 = sp') (hra : (e.get 1).getLsbD 0 = false)
    (h0 : (sp' + 0x2c#32).toNat % 4 = 0) (h1 : (sp' + 0x28#32).toNat % 4 = 0)
    (h2 : (sp' + 0x24#32).toNat % 4 = 0)
    (r0 : B.inRam (sp' + 0x2c#32) 4 = true) (r1 : B.inRam (sp' + 0x28#32) 4 = true)
    (r2 : B.inRam (sp' + 0x24#32) 4 = true) :
    QRun B img 5 ⟨e, R⟩ ⟨epi e R sp', R⟩ := by
  let e1 := e.wr 8 (ramRead R (sp' + 0x2c#32) .w) 0x800210b2
  let e2 := e1.wr 9 (ramRead R (sp' + 0x28#32) .w) 0x800210b4
  let e3 := e2.wr 18 (ramRead R (sp' + 0x24#32) .w) 0x800210b6
  let e4 := e3.wr 2 (sp' + 0x30#32) 0x800210b8
  have q1 : Quiet e1 := Quiet.of_sameCsr (Core.sameCsr_wr _ _ _ _) hq
  have q2 : Quiet e2 := Quiet.of_sameCsr (Core.sameCsr_wr _ _ _ _) q1
  have q3 : Quiet e3 := Quiet.of_sameCsr (Core.sameCsr_wr _ _ _ _) q2
  have q4 : Quiet e4 := Quiet.of_sameCsr (Core.sameCsr_wr _ _ _ _) q3
  have s0 : DetStep B img ⟨e, R⟩ ⟨e1, R⟩ := by
    refine detStep_of (by rw [hpc]; decide) (by rw [hpc]; exact f800210b0) fun o => ?_
    rw [exec_load, hsp, interp_load_ram (w := .w) o h0 r0, hpc]; rfl
  have s1 : DetStep B img ⟨e1, R⟩ ⟨e2, R⟩ := by
    refine detStep_of (by show (0x800210b2 : Word).getLsbD 0 = false; decide) f800210b2 fun o => ?_
    rw [exec_load]
    have : e1.get 2 = sp' := by simp [e1, Core.wr_get_ne, hsp]
    rw [this, interp_load_ram (w := .w) o h1 r1]; rfl
  have s2 : DetStep B img ⟨e2, R⟩ ⟨e3, R⟩ := by
    refine detStep_of (by show (0x800210b4 : Word).getLsbD 0 = false; decide) f800210b4 fun o => ?_
    rw [exec_load]
    have : e2.get 2 = sp' := by simp [e2, e1, Core.wr_get_ne, hsp]
    rw [this, interp_load_ram (w := .w) o h2 r2]; rfl
  have s3 : DetStep B img ⟨e3, R⟩ ⟨e4, R⟩ := by
    refine detStep_of (by show (0x800210b6 : Word).getLsbD 0 = false; decide) f800210b6 fun o => ?_
    rw [exec_opimm]
    have : e3.get 2 = sp' := by simp [e3, e2, e1, Core.wr_get_ne, hsp]
    rw [this]; rfl
  have s4 : DetStep B img ⟨e4, R⟩ ⟨epi e R sp', R⟩ := by
    refine detStep_of (by show (0x800210b8 : Word).getLsbD 0 = false; decide) f800210b8 fun o => ?_
    rw [exec_jalr, Core.set_zero]
    have : e4.get 1 = e.get 1 := by simp [e4, e3, e2, e1, Core.wr_get_ne]
    rw [this, BitVec.add_zero, and_not_one _ hra, jump_ok _ _ hra]; rfl
  exact .step hq s0 (.step q1 s1 (.step q2 s2 (.step q3 s3 (.single q4 s4))))

/-! ## Prologue: trampoline, frame, saves, direction test -/

/-- RAM after the three saves. -/
def saved (c : Core) (ram : Word → BitVec 8) : Word → BitVec 8 :=
  let sp' := c.get 2 + 0xffffffd0#32
  ramWrite (ramWrite (ramWrite ram (sp' + 0x2c#32) (c.get 8) .w) (sp' + 0x28#32) (c.get 9) .w)
    (sp' + 0x24#32) (c.get 18) .w

/-- The core just before the direction branch at 0x80020daa. -/
def pro (c : Core) : Core :=
  ((((((c.wr 6 0x80020c1e 0x80020c22).goto 0x80020d9e).wr 2 (c.get 2 + 0xffffffd0#32) 0x80020da0).goto
    0x80020da2).goto 0x80020da4).goto 0x80020da6).wr 13 (alu .sub (c.get 10) (c.get 11)) 0x80020daa

theorem pro_sameCsr (c : Core) : (pro c).sameCsr c :=
  (Core.sameCsr_wr _ _ _ _).trans ((Core.sameCsr_goto _ _).trans ((Core.sameCsr_goto _ _).trans
    ((Core.sameCsr_goto _ _).trans ((Core.sameCsr_wr _ _ _ _).trans ((Core.sameCsr_goto _ _).trans
      (Core.sameCsr_wr _ _ _ _))))))

theorem pro_get (c : Core) (r : Reg) (h2 : r ≠ 2) (h6 : r ≠ 6) (h13 : r ≠ 13) : (pro c).get r = c.get r := by
  simp [pro, Core.wr_get_ne, h2, h6, h13]

/-- The stack slots: aligned words inside model RAM. -/
structure Slots (sp : Word) : Prop where
  al : sp.toNat % 4 = 0
  ram : 0x80029bc8 + 12 ≤ sp.toNat ∧ sp.toNat ≤ 0x81000000

theorem Slots.al' {sp : Word} (h : Slots sp) (k : Nat) (hk : k = 0x2c ∨ k = 0x28 ∨ k = 0x24) :
    (sp + 0xffffffd0#32 + BitVec.ofNat 32 k).toNat % 4 = 0 := by
  have := h.al; have := h.ram; rcases hk with rfl | rfl | rfl <;> bv_omega

theorem Slots.in' {sp : Word} (h : Slots sp) (k : Nat) (hk : k = 0x2c ∨ k = 0x28 ∨ k = 0x24) :
    B.inRam (sp + 0xffffffd0#32 + BitVec.ofNat 32 k) 4 = true := by
  have := h.ram; rw [B_ram]; rcases hk with rfl | rfl | rfl <;> constructor <;> bv_omega

theorem prologue (c : Core) (ram : Word → BitVec 8) (hpc : c.pc = 0x80020c1e) (hq : Quiet c)
    (hs : Slots (c.get 2)) : QRun B img 7 ⟨c, ram⟩ ⟨pro c, saved c ram⟩ := by
  let sp' := c.get 2 + 0xffffffd0#32
  let c1 := c.wr 6 0x80020c1e 0x80020c22
  let c2 := c1.goto 0x80020d9e
  let c3 := c2.wr 2 sp' 0x80020da0
  let ram1 := ramWrite ram (sp' + 0x2c#32) (c.get 8) .w
  let ram2 := ramWrite ram1 (sp' + 0x28#32) (c.get 9) .w
  have q1 : Quiet c1 := Quiet.of_sameCsr (Core.sameCsr_wr _ _ _ _) hq
  have q2 : Quiet c2 := Quiet.of_sameCsr (Core.sameCsr_goto _ _) q1
  have q3 : Quiet c3 := Quiet.of_sameCsr (Core.sameCsr_wr _ _ _ _) q2
  have q4 : Quiet (c3.goto 0x80020da2) := Quiet.of_sameCsr (Core.sameCsr_goto _ _) q3
  have q5 : Quiet ((c3.goto 0x80020da2).goto 0x80020da4) := Quiet.of_sameCsr (Core.sameCsr_goto _ _) q4
  have q6 : Quiet (((c3.goto 0x80020da2).goto 0x80020da4).goto 0x80020da6) :=
    Quiet.of_sameCsr (Core.sameCsr_goto _ _) q5
  have g2 : ∀ (d : Core), d = c3 ∨ d = c3.goto 0x80020da2 ∨ d = (c3.goto 0x80020da2).goto 0x80020da4 →
      d.get 2 = sp' := by
    intro d hd; rcases hd with rfl | rfl | rfl <;> simp [c3, Core.wr_get_self]
  have s0 : DetStep B img ⟨c, ram⟩ ⟨c1, ram⟩ := by
    refine detStep_of (by rw [hpc]; decide) (by rw [hpc]; exact f80020c1e) fun o => ?_
    rw [exec_auipc, hpc]; rfl
  have s1 : DetStep B img ⟨c1, ram⟩ ⟨c2, ram⟩ := by
    refine detStep_of (by show (0x80020c22 : Word).getLsbD 0 = false; decide) f80020c22 fun o => ?_
    rw [exec_jalr, Core.set_zero]
    have : c1.get 6 = 0x80020c1e := by simp [c1, Core.wr_get_self]
    rw [this, show (0x80020c1e : Word) + 0x180#32 &&& ~~~1 = 0x80020d9e by decide, jump_ok _ _ (by decide)]
    rfl
  have s2 : DetStep B img ⟨c2, ram⟩ ⟨c3, ram⟩ := by
    refine detStep_of (by show (0x80020d9e : Word).getLsbD 0 = false; decide) f80020d9e fun o => ?_
    rw [exec_opimm]
    have : c2.get 2 = c.get 2 := by simp [c2, c1, Core.wr_get_ne]
    rw [this]; rfl
  have s3 : DetStep B img ⟨c3, ram⟩ ⟨c3.goto 0x80020da2, ram1⟩ := by
    refine detStep_of (by show (0x80020da0 : Word).getLsbD 0 = false; decide) f80020da0 fun o => ?_
    rw [exec_store, g2 c3 (.inl rfl)]
    have : c3.get 8 = c.get 8 := by simp [c3, c2, c1, Core.wr_get_ne]
    rw [this, interp_store_ram (w := .w) o (hs.al' 0x2c (by decide)) (hs.in' 0x2c (by decide))]; rfl
  have s4 : DetStep B img ⟨c3.goto 0x80020da2, ram1⟩ ⟨(c3.goto 0x80020da2).goto 0x80020da4, ram2⟩ := by
    refine detStep_of (by show (0x80020da2 : Word).getLsbD 0 = false; decide) f80020da2 fun o => ?_
    rw [exec_store, g2 _ (.inr (.inl rfl))]
    have : (c3.goto 0x80020da2).get 9 = c.get 9 := by simp [c3, c2, c1, Core.wr_get_ne]
    rw [this, interp_store_ram (w := .w) o (hs.al' 0x28 (by decide)) (hs.in' 0x28 (by decide))]; rfl
  have s5 : DetStep B img ⟨(c3.goto 0x80020da2).goto 0x80020da4, ram2⟩
      ⟨((c3.goto 0x80020da2).goto 0x80020da4).goto 0x80020da6, saved c ram⟩ := by
    refine detStep_of (by show (0x80020da4 : Word).getLsbD 0 = false; decide) f80020da4 fun o => ?_
    rw [exec_store, g2 _ (.inr (.inr rfl))]
    have : ((c3.goto 0x80020da2).goto 0x80020da4).get 18 = c.get 18 := by simp [c3, c2, c1, Core.wr_get_ne]
    rw [this, interp_store_ram (w := .w) o (hs.al' 0x24 (by decide)) (hs.in' 0x24 (by decide))]; rfl
  have s6 : DetStep B img ⟨((c3.goto 0x80020da2).goto 0x80020da4).goto 0x80020da6, saved c ram⟩
      ⟨pro c, saved c ram⟩ := by
    refine detStep_of (by show (0x80020da6 : Word).getLsbD 0 = false; decide) f80020da6 fun o => ?_
    rw [exec_op]
    have h10 : (((c3.goto 0x80020da2).goto 0x80020da4).goto 0x80020da6).get 10 = c.get 10 := by
      simp [c3, c2, c1, Core.wr_get_ne]
    have h11 : (((c3.goto 0x80020da2).goto 0x80020da4).goto 0x80020da6).get 11 = c.get 11 := by
      simp [c3, c2, c1, Core.wr_get_ne]
    rw [h10, h11]; rfl
  exact .step hq s0 (.step q1 s1 (.step q2 s2 (.step q3 s3 (.step q4 s4 (.step q5 s5 (.single q6 s6))))))

/-! ## The two directions for n < 16 -/

theorem alu_add (a b : Word) : alu .add a b = a + b := rfl
theorem alu_sub (a b : Word) : alu .sub a b = a - b := rfl

theorem pro_get2 (c : Core) : (pro c).get 2 = c.get 2 + 0xffffffd0#32 := by
  simp [pro, Core.wr_get_ne, Core.wr_get_self]

theorem pro_get13 (c : Core) : (pro c).get 13 = alu .sub (c.get 10) (c.get 11) := by
  simp [pro, Core.wr_get_self]

/-- Frame of the paths: what they leave equal to the entry core. -/
def Frame (c e : Core) (w : List Nat) : Prop :=
  e.sameCsr c ∧ e.get 2 = c.get 2 + 0xffffffd0#32 ∧ ∀ r : Reg, r.val ∉ 2 :: 6 :: w → e.get r = c.get r

/-- Forward (dst - src ≥ n, unsigned): small-copy test, then the forward
    byte loop, or straight to the epilogue when n = 0. -/
theorem fwd_path (c : Core) (R0 : Word → BitVec 8) (hq : Quiet c)
    (hn : (c.get 12).toNat < 16) (hdir : (c.get 10 - c.get 11).ult (c.get 12) = false)
    (hd : B.inRam (c.get 10) (c.get 12).toNat = true) (hs : B.inRam (c.get 11) (c.get 12).toNat = true) :
    ∃ k e, QRun B img k ⟨pro c, R0⟩ ⟨e, fwd R0 (c.get 11) (c.get 10) (c.get 12).toNat⟩ ∧
      e.pc = 0x800210b0 ∧ Frame c e [11, 12, 13, 14] := by
  let P := pro c
  have qP : Quiet P := Quiet.of_sameCsr (pro_sameCsr c) hq
  have g10 : P.get 10 = c.get 10 := pro_get c 10 (by decide) (by decide) (by decide)
  have g11 : P.get 11 = c.get 11 := pro_get c 11 (by decide) (by decide) (by decide)
  have g12 : P.get 12 = c.get 12 := pro_get c 12 (by decide) (by decide) (by decide)
  let d1 := P.goto 0x80020e20
  let d2 := d1.wr 13 (alu .add 0 0x10#32) 0x80020e22
  let d3 := d2.goto 0x80020e92
  let d4 := d3.wr 13 (alu .add 0 (c.get 10)) 0x80020e94
  let d5 := d4.wr 14 (alu .add (c.get 10) (c.get 12)) 0x80020e98
  have q1 : Quiet d1 := Quiet.of_sameCsr (Core.sameCsr_goto _ _) qP
  have q2 : Quiet d2 := Quiet.of_sameCsr (Core.sameCsr_wr _ _ _ _) q1
  have q3 : Quiet d3 := Quiet.of_sameCsr (Core.sameCsr_goto _ _) q2
  have q4 : Quiet d4 := Quiet.of_sameCsr (Core.sameCsr_wr _ _ _ _) q3
  have q5 : Quiet d5 := Quiet.of_sameCsr (Core.sameCsr_wr _ _ _ _) q4
  have cs5 : d5.sameCsr c := (Core.sameCsr_wr _ _ _ _).trans ((Core.sameCsr_wr _ _ _ _).trans
    ((Core.sameCsr_goto _ _).trans ((Core.sameCsr_wr _ _ _ _).trans ((Core.sameCsr_goto _ _).trans
      (pro_sameCsr c)))))
  have s0 : DetStep B img ⟨P, R0⟩ ⟨d1, R0⟩ := by
    refine detStep_of (by show (0x80020daa : Word).getLsbD 0 = false; decide) f80020daa fun o => ?_
    rw [exec_branch, pro_get13, g12]
    have e : alu .sub (c.get 10) (c.get 11) = c.get 10 - c.get 11 := rfl
    simp only [taken, e, hdir, Bool.not_false, if_true]
    rw [show P.pc + 0x76#32 = 0x80020e20 by rw [show P.pc = 0x80020daa from rfl]; decide,
      jump_ok _ _ (by decide)]; rfl
  have s1 : DetStep B img ⟨d1, R0⟩ ⟨d2, R0⟩ := by
    refine detStep_of (by show (0x80020e20 : Word).getLsbD 0 = false; decide) f80020e20 fun o => ?_
    rw [exec_opimm, Core.get_zero]; rfl
  have s2 : DetStep B img ⟨d2, R0⟩ ⟨d3, R0⟩ := by
    refine detStep_of (by show (0x80020e22 : Word).getLsbD 0 = false; decide) f80020e22 fun o => ?_
    rw [exec_branch]
    have e12 : d2.get 12 = c.get 12 := by simp [d2, d1, Core.wr_get_ne, g12]
    have e13 : d2.get 13 = alu .add 0 0x10#32 := by simp [d2, Core.wr_get_self]
    have ht : (c.get 12).ult (alu .add 0 0x10#32) = true := by
      rw [alu_add]; simp only [BitVec.ult, decide_eq_true_iff]; bv_omega
    rw [e12, e13]; simp only [taken, ht, if_true]
    rw [show d2.pc + 0x70#32 = 0x80020e92 by rw [show d2.pc = 0x80020e22 from rfl]; decide,
      jump_ok _ _ (by decide)]; rfl
  have s3 : DetStep B img ⟨d3, R0⟩ ⟨d4, R0⟩ := by
    refine detStep_of (by show (0x80020e92 : Word).getLsbD 0 = false; decide) f80020e92 fun o => ?_
    rw [exec_op, Core.get_zero]
    have : d3.get 10 = c.get 10 := by simp [d3, d2, d1, Core.wr_get_ne, g10]
    rw [this]; rfl
  have s4 : DetStep B img ⟨d4, R0⟩ ⟨d5, R0⟩ := by
    refine detStep_of (by show (0x80020e94 : Word).getLsbD 0 = false; decide) f80020e94 fun o => ?_
    rw [exec_op]
    have h10 : d4.get 10 = c.get 10 := by simp [d4, d3, d2, d1, Core.wr_get_ne, g10]
    have h12 : d4.get 12 = c.get 12 := by simp [d4, d3, d2, d1, Core.wr_get_ne, g12]
    rw [h10, h12]; rfl
  have hpre : QRun B img 5 ⟨P, R0⟩ ⟨d5, R0⟩ :=
    .step qP s0 (.step q1 s1 (.step q2 s2 (.step q3 s3 (.single q4 s4))))
  have f5 : ∀ r : Reg, r.val ∉ [2, 6, 11, 12, 13, 14] → d5.get r = c.get r := by
    intro r hr
    have h2 : r ≠ 2 := fun e => hr (by subst e; decide)
    have h6 : r ≠ 6 := fun e => hr (by subst e; decide)
    have h13 : r ≠ 13 := fun e => hr (by subst e; decide)
    have h14 : r ≠ 14 := fun e => hr (by subst e; decide)
    simp only [d5, d4, d3, d2, d1, Core.wr_get_ne _ _ _ _ _ h14, Core.wr_get_ne _ _ _ _ _ h13, Core.goto_get]
    exact pro_get c r h2 h6 h13
  have d5sp : d5.get 2 = c.get 2 + 0xffffffd0#32 := by
    simp only [d5, d4, d3, d2, d1, Core.wr_get_ne _ _ _ _ _ (show (2 : Reg) ≠ 14 by decide),
      Core.wr_get_ne _ _ _ _ _ (show (2 : Reg) ≠ 13 by decide), Core.goto_get]
    exact pro_get2 c
  have hdr := (B_ram _ _).mp hd
  by_cases hz : (c.get 12).toNat = 0
  · -- n = 0: bltu not taken, j to the epilogue.
    have s5 : DetStep B img ⟨d5, R0⟩ ⟨d5.goto 0x80020e9c, R0⟩ := by
      refine detStep_of (by show (0x80020e98 : Word).getLsbD 0 = false; decide) f80020e98 fun o => ?_
      rw [exec_branch]
      have h10 : d5.get 10 = c.get 10 := by simp [d5, d4, d3, d2, d1, Core.wr_get_ne, g10]
      have h14 : d5.get 14 = alu .add (c.get 10) (c.get 12) := by simp [d5, Core.wr_get_self]
      have hnt : (c.get 10).ult (alu .add (c.get 10) (c.get 12)) = false := by
        rw [alu_add]; simp only [BitVec.ult, decide_eq_false_iff_not]; bv_omega
      rw [h10, h14]; simp only [taken, hnt, Bool.false_eq_true, if_false]; rfl
    have q6 : Quiet (d5.goto 0x80020e9c) := Quiet.of_sameCsr (Core.sameCsr_goto _ _) q5
    have s6 : DetStep B img ⟨d5.goto 0x80020e9c, R0⟩ ⟨d5.goto 0x800210b0, R0⟩ := by
      refine detStep_of (by show (0x80020e9c : Word).getLsbD 0 = false; decide) f80020e9c fun o => ?_
      rw [exec_jal, Core.set_zero,
        show (d5.goto 0x80020e9c).pc + 0x214#32 = 0x800210b0 by
          rw [show (d5.goto 0x80020e9c).pc = 0x80020e9c from rfl]; decide,
        jump_ok _ _ (by decide)]; rfl
    refine ⟨7, d5.goto 0x800210b0, ?_, rfl, (Core.sameCsr_goto _ _).trans cs5, by simpa using d5sp,
      fun r hr => by rw [Core.goto_get]; exact f5 r hr⟩
    rw [hz]; exact hpre.trans (.step q5 s5 (.single q6 s6))
  · -- n > 0: into the forward loop.
    have s5 : DetStep B img ⟨d5, R0⟩ ⟨d5.goto 0x80020fc6, R0⟩ := by
      refine detStep_of (by show (0x80020e98 : Word).getLsbD 0 = false; decide) f80020e98 fun o => ?_
      rw [exec_branch]
      have h10 : d5.get 10 = c.get 10 := by simp [d5, d4, d3, d2, d1, Core.wr_get_ne, g10]
      have h14 : d5.get 14 = alu .add (c.get 10) (c.get 12) := by simp [d5, Core.wr_get_self]
      have ht : (c.get 10).ult (alu .add (c.get 10) (c.get 12)) = true := by
        rw [alu_add]; simp only [BitVec.ult, decide_eq_true_iff]; bv_omega
      rw [h10, h14]; simp only [taken, ht, if_true]
      rw [show d5.pc + 0x12e#32 = 0x80020fc6 by rw [show d5.pc = 0x80020e98 from rfl]; decide,
        jump_ok _ _ (by decide)]; rfl
    have q6 : Quiet (d5.goto 0x80020fc6) := Quiet.of_sameCsr (Core.sameCsr_goto _ _) q5
    let k := (c.get 12).toNat - 1
    have hk : k + 1 = (c.get 12).toNat := by omega
    have l11 : (d5.goto 0x80020fc6).get 11 = c.get 11 := by
      simp [d5, d4, d3, d2, d1, Core.wr_get_ne, g11]
    have l13 : (d5.goto 0x80020fc6).get 13 = c.get 10 := by
      simp [d5, d4, d3, d2, d1, Core.wr_get_ne, Core.wr_get_self, alu_add]
    have l12 : (d5.goto 0x80020fc6).get 12 = BitVec.ofNat 32 (k + 1) := by
      simp only [Core.goto_get, d5, d4, d3, d2, d1]
      simp [Core.wr_get_ne, g12, hk]
    obtain ⟨n, e, hr, hpc, hcs, hfr⟩ := fwd_loop k (d5.goto 0x80020fc6) R0 rfl q6 l12 (by omega)
      (by rw [l11, hk]; exact hs) (by rw [l13, hk]; exact hd)
    refine ⟨5 + 1 + n, e, ?_, hpc, hcs.trans ((Core.sameCsr_goto _ _).trans cs5), ?_, ?_⟩
    · rw [l11, l13, hk] at hr; exact (hpre.trans (.single q5 s5)).trans hr
    · rw [hfr 2 (by decide) (by decide) (by decide) (by decide), Core.goto_get]; exact d5sp
    · intro r hr
      have h11 : r ≠ 11 := fun e => hr (by subst e; decide)
      have h12 : r ≠ 12 := fun e => hr (by subst e; decide)
      have h13 : r ≠ 13 := fun e => hr (by subst e; decide)
      have h14 : r ≠ 14 := fun e => hr (by subst e; decide)
      rw [hfr r h11 h12 h13 h14, Core.goto_get]; exact f5 r hr

/-- Backward (dst - src < n, unsigned: dst inside the source, above it):
    small-copy test, then the backward byte loop from the top. -/
theorem bwd_path (c : Core) (R0 : Word → BitVec 8) (hq : Quiet c)
    (hn : (c.get 12).toNat < 16) (hdir : (c.get 10 - c.get 11).ult (c.get 12) = true)
    (hd : B.inRam (c.get 10) (c.get 12).toNat = true) (hs : B.inRam (c.get 11) (c.get 12).toNat = true) :
    ∃ k e, QRun B img k ⟨pro c, R0⟩
      ⟨e, bwd R0 (c.get 11 + c.get 12 + 0xffffffff#32) (c.get 10 + c.get 12) (c.get 12).toNat⟩ ∧
      e.pc = 0x800210b0 ∧ Frame c e [9, 11, 12, 13, 16] := by
  let P := pro c
  have qP : Quiet P := Quiet.of_sameCsr (pro_sameCsr c) hq
  have g10 : P.get 10 = c.get 10 := pro_get c 10 (by decide) (by decide) (by decide)
  have g11 : P.get 11 = c.get 11 := pro_get c 11 (by decide) (by decide) (by decide)
  have g12 : P.get 12 = c.get 12 := pro_get c 12 (by decide) (by decide) (by decide)
  have hdr := (B_ram _ _).mp hd
  have hsr := (B_ram _ _).mp hs
  have hpos : 0 < (c.get 12).toNat := by
    simp only [BitVec.ult, decide_eq_true_iff] at hdir; omega
  let e1 := P.goto 0x80020dae
  let e2 := e1.wr 9 (alu .add (c.get 10) (c.get 12)) 0x80020db2
  let e3 := e2.wr 13 (alu .add 0 0x10#32) 0x80020db4
  let e4 := e3.wr 16 (alu .add (c.get 11) (c.get 12)) 0x80020db8
  let e5 := e4.goto 0x80021092
  let e6 := e5.wr 11 (alu .sub (alu .add (c.get 10) (c.get 12)) (c.get 12)) 0x80021096
  let e7 := e6.goto 0x8002109a
  let e8 := e7.wr 16 (alu .add (alu .add (c.get 11) (c.get 12)) 0xffffffff#32) 0x8002109c
  have q1 : Quiet e1 := Quiet.of_sameCsr (Core.sameCsr_goto _ _) qP
  have q2 : Quiet e2 := Quiet.of_sameCsr (Core.sameCsr_wr _ _ _ _) q1
  have q3 : Quiet e3 := Quiet.of_sameCsr (Core.sameCsr_wr _ _ _ _) q2
  have q4 : Quiet e4 := Quiet.of_sameCsr (Core.sameCsr_wr _ _ _ _) q3
  have q5 : Quiet e5 := Quiet.of_sameCsr (Core.sameCsr_goto _ _) q4
  have q6 : Quiet e6 := Quiet.of_sameCsr (Core.sameCsr_wr _ _ _ _) q5
  have q7 : Quiet e7 := Quiet.of_sameCsr (Core.sameCsr_goto _ _) q6
  have q8 : Quiet e8 := Quiet.of_sameCsr (Core.sameCsr_wr _ _ _ _) q7
  have cs8 : e8.sameCsr c := (Core.sameCsr_wr _ _ _ _).trans ((Core.sameCsr_goto _ _).trans
    ((Core.sameCsr_wr _ _ _ _).trans ((Core.sameCsr_goto _ _).trans ((Core.sameCsr_wr _ _ _ _).trans
      ((Core.sameCsr_wr _ _ _ _).trans ((Core.sameCsr_wr _ _ _ _).trans ((Core.sameCsr_goto _ _).trans
        (pro_sameCsr c))))))))
  have s0 : DetStep B img ⟨P, R0⟩ ⟨e1, R0⟩ := by
    refine detStep_of (by show (0x80020daa : Word).getLsbD 0 = false; decide) f80020daa fun o => ?_
    rw [exec_branch, pro_get13, g12]
    simp only [taken, alu_sub, hdir, Bool.not_true, Bool.false_eq_true, if_false]
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
    have ht : (c.get 12).ult (alu .add 0 0x10#32) = true := by
      rw [alu_add]; simp only [BitVec.ult, decide_eq_true_iff]; bv_omega
    rw [h12, h13]; simp only [taken, ht, if_true]
    rw [show e4.pc + 0x2da#32 = 0x80021092 by rw [show e4.pc = 0x80020db8 from rfl]; decide,
      jump_ok _ _ (by decide)]; rfl
  have s5 : DetStep B img ⟨e5, R0⟩ ⟨e6, R0⟩ := by
    refine detStep_of (by show (0x80021092 : Word).getLsbD 0 = false; decide) f80021092 fun o => ?_
    rw [exec_op]
    have h9 : e5.get 9 = alu .add (c.get 10) (c.get 12) := by simp [e5, e4, e3, e2, Core.wr_get_ne, Core.wr_get_self]
    have h12 : e5.get 12 = (c.get 12) := by simp [e5, e4, e3, e2, e1, Core.wr_get_ne, g12]
    rw [h9, h12]; rfl
  have s6 : DetStep B img ⟨e6, R0⟩ ⟨e7, R0⟩ := by
    refine detStep_of (by show (0x80021096 : Word).getLsbD 0 = false; decide) f80021096 fun o => ?_
    rw [exec_branch]
    have h11 : e6.get 11 = alu .sub (alu .add (c.get 10) (c.get 12)) (c.get 12) := by simp [e6, Core.wr_get_self]
    have h9 : e6.get 9 = alu .add (c.get 10) (c.get 12) := by simp [e6, e5, e4, e3, e2, Core.wr_get_ne, Core.wr_get_self]
    have ht : (alu .sub (alu .add (c.get 10) (c.get 12)) (c.get 12)).ult (alu .add (c.get 10) (c.get 12)) = true := by
      rw [alu_add, alu_sub]; simp only [BitVec.ult, decide_eq_true_iff]; bv_omega
    rw [h11, h9]; simp only [taken, ht, Bool.not_true, Bool.false_eq_true, if_false]; rfl
  have s7 : DetStep B img ⟨e7, R0⟩ ⟨e8, R0⟩ := by
    refine detStep_of (by show (0x8002109a : Word).getLsbD 0 = false; decide) f8002109a fun o => ?_
    rw [exec_opimm]
    have : e7.get 16 = alu .add (c.get 11) (c.get 12) := by simp [e7, e6, e5, e4, Core.wr_get_ne, Core.wr_get_self]
    rw [this]; rfl
  have hpre : QRun B img 8 ⟨P, R0⟩ ⟨e8, R0⟩ :=
    .step qP s0 (.step q1 s1 (.step q2 s2 (.step q3 s3 (.step q4 s4 (.step q5 s5 (.step q6 s6
      (.single q7 s7)))))))
  let k := (c.get 12).toNat - 1
  have hk : k + 1 = (c.get 12).toNat := by omega
  have l9 : e8.get 9 = (c.get 10) + (c.get 12) := by simp [e8, e7, e6, e5, e4, e3, e2, Core.wr_get_ne, Core.wr_get_self, alu_add]
  have l11 : e8.get 11 = (c.get 10) := by
    simp only [e8, e7, e6, Core.wr_get_ne _ _ _ _ _ (show (11 : Reg) ≠ 16 by decide), Core.goto_get,
      Core.wr_get_self _ _ _ _ (show (11 : Reg).val ≠ 0 by decide), alu_add, alu_sub]
    bv_omega
  have l16 : e8.get 16 = (c.get 11) + (c.get 12) + 0xffffffff#32 := by
    simp [e8, Core.wr_get_self, alu_add]
  obtain ⟨m, e, hr, hpc, hcs, hfr⟩ := bwd_loop k e8 R0 rfl q8
    (by rw [l9, l11, show (BitVec.ofNat 32 (k + 1) : Word) = (c.get 12) by rw [hk]; simp]) (by rw [l11, hk]; omega)
    (by rw [l16]; bv_omega) (by rw [l11, hk]; exact hd)
    (by rw [l16, show (c.get 11) + (c.get 12) + 0xffffffff#32 - BitVec.ofNat 32 k = (c.get 11) by bv_omega, hk]; exact hs)
  refine ⟨8 + m, e, ?_, hpc, hcs.trans cs8, ?_, ?_⟩
  · rw [l16, l9, hk] at hr; exact hpre.trans hr
  · rw [hfr 2 (by decide) (by decide) (by decide) (by decide)]
    simp only [e8, e7, e6, e5, e4, e3, e2, e1, Core.wr_get_ne _ _ _ _ _ (show (2 : Reg) ≠ 16 by decide),
      Core.wr_get_ne _ _ _ _ _ (show (2 : Reg) ≠ 11 by decide),
      Core.wr_get_ne _ _ _ _ _ (show (2 : Reg) ≠ 13 by decide),
      Core.wr_get_ne _ _ _ _ _ (show (2 : Reg) ≠ 9 by decide), Core.goto_get]
    exact pro_get2 c
  · intro r hr
    have h2 : r ≠ 2 := fun e => hr (by subst e; decide)
    have h6 : r ≠ 6 := fun e => hr (by subst e; decide)
    have h9 : r ≠ 9 := fun e => hr (by subst e; decide)
    have h11 : r ≠ 11 := fun e => hr (by subst e; decide)
    have h12 : r ≠ 12 := fun e => hr (by subst e; decide)
    have h13 : r ≠ 13 := fun e => hr (by subst e; decide)
    have h16 : r ≠ 16 := fun e => hr (by subst e; decide)
    rw [hfr r h9 h12 h13 h16]
    simp only [e8, e7, e6, e5, e4, e3, e2, e1, Core.wr_get_ne _ _ _ _ _ h16, Core.wr_get_ne _ _ _ _ _ h11,
      Core.wr_get_ne _ _ _ _ _ h13, Core.wr_get_ne _ _ _ _ _ h9, Core.goto_get]
    exact pro_get c r h2 h6 h13

end E5R.Rmk.Memmove
