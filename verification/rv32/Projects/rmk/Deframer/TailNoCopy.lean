/-
  `Deframer::tail` on the pinned RMK image: the prologue and epilogue every path of `tail`
  shares, and the whole path that makes no call (consumed = 0).

  Original e5r code, Apache-2.0.

  PROVED here (no dependency on memmove: this path makes no call):
  * `prologue`: 0x8001d576..0x8001d58c, frame, the five saves, the two field loads;
  * `epilogue`: 0x8001d5ba..0x8001d5c6, the five restores and `ret`;
  * `nocopy`: from every machine meeting `TailPre frame` (any frame of at least tail's own 0x20
    bytes) with `consumed = 0`, a quiet run reaches a machine meeting `TailPost frame`.
  NOT proved here: the `consumed ≠ 0` path (it calls memmove, so it is proved against
  `CopyContract`), and `TailPanicControl`.
-/
import Projects.rmk.Deframer.Spec
import Projects.rmk.Deframer.TailFetch

set_option maxRecDepth 100000

namespace E5R.Rmk.Deframer.Tail
open E5R E5R.Rmk.TailFetch

theorem alu_add (a b : Word) : alu .add a b = a + b := rfl
theorem alu_sub (a b : Word) : alu .sub a b = a - b := rfl

/-! ## RAM frames for word writes that do not wrap -/

theorem wr_byte_other (ram : Word → BitVec 8) (a v x : Word) (ha : a.toNat + 4 ≤ 2 ^ 32)
    (h : x.toNat < a.toNat ∨ a.toNat + 4 ≤ x.toNat) : ramWrite ram a v .w x = ram x := by
  apply ramWrite_w_other; intro k hk e
  have := congrArg BitVec.toNat e
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.reducePow] at this ha
  omega

theorem rd_congr {ram ram' : Word → BitVec 8} (a : Word) (ha : a.toNat + 4 ≤ 2 ^ 32)
    (h : ∀ x : Word, a.toNat ≤ x.toNat → x.toNat < a.toNat + 4 → ram' x = ram x) :
    ramRead ram' a .w = ramRead ram a .w := by
  apply ramRead_w_congr; intro k hk
  apply h <;> simp only [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.reducePow] at ha ⊢ <;> omega

theorem rd_wr_other (ram : Word → BitVec 8) (a v b : Word) (ha : a.toNat + 4 ≤ 2 ^ 32)
    (hb : b.toNat + 4 ≤ 2 ^ 32) (h : b.toNat + 4 ≤ a.toNat ∨ a.toNat + 4 ≤ b.toNat) :
    ramRead (ramWrite ram a v .w) b .w = ramRead ram b .w :=
  rd_congr b hb fun x h1 h2 => wr_byte_other ram a v x ha (by omega)

theorem add_toNat (a : Word) (k : Nat) (h : a.toNat + k < 2 ^ 32) :
    (a + BitVec.ofNat 32 k).toNat = a.toNat + k := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega

theorem sub_toNat (a b : Word) (h : b.toNat ≤ a.toNat) : (a - b).toNat = a.toNat - b.toNat := by
  bv_omega

theorem ofNat_toNat (x : Word) : BitVec.ofNat 32 x.toNat = x := by
  apply BitVec.eq_of_toNat_eq; simp

/-! ## The frame: tail's five save slots at fp + 0xc .. fp + 0x1c -/

/-- `tail`'s stack pointer after `addi sp, sp, -0x20`. -/
def fp (c : Core) : Word := c.get 2 + 0xffffffe0#32

/-- A frame pointer whose 0x20 bytes are aligned and in model RAM. -/
structure FP (f : Word) : Prop where
  al : f.toNat % 4 = 0
  lo : 0x80029bc8 ≤ f.toNat
  hi : f.toNat + 0x20 ≤ 0x81000000

theorem FP.slot_al {f : Word} (h : FP f) (k : Nat)
    (hk : k = 0x1c ∨ k = 0x18 ∨ k = 0x14 ∨ k = 0x10 ∨ k = 0xc) :
    (f + BitVec.ofNat 32 k).toNat % 4 = 0 := by
  have := h.al; have := h.hi; rcases hk with rfl | rfl | rfl | rfl | rfl <;> bv_omega

theorem FP.slot_in {f : Word} (h : FP f) (k : Nat)
    (hk : k = 0x1c ∨ k = 0x18 ∨ k = 0x14 ∨ k = 0x10 ∨ k = 0xc) :
    B.inRam (f + BitVec.ofNat 32 k) 4 = true := by
  have := h.lo; have := h.hi
  rw [B_ram]; rcases hk with rfl | rfl | rfl | rfl | rfl <;> constructor <;> bv_omega

/-- The stack below `sp`, as `CallEnv.stack` gives it, in numbers. -/
theorem stack_nat (sp : Word) (frame : Nat) (h : B.inRam (sp - BitVec.ofNat 32 frame) frame = true) :
    0x80029bc8 + frame ≤ sp.toNat ∧ sp.toNat ≤ 0x81000000 := by
  rw [B_ram] at h; bv_omega

theorem fp_FP (c : Core) (hal : (c.get 2).toNat % 4 = 0)
    (h : 0x80029bc8 + 0x20 ≤ (c.get 2).toNat ∧ (c.get 2).toNat ≤ 0x81000000) : FP (fp c) := by
  unfold fp; exact ⟨by bv_omega, by bv_omega, by bv_omega⟩

theorem fp_add (c : Core) : fp c + 0x20#32 = c.get 2 := by unfold fp; bv_omega

theorem fp_toNat (c : Core) (h : 0x20 ≤ (c.get 2).toNat) : (fp c).toNat = (c.get 2).toNat - 0x20 := by
  unfold fp; bv_omega

/-- RAM after the five saves. -/
def tsave (c : Core) (ram : Word → BitVec 8) : Word → BitVec 8 :=
  ramWrite (ramWrite (ramWrite (ramWrite (ramWrite ram (fp c + 0x1c#32) (c.get 1) .w)
    (fp c + 0x18#32) (c.get 8) .w) (fp c + 0x14#32) (c.get 9) .w) (fp c + 0x10#32) (c.get 18) .w)
    (fp c + 0xc#32) (c.get 19) .w

section Saves
variable (c : Core) (ram : Word → BitVec 8)
  (hs : 0x80029bc8 + 0x20 ≤ (c.get 2).toNat ∧ (c.get 2).toNat ≤ 0x81000000)
include hs

theorem tsave_other (x : Word) (hx : x.toNat < (c.get 2).toNat - 0x20 ∨ (c.get 2).toNat ≤ x.toNat) :
    tsave c ram x = ram x := by
  have := fp_toNat c (by omega)
  unfold tsave
  rw [wr_byte_other _ _ _ _ (by bv_omega) (by bv_omega), wr_byte_other _ _ _ _ (by bv_omega) (by bv_omega),
    wr_byte_other _ _ _ _ (by bv_omega) (by bv_omega), wr_byte_other _ _ _ _ (by bv_omega) (by bv_omega),
    wr_byte_other _ _ _ _ (by bv_omega) (by bv_omega)]

theorem tsave_rd (a : Word) (ha : a.toNat + 4 ≤ (c.get 2).toNat - 0x20) :
    ramRead (tsave c ram) a .w = ramRead ram a .w :=
  rd_congr a (by omega) fun x _ h2 => tsave_other c ram hs x (.inl (by omega))

theorem tsave_1c : ramRead (tsave c ram) (fp c + 0x1c#32) .w = c.get 1 := by
  have := fp_toNat c (by omega)
  unfold tsave
  rw [rd_wr_other _ _ _ _ (by bv_omega) (by bv_omega) (by bv_omega),
    rd_wr_other _ _ _ _ (by bv_omega) (by bv_omega) (by bv_omega),
    rd_wr_other _ _ _ _ (by bv_omega) (by bv_omega) (by bv_omega),
    rd_wr_other _ _ _ _ (by bv_omega) (by bv_omega) (by bv_omega), ramRead_ramWrite_w]

theorem tsave_18 : ramRead (tsave c ram) (fp c + 0x18#32) .w = c.get 8 := by
  have := fp_toNat c (by omega)
  unfold tsave
  rw [rd_wr_other _ _ _ _ (by bv_omega) (by bv_omega) (by bv_omega),
    rd_wr_other _ _ _ _ (by bv_omega) (by bv_omega) (by bv_omega),
    rd_wr_other _ _ _ _ (by bv_omega) (by bv_omega) (by bv_omega), ramRead_ramWrite_w]

theorem tsave_14 : ramRead (tsave c ram) (fp c + 0x14#32) .w = c.get 9 := by
  have := fp_toNat c (by omega)
  unfold tsave
  rw [rd_wr_other _ _ _ _ (by bv_omega) (by bv_omega) (by bv_omega),
    rd_wr_other _ _ _ _ (by bv_omega) (by bv_omega) (by bv_omega), ramRead_ramWrite_w]

theorem tsave_10 : ramRead (tsave c ram) (fp c + 0x10#32) .w = c.get 18 := by
  have := fp_toNat c (by omega)
  unfold tsave
  rw [rd_wr_other _ _ _ _ (by bv_omega) (by bv_omega) (by bv_omega), ramRead_ramWrite_w]

omit hs in
theorem tsave_0c : ramRead (tsave c ram) (fp c + 0xc#32) .w = c.get 19 := by
  unfold tsave; rw [ramRead_ramWrite_w]

end Saves

/-! ## Prologue: 0x8001d576 .. 0x8001d58c -/

/-- The core at the `beqz a0` of 0x8001d58c: s0 = self, s1 = filled, s2 = len, s3 = buf,
    a0 = consumed (both read after the saves). -/
def tpro (c : Core) (ram : Word → BitVec 8) : Core :=
  (((((((c.wr 2 (fp c) 0x8001d578).goto 0x8001d582).wr 18 (alu .add 0 (c.get 12)) 0x8001d584).wr 8
    (alu .add 0 (c.get 10)) 0x8001d586).wr 10 (ramRead (tsave c ram) (c.get 10) .w) 0x8001d588).wr 9
    (ramRead (tsave c ram) (c.get 10 + 0x4#32) .w) 0x8001d58a).wr 19 (alu .add 0 (c.get 11)) 0x8001d58c)

theorem tpro_sameCsr (c : Core) (ram) : (tpro c ram).sameCsr c :=
  (Core.sameCsr_wr _ _ _ _).trans ((Core.sameCsr_wr _ _ _ _).trans ((Core.sameCsr_wr _ _ _ _).trans
    ((Core.sameCsr_wr _ _ _ _).trans ((Core.sameCsr_wr _ _ _ _).trans ((Core.sameCsr_goto _ _).trans
      (Core.sameCsr_wr _ _ _ _))))))

theorem tpro_get2 (c ram) : (tpro c ram).get 2 = fp c := by simp [tpro, Core.wr_get_ne, Core.wr_get_self]
theorem tpro_get8 (c ram) : (tpro c ram).get 8 = c.get 10 := by
  simp [tpro, Core.wr_get_ne, Core.wr_get_self, alu_add]
theorem tpro_get9 (c ram) : (tpro c ram).get 9 = ramRead (tsave c ram) (c.get 10 + 0x4#32) .w := by
  simp [tpro, Core.wr_get_ne, Core.wr_get_self]
theorem tpro_get10 (c ram) : (tpro c ram).get 10 = ramRead (tsave c ram) (c.get 10) .w := by
  simp [tpro, Core.wr_get_ne, Core.wr_get_self]
theorem tpro_get18 (c ram) : (tpro c ram).get 18 = c.get 12 := by
  simp [tpro, Core.wr_get_ne, Core.wr_get_self, alu_add]
theorem tpro_get19 (c ram) : (tpro c ram).get 19 = c.get 11 := by
  simp [tpro, Core.wr_get_ne, Core.wr_get_self, alu_add]
theorem tpro_get (c ram) (r : Reg) (h2 : r ≠ 2) (h8 : r ≠ 8) (h9 : r ≠ 9) (h10 : r ≠ 10)
    (h18 : r ≠ 18) (h19 : r ≠ 19) : (tpro c ram).get r = c.get r := by
  simp [tpro, Core.wr_get_ne, h2, h8, h9, h10, h18, h19]

theorem prologue (c : Core) (ram : Word → BitVec 8) (hpc : c.pc = 0x8001d576) (hq : Quiet c)
    (hal : (c.get 10).toNat % 4 = 0) (hself : B.inRam (c.get 10) 12 = true)
    (hsp : (c.get 2).toNat % 4 = 0)
    (hs : 0x80029bc8 + 0x20 ≤ (c.get 2).toNat ∧ (c.get 2).toNat ≤ 0x81000000) :
    QRun B img 11 ⟨c, ram⟩ ⟨tpro c ram, tsave c ram⟩ := by
  have F := fp_FP c hsp hs
  have hp := (B_ram _ _).mp hself
  let c1 := c.wr 2 (fp c) 0x8001d578
  let W1 := ramWrite ram (fp c + 0x1c#32) (c.get 1) .w
  let W2 := ramWrite W1 (fp c + 0x18#32) (c.get 8) .w
  let W3 := ramWrite W2 (fp c + 0x14#32) (c.get 9) .w
  let W4 := ramWrite W3 (fp c + 0x10#32) (c.get 18) .w
  let c7 := (c1.goto 0x8001d582).wr 18 (alu .add 0 (c.get 12)) 0x8001d584
  let c8 := c7.wr 8 (alu .add 0 (c.get 10)) 0x8001d586
  let c9 := c8.wr 10 (ramRead (tsave c ram) (c.get 10) .w) 0x8001d588
  let c10 := c9.wr 9 (ramRead (tsave c ram) (c.get 10 + 0x4#32) .w) 0x8001d58a
  have q1 : Quiet c1 := Quiet.of_sameCsr (Core.sameCsr_wr _ _ _ _) hq
  have qg : ∀ p, Quiet (c1.goto p) := fun p => Quiet.of_sameCsr (Core.sameCsr_goto _ _) q1
  have q7 : Quiet c7 := Quiet.of_sameCsr (Core.sameCsr_wr _ _ _ _) (qg _)
  have q8 : Quiet c8 := Quiet.of_sameCsr (Core.sameCsr_wr _ _ _ _) q7
  have q9 : Quiet c9 := Quiet.of_sameCsr (Core.sameCsr_wr _ _ _ _) q8
  have q10 : Quiet c10 := Quiet.of_sameCsr (Core.sameCsr_wr _ _ _ _) q9
  have g2 : ∀ p, (c1.goto p).get 2 = fp c := fun p => by simp [c1, Core.wr_get_self]
  have gk : ∀ p (r : Reg), r ≠ 2 → (c1.goto p).get r = c.get r := fun p r h => by
    simp [c1, Core.wr_get_ne, h]
  have s0 : DetStep B img ⟨c, ram⟩ ⟨c1, ram⟩ := by
    refine detStep_of (by rw [hpc]; decide) (by rw [hpc]; exact f8001d576) fun o => ?_
    rw [exec_opimm, hpc]; rfl
  have s1 : DetStep B img ⟨c1, ram⟩ ⟨c1.goto 0x8001d57a, W1⟩ := by
    refine detStep_of (by show (0x8001d578 : Word).getLsbD 0 = false; decide) f8001d578 fun o => ?_
    rw [exec_store]
    have e2 : c1.get 2 = fp c := by simp [c1, Core.wr_get_self]
    have e1 : c1.get 1 = c.get 1 := by simp [c1, Core.wr_get_ne]
    rw [e2, e1, interp_store_ram (w := .w) o (F.slot_al 0x1c (by decide)) (F.slot_in 0x1c (by decide))]; rfl
  have s2 : DetStep B img ⟨c1.goto 0x8001d57a, W1⟩ ⟨c1.goto 0x8001d57c, W2⟩ := by
    refine detStep_of (by show (0x8001d57a : Word).getLsbD 0 = false; decide) f8001d57a fun o => ?_
    rw [exec_store, g2, gk _ 8 (by decide),
      interp_store_ram (w := .w) o (F.slot_al 0x18 (by decide)) (F.slot_in 0x18 (by decide))]; rfl
  have s3 : DetStep B img ⟨c1.goto 0x8001d57c, W2⟩ ⟨c1.goto 0x8001d57e, W3⟩ := by
    refine detStep_of (by show (0x8001d57c : Word).getLsbD 0 = false; decide) f8001d57c fun o => ?_
    rw [exec_store, g2, gk _ 9 (by decide),
      interp_store_ram (w := .w) o (F.slot_al 0x14 (by decide)) (F.slot_in 0x14 (by decide))]; rfl
  have s4 : DetStep B img ⟨c1.goto 0x8001d57e, W3⟩ ⟨c1.goto 0x8001d580, W4⟩ := by
    refine detStep_of (by show (0x8001d57e : Word).getLsbD 0 = false; decide) f8001d57e fun o => ?_
    rw [exec_store, g2, gk _ 18 (by decide),
      interp_store_ram (w := .w) o (F.slot_al 0x10 (by decide)) (F.slot_in 0x10 (by decide))]; rfl
  have s5 : DetStep B img ⟨c1.goto 0x8001d580, W4⟩ ⟨c1.goto 0x8001d582, tsave c ram⟩ := by
    refine detStep_of (by show (0x8001d580 : Word).getLsbD 0 = false; decide) f8001d580 fun o => ?_
    rw [exec_store, g2, gk _ 19 (by decide),
      interp_store_ram (w := .w) o (F.slot_al 0xc (by decide)) (F.slot_in 0xc (by decide))]; rfl
  have s6 : DetStep B img ⟨c1.goto 0x8001d582, tsave c ram⟩ ⟨c7, tsave c ram⟩ := by
    refine detStep_of (by show (0x8001d582 : Word).getLsbD 0 = false; decide) f8001d582 fun o => ?_
    rw [exec_op, Core.get_zero, gk _ 12 (by decide)]; rfl
  have s7 : DetStep B img ⟨c7, tsave c ram⟩ ⟨c8, tsave c ram⟩ := by
    refine detStep_of (by show (0x8001d584 : Word).getLsbD 0 = false; decide) f8001d584 fun o => ?_
    rw [exec_op, Core.get_zero]
    have : c7.get 10 = c.get 10 := by simp [c7, Core.wr_get_ne, gk]
    rw [this]; rfl
  have s8 : DetStep B img ⟨c8, tsave c ram⟩ ⟨c9, tsave c ram⟩ := by
    refine detStep_of (by show (0x8001d586 : Word).getLsbD 0 = false; decide) f8001d586 fun o => ?_
    rw [exec_load]
    have : c8.get 10 = c.get 10 := by simp [c8, c7, Core.wr_get_ne, gk]
    rw [this, BitVec.add_zero,
      interp_load_ram (w := .w) o hal ((B_ram _ _).mpr ⟨hp.1, show (c.get 10).toNat + 4 ≤ _ by omega⟩)]; rfl
  have s9 : DetStep B img ⟨c9, tsave c ram⟩ ⟨c10, tsave c ram⟩ := by
    refine detStep_of (by show (0x8001d588 : Word).getLsbD 0 = false; decide) f8001d588 fun o => ?_
    rw [exec_load]
    have : c9.get 8 = c.get 10 := by simp [c9, c8, Core.wr_get_ne, Core.wr_get_self, alu_add]
    rw [this, interp_load_ram (w := .w) o (show (c.get 10 + 0x4#32).toNat % 4 = 0 by bv_omega)
      ((B_ram _ _).mpr ⟨by bv_omega, show (c.get 10 + 0x4#32).toNat + 4 ≤ _ by bv_omega⟩)]; rfl
  have s10 : DetStep B img ⟨c10, tsave c ram⟩ ⟨tpro c ram, tsave c ram⟩ := by
    refine detStep_of (by show (0x8001d58a : Word).getLsbD 0 = false; decide) f8001d58a fun o => ?_
    rw [exec_op, Core.get_zero]
    have : c10.get 11 = c.get 11 := by simp [c10, c9, c8, c7, Core.wr_get_ne, gk]
    rw [this]; rfl
  exact .step hq s0 (.step q1 s1 (.step (qg _) s2 (.step (qg _) s3 (.step (qg _) s4 (.step (qg _) s5
    (.step (qg _) s6 (.step q7 s7 (.step q8 s8 (.step q9 s9 (.single q10 s10))))))))))

/-! ## Epilogue: 0x8001d5ba .. 0x8001d5c6 -/

/-- The core `ret` reaches: ra, s0..s3 from the slots, sp = fp + 0x20. -/
def tepi (e : Core) (R : Word → BitVec 8) (f : Word) : Core :=
  ((((((e.wr 1 (ramRead R (f + 0x1c#32) .w) 0x8001d5bc).wr 8 (ramRead R (f + 0x18#32) .w)
    0x8001d5be).wr 9 (ramRead R (f + 0x14#32) .w) 0x8001d5c0).wr 18 (ramRead R (f + 0x10#32) .w)
    0x8001d5c2).wr 19 (ramRead R (f + 0xc#32) .w) 0x8001d5c4).wr 2 (f + 0x20#32) 0x8001d5c6).goto
    (ramRead R (f + 0x1c#32) .w)

theorem tepi_sameCsr (e R f) : (tepi e R f).sameCsr e :=
  (Core.sameCsr_goto _ _).trans ((Core.sameCsr_wr _ _ _ _).trans ((Core.sameCsr_wr _ _ _ _).trans
    ((Core.sameCsr_wr _ _ _ _).trans ((Core.sameCsr_wr _ _ _ _).trans ((Core.sameCsr_wr _ _ _ _).trans
      (Core.sameCsr_wr _ _ _ _))))))

theorem tepi_get (e R f) (r : Reg) (h1 : r ≠ 1) (h2 : r ≠ 2) (h8 : r ≠ 8) (h9 : r ≠ 9)
    (h18 : r ≠ 18) (h19 : r ≠ 19) : (tepi e R f).get r = e.get r := by
  simp [tepi, Core.wr_get_ne, h1, h2, h8, h9, h18, h19]

theorem tepi_get1 (e R f) : (tepi e R f).get 1 = ramRead R (f + 0x1c#32) .w := by
  simp [tepi, Core.wr_get_ne, Core.wr_get_self]
theorem tepi_get2 (e R f) : (tepi e R f).get 2 = f + 0x20#32 := by
  simp [tepi, Core.wr_get_ne, Core.wr_get_self]
theorem tepi_get8 (e R f) : (tepi e R f).get 8 = ramRead R (f + 0x18#32) .w := by
  simp [tepi, Core.wr_get_ne, Core.wr_get_self]
theorem tepi_get9 (e R f) : (tepi e R f).get 9 = ramRead R (f + 0x14#32) .w := by
  simp [tepi, Core.wr_get_ne, Core.wr_get_self]
theorem tepi_get18 (e R f) : (tepi e R f).get 18 = ramRead R (f + 0x10#32) .w := by
  simp [tepi, Core.wr_get_ne, Core.wr_get_self]
theorem tepi_get19 (e R f) : (tepi e R f).get 19 = ramRead R (f + 0xc#32) .w := by
  simp [tepi, Core.wr_get_ne, Core.wr_get_self]

theorem epilogue (e : Core) (R : Word → BitVec 8) (f : Word) (hpc : e.pc = 0x8001d5ba) (hq : Quiet e)
    (hsp : e.get 2 = f) (F : FP f) (hra : (ramRead R (f + 0x1c#32) .w).getLsbD 0 = false) :
    QRun B img 7 ⟨e, R⟩ ⟨tepi e R f, R⟩ := by
  let e1 := e.wr 1 (ramRead R (f + 0x1c#32) .w) 0x8001d5bc
  let e2 := e1.wr 8 (ramRead R (f + 0x18#32) .w) 0x8001d5be
  let e3 := e2.wr 9 (ramRead R (f + 0x14#32) .w) 0x8001d5c0
  let e4 := e3.wr 18 (ramRead R (f + 0x10#32) .w) 0x8001d5c2
  let e5 := e4.wr 19 (ramRead R (f + 0xc#32) .w) 0x8001d5c4
  let e6 := e5.wr 2 (f + 0x20#32) 0x8001d5c6
  have q1 : Quiet e1 := Quiet.of_sameCsr (Core.sameCsr_wr _ _ _ _) hq
  have q2 : Quiet e2 := Quiet.of_sameCsr (Core.sameCsr_wr _ _ _ _) q1
  have q3 : Quiet e3 := Quiet.of_sameCsr (Core.sameCsr_wr _ _ _ _) q2
  have q4 : Quiet e4 := Quiet.of_sameCsr (Core.sameCsr_wr _ _ _ _) q3
  have q5 : Quiet e5 := Quiet.of_sameCsr (Core.sameCsr_wr _ _ _ _) q4
  have q6 : Quiet e6 := Quiet.of_sameCsr (Core.sameCsr_wr _ _ _ _) q5
  have s0 : DetStep B img ⟨e, R⟩ ⟨e1, R⟩ := by
    refine detStep_of (by rw [hpc]; decide) (by rw [hpc]; exact f8001d5ba) fun o => ?_
    rw [exec_load, hsp, interp_load_ram (w := .w) o (F.slot_al 0x1c (by decide)) (F.slot_in 0x1c (by decide)), hpc]
    rfl
  have s1 : DetStep B img ⟨e1, R⟩ ⟨e2, R⟩ := by
    refine detStep_of (by show (0x8001d5bc : Word).getLsbD 0 = false; decide) f8001d5bc fun o => ?_
    rw [exec_load]
    have : e1.get 2 = f := by simp [e1, Core.wr_get_ne, hsp]
    rw [this, interp_load_ram (w := .w) o (F.slot_al 0x18 (by decide)) (F.slot_in 0x18 (by decide))]; rfl
  have s2 : DetStep B img ⟨e2, R⟩ ⟨e3, R⟩ := by
    refine detStep_of (by show (0x8001d5be : Word).getLsbD 0 = false; decide) f8001d5be fun o => ?_
    rw [exec_load]
    have : e2.get 2 = f := by simp [e2, e1, Core.wr_get_ne, hsp]
    rw [this, interp_load_ram (w := .w) o (F.slot_al 0x14 (by decide)) (F.slot_in 0x14 (by decide))]; rfl
  have s3 : DetStep B img ⟨e3, R⟩ ⟨e4, R⟩ := by
    refine detStep_of (by show (0x8001d5c0 : Word).getLsbD 0 = false; decide) f8001d5c0 fun o => ?_
    rw [exec_load]
    have : e3.get 2 = f := by simp [e3, e2, e1, Core.wr_get_ne, hsp]
    rw [this, interp_load_ram (w := .w) o (F.slot_al 0x10 (by decide)) (F.slot_in 0x10 (by decide))]; rfl
  have s4 : DetStep B img ⟨e4, R⟩ ⟨e5, R⟩ := by
    refine detStep_of (by show (0x8001d5c2 : Word).getLsbD 0 = false; decide) f8001d5c2 fun o => ?_
    rw [exec_load]
    have : e4.get 2 = f := by simp [e4, e3, e2, e1, Core.wr_get_ne, hsp]
    rw [this, interp_load_ram (w := .w) o (F.slot_al 0xc (by decide)) (F.slot_in 0xc (by decide))]; rfl
  have s5 : DetStep B img ⟨e5, R⟩ ⟨e6, R⟩ := by
    refine detStep_of (by show (0x8001d5c4 : Word).getLsbD 0 = false; decide) f8001d5c4 fun o => ?_
    rw [exec_opimm]
    have : e5.get 2 = f := by simp [e5, e4, e3, e2, e1, Core.wr_get_ne, hsp]
    rw [this]; rfl
  have s6 : DetStep B img ⟨e6, R⟩ ⟨tepi e R f, R⟩ := by
    refine detStep_of (by show (0x8001d5c6 : Word).getLsbD 0 = false; decide) f8001d5c6 fun o => ?_
    rw [exec_jalr, Core.set_zero]
    have : e6.get 1 = ramRead R (f + 0x1c#32) .w := by
      simp [e6, e5, e4, e3, e2, e1, Core.wr_get_ne, Core.wr_get_self]
    rw [this, BitVec.add_zero, Memmove.and_not_one _ hra, jump_ok _ _ hra]; rfl
  exact .step hq s0 (.step q1 s1 (.step q2 s2 (.step q3 s3 (.step q4 s4 (.step q5 s5 (.single q6 s6))))))

/-! ## The path without a copy: consumed = 0 -/

/-- The core at 0x8001d5ba on the no-copy path: a1 = len - filled, a0 = buf + filled. -/
def tmid (c : Core) (ram : Word → BitVec 8) : Core :=
  let P := tpro c ram
  let v := ramRead (tsave c ram) (c.get 10 + 0x4#32) .w
  ((P.goto 0x8001d5b2).wr 11 (alu .sub (c.get 12) v) 0x8001d5b6).wr 10 (alu .add (c.get 11) v) 0x8001d5ba

theorem nocopy_mid (c : Core) (ram : Word → BitVec 8) (hq : Quiet c)
    (h0 : ramRead (tsave c ram) (c.get 10) .w = 0)
    (hle : (ramRead (tsave c ram) (c.get 10 + 0x4#32) .w).toNat ≤ (c.get 12).toNat) :
    QRun B img 4 ⟨tpro c ram, tsave c ram⟩ ⟨tmid c ram, tsave c ram⟩ := by
  let P := tpro c ram
  let v := ramRead (tsave c ram) (c.get 10 + 0x4#32) .w
  have qP : Quiet P := Quiet.of_sameCsr (tpro_sameCsr c ram) hq
  have qg : ∀ p, Quiet (P.goto p) := fun p => Quiet.of_sameCsr (Core.sameCsr_goto _ _) qP
  let n3 := (P.goto 0x8001d5b2).wr 11 (alu .sub (c.get 12) v) 0x8001d5b6
  have q3 : Quiet n3 := Quiet.of_sameCsr (Core.sameCsr_wr _ _ _ _) (qg _)
  have s0 : DetStep B img ⟨P, tsave c ram⟩ ⟨P.goto 0x8001d5ae, tsave c ram⟩ := by
    refine detStep_of (by show (0x8001d58c : Word).getLsbD 0 = false; decide) f8001d58c fun o => ?_
    rw [exec_branch, Core.get_zero, tpro_get10, h0]
    simp only [taken, beq_self_eq_true, ite_true]
    rw [show P.pc + 0x22#32 = 0x8001d5ae from rfl, jump_ok _ _ (by decide)]; rfl
  have s1 : DetStep B img ⟨P.goto 0x8001d5ae, tsave c ram⟩ ⟨P.goto 0x8001d5b2, tsave c ram⟩ := by
    refine detStep_of (by show (0x8001d5ae : Word).getLsbD 0 = false; decide) f8001d5ae fun o => ?_
    rw [exec_branch, Core.goto_get, Core.goto_get, tpro_get18, tpro_get9]
    have hn : (c.get 12).ult (ramRead (tsave c ram) (c.get 10 + 0x4#32) .w) = false := by
      simp only [BitVec.ult, decide_eq_false_iff_not]; omega
    simp only [taken, hn, Bool.false_eq_true, ite_false]; rfl
  have s2 : DetStep B img ⟨P.goto 0x8001d5b2, tsave c ram⟩ ⟨n3, tsave c ram⟩ := by
    refine detStep_of (by show (0x8001d5b2 : Word).getLsbD 0 = false; decide) f8001d5b2 fun o => ?_
    rw [exec_op, Core.goto_get, Core.goto_get, tpro_get18, tpro_get9]; rfl
  have s3 : DetStep B img ⟨n3, tsave c ram⟩ ⟨tmid c ram, tsave c ram⟩ := by
    refine detStep_of (by show (0x8001d5b6 : Word).getLsbD 0 = false; decide) f8001d5b6 fun o => ?_
    rw [exec_op]
    have h19 : n3.get 19 = c.get 11 := by simp [n3, P, Core.wr_get_ne, tpro_get19]
    have h9 : n3.get 9 = v := by simp [n3, P, Core.wr_get_ne, tpro_get9, v]
    rw [h19, h9]; rfl
  exact .step qP s0 (.step (qg _) s1 (.step (qg _) s2 (.single q3 s3)))

/-- `tail` with consumed = 0 meets `TailPost`, for any frame of at least its own 0x20 bytes. -/
theorem nocopy (frame : Nat) (hf : 0x20 ≤ frame) (m₀ : Machine) (h : TailPre frame m₀)
    (h0 : consumed m₀.ram (m₀.core.get 10) = 0) :
    ∃ k m, QRun B img k m₀ m ∧ TailPost frame m₀ m := by
  obtain ⟨c, R0⟩ := m₀
  obtain ⟨E, hI⟩ := h
  simp only at E hI h0 ⊢
  have hpc : c.pc = 0x8001d576 := E.pc
  have hst := stack_nat (c.get 2) frame E.stack
  have hs : 0x80029bc8 + 0x20 ≤ (c.get 2).toNat ∧ (c.get 2).toNat ≤ 0x81000000 := ⟨by omega, hst.2⟩
  have hp := (B_ram (c.get 10) 12).mp E.self
  have hsep : (c.get 10).toNat + 12 ≤ (c.get 2).toNat - frame ∧
      (c.get 11).toNat + (c.get 12).toNat ≤ (c.get 2).toNat - frame := E.stackSep
  have hI : consumed R0 (c.get 10) ≤ filled R0 (c.get 10) ∧ filled R0 (c.get 10) ≤ (c.get 12).toNat := hI
  have F := fp_FP c E.spAl hs
  have hfp := fp_toNat c (by omega)
  let R := tsave c R0
  -- the fields, read after the saves, are the entry fields
  have rc : ramRead R (c.get 10) .w = ramRead R0 (c.get 10) .w := tsave_rd c R0 hs _ (by omega)
  have rf : ramRead R (c.get 10 + 0x4#32) .w = ramRead R0 (c.get 10 + 0x4#32) .w :=
    tsave_rd c R0 hs _ (by rw [add_toNat _ 4 (by omega)]; omega)
  have hc0 : ramRead R (c.get 10) .w = 0 := by
    rw [rc]; apply BitVec.eq_of_toNat_eq; exact h0
  have hle : (ramRead R (c.get 10 + 0x4#32) .w).toNat ≤ (c.get 12).toNat := by
    rw [rf]; exact hI.2
  have hra : (ramRead R (fp c + 0x1c#32) .w).getLsbD 0 = false := by
    rw [tsave_1c c R0 hs]; exact E.ra
  have run := ((prologue c R0 hpc E.quiet E.selfAl E.self E.spAl hs).trans
    (nocopy_mid c R0 E.quiet hc0 hle)).trans
    (epilogue (tmid c R0) R (fp c) rfl
      (Quiet.of_sameCsr ((Core.sameCsr_wr _ _ _ _).trans ((Core.sameCsr_wr _ _ _ _).trans
        ((Core.sameCsr_goto _ _).trans (tpro_sameCsr c R0)))) E.quiet)
      (by simp [tmid, Core.wr_get_ne, tpro_get2]) F hra)
  refine ⟨_, _, run, ?_⟩
  -- what the final machine holds
  let v := ramRead R (c.get 10 + 0x4#32) .w
  have filled_eq : filled R (c.get 10) = filled R0 (c.get 10) := by
    exact congrArg BitVec.toNat rf
  have consumed_eq : consumed R (c.get 10) = consumed R0 (c.get 10) := by
    exact congrArg BitVec.toNat rc
  have hv : filled R (c.get 10) = v.toNat := rfl
  have mg : ∀ r : Reg, r ≠ 10 → r ≠ 11 → (tmid c R0).get r = (tpro c R0).get r := fun r h10 h11 => by
    simp [tmid, Core.wr_get_ne, h10, h11]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [tepi, Core.goto_pc]; exact tsave_1c c R0 hs
  · exact (tepi_sameCsr _ _ _).trans ((Core.sameCsr_wr _ _ _ _).trans ((Core.sameCsr_wr _ _ _ _).trans
      ((Core.sameCsr_goto _ _).trans (tpro_sameCsr c R0))))
  · exact (tepi_get2 _ _ _).trans (fp_add c)
  · intro r hr
    by_cases h1 : r = 1
    · subst h1; exact (tepi_get1 _ _ _).trans (tsave_1c c R0 hs)
    by_cases h2 : r = 2
    · subst h2; exact (tepi_get2 _ _ _).trans (fp_add c)
    by_cases h8 : r = 8
    · subst h8; exact (tepi_get8 _ _ _).trans (tsave_18 c R0 hs)
    by_cases h9 : r = 9
    · subst h9; exact (tepi_get9 _ _ _).trans (tsave_14 c R0 hs)
    by_cases h18 : r = 18
    · subst h18; exact (tepi_get18 _ _ _).trans (tsave_10 c R0 hs)
    by_cases h19 : r = 19
    · subst h19; exact (tepi_get19 _ _ _).trans (tsave_0c c R0)
    have h10 : r ≠ 10 := fun e => hr (by subst e; decide)
    have h11 : r ≠ 11 := fun e => hr (by subst e; decide)
    simp only
    rw [tepi_get _ _ _ r h1 h2 h8 h9 h18 h19, mg r h10 h11, tpro_get c R0 r h2 h8 h9 h10 h18 h19]
  · show consumed R (c.get 10) = 0; rw [consumed_eq]; exact h0
  · show filled R (c.get 10) = _; rw [filled_eq, h0]; rfl
  · show (tepi (tmid c R0) R (fp c)).get 10 = _ ∧ _
    rw [tepi_get _ _ _ 10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      tepi_get _ _ _ 11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hv,
      ofNat_toNat]
    simp only [tmid, Core.wr_get_self _ _ _ _ (show (10 : Reg).val ≠ 0 by decide),
      Core.wr_get_ne _ _ _ _ _ (show (11 : Reg) ≠ 10 by decide),
      Core.wr_get_self _ _ _ _ (show (11 : Reg).val ≠ 0 by decide), alu_add, alu_sub]
    exact ⟨rfl, sub_toNat _ _ hle⟩
  · intro k hk
    show R _ = R0 _
    rw [h0, Nat.zero_add]
    have hk' : k < (c.get 12).toNat := by rw [filled_eq] at hk; exact Nat.lt_of_lt_of_le hk hI.2
    have hb : (c.get 11 + BitVec.ofNat 32 k).toNat = (c.get 11).toNat + k := add_toNat _ k (by omega)
    exact tsave_other c R0 hs _ (.inl (by rw [hb]; omega))
  · show consumed R (c.get 10) ≤ filled R (c.get 10) ∧ filled R (c.get 10) ≤ (c.get 12).toNat
    rw [consumed_eq, filled_eq]; exact hI
  · intro x hx
    show R x = R0 x
    have h3 : ¬ ((c.get 2).toNat - frame ≤ x.toNat ∧ x.toNat < (c.get 2).toNat) := hx.2.2
    exact tsave_other c R0 hs x (by omega)

end E5R.Rmk.Deframer.Tail
