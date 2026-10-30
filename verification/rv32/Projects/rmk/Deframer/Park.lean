/-
  `Deframer::park_pending` on the pinned RMK image, proved against memmove's contract as an explicit
  hypothesis.

  Original e5r code, Apache-2.0.

  PROVED here, CONDITIONAL ON `CopyContract` (a hypothesis of each theorem, not proved here):
  `park_from_copy : ParkFromCopy`, i.e. `CopyContract → ParkContract`: from every machine at
  `park_pending` meeting `CallEnv parkPc parkStack` and the invariant, a quiet run reaches
  `ParkPost` (the pending bytes at the end of the buffer, the deframer emptied, their number
  returned). The call is made on every path that returns, also for zero pending bytes.
-/
import Projects.rmk.Deframer.TailCopy
import Projects.rmk.Deframer.ParkFetch

set_option maxRecDepth 100000

namespace E5R.Rmk.Deframer.Park
open E5R E5R.Rmk.ParkFetch E5R.Rmk.Deframer.Tail

/-! ## The 16-byte frame: ra, s0, s1 at f + 0xc, f + 8, f + 4 -/

def pfp (c : Core) : Word := c.get 2 + 0xfffffff0#32

structure FP16 (f : Word) : Prop where
  al : f.toNat % 4 = 0
  lo : 0x80029bc8 ≤ f.toNat
  hi : f.toNat + 0x10 ≤ 0x81000000

theorem FP16.slot_al {f : Word} (h : FP16 f) (k : Nat) (hk : k = 0xc ∨ k = 0x8 ∨ k = 0x4) :
    (f + BitVec.ofNat 32 k).toNat % 4 = 0 := by
  have := h.al; have := h.hi; rcases hk with rfl | rfl | rfl <;> bv_omega

theorem FP16.slot_in {f : Word} (h : FP16 f) (k : Nat) (hk : k = 0xc ∨ k = 0x8 ∨ k = 0x4) :
    B.inRam (f + BitVec.ofNat 32 k) 4 = true := by
  have := h.lo; have := h.hi
  rw [B_ram]; rcases hk with rfl | rfl | rfl <;> constructor <;> bv_omega

theorem pfp_FP (c : Core) (hal : (c.get 2).toNat % 4 = 0)
    (h : 0x80029bc8 + 0x10 ≤ (c.get 2).toNat ∧ (c.get 2).toNat ≤ 0x81000000) : FP16 (pfp c) := by
  unfold pfp; exact ⟨by bv_omega, by bv_omega, by bv_omega⟩

theorem pfp_toNat (c : Core) (h : 0x10 ≤ (c.get 2).toNat) : (pfp c).toNat = (c.get 2).toNat - 0x10 := by
  unfold pfp; bv_omega

theorem pfp_add (c : Core) : pfp c + 0x10#32 = c.get 2 := by unfold pfp; bv_omega

def psave (c : Core) (ram : Word → BitVec 8) : Word → BitVec 8 :=
  ramWrite (ramWrite (ramWrite ram (pfp c + 0xc#32) (c.get 1) .w) (pfp c + 0x8#32) (c.get 8) .w)
    (pfp c + 0x4#32) (c.get 9) .w

section Saves
variable (c : Core) (ram : Word → BitVec 8)
  (hs : 0x80029bc8 + 0x10 ≤ (c.get 2).toNat ∧ (c.get 2).toNat ≤ 0x81000000)
include hs

theorem psave_other (x : Word) (hx : x.toNat < (c.get 2).toNat - 0x10 ∨ (c.get 2).toNat ≤ x.toNat) :
    psave c ram x = ram x := by
  have := pfp_toNat c (by omega)
  unfold psave
  rw [wr_byte_other _ _ _ _ (by bv_omega) (by bv_omega), wr_byte_other _ _ _ _ (by bv_omega) (by bv_omega),
    wr_byte_other _ _ _ _ (by bv_omega) (by bv_omega)]

theorem psave_rd (a : Word) (ha : a.toNat + 4 ≤ (c.get 2).toNat - 0x10) :
    ramRead (psave c ram) a .w = ramRead ram a .w :=
  rd_congr a (by omega) fun x _ h2 => psave_other c ram hs x (.inl (by omega))

theorem psave_c : ramRead (psave c ram) (pfp c + 0xc#32) .w = c.get 1 := by
  have := pfp_toNat c (by omega)
  unfold psave
  rw [rd_wr_other _ _ _ _ (by bv_omega) (by bv_omega) (by bv_omega),
    rd_wr_other _ _ _ _ (by bv_omega) (by bv_omega) (by bv_omega), ramRead_ramWrite_w]

theorem psave_8 : ramRead (psave c ram) (pfp c + 0x8#32) .w = c.get 8 := by
  have := pfp_toNat c (by omega)
  unfold psave
  rw [rd_wr_other _ _ _ _ (by bv_omega) (by bv_omega) (by bv_omega), ramRead_ramWrite_w]

omit hs in
theorem psave_4 : ramRead (psave c ram) (pfp c + 0x4#32) .w = c.get 9 := by
  unfold psave; rw [ramRead_ramWrite_w]

end Saves

/-! ## To memmove's entry: 0x8001d388 .. 0x8001d3b4 -/

/-- At memmove's entry: a0 = buf + len - n, a1 = buf + consumed, a2 = s1 = n = filled - consumed,
    s0 = self, ra = 0x8001d3b8. -/
def pcall (c : Core) (ram : Word → BitVec 8) : Core :=
  let a := ramRead (psave c ram) (c.get 10) .w
  let v := ramRead (psave c ram) (c.get 10 + 0x4#32) .w
  ((((((((((((((c.wr 2 (pfp c) 0x8001d38a).goto 0x8001d390).wr 14 v 0x8001d392).goto 0x8001d396).wr 8
    (alu .add 0 (c.get 10)) 0x8001d398).wr 10 a 0x8001d39a).goto 0x8001d39e).wr 9 (alu .sub v a)
    0x8001d3a2).wr 13 (alu .add (c.get 11) a) 0x8001d3a6).wr 10 (alu .add (c.get 11) (c.get 12))
    0x8001d3aa).wr 10 (alu .sub (alu .add (c.get 11) (c.get 12)) (alu .sub v a)) 0x8001d3ac).wr 11
    (alu .add 0 (alu .add (c.get 11) a)) 0x8001d3ae).wr 12 (alu .add 0 (alu .sub v a)) 0x8001d3b0).wr 1
    (0x8001d3b0 + 0x4000#32) 0x8001d3b4).wr 1 0x8001d3b8 0x80020c1e

theorem pcall_sameCsr (c ram) : (pcall c ram).sameCsr c := by
  unfold pcall
  repeat (first | exact Core.sameCsr_wr _ _ _ _ | exact Core.sameCsr_goto _ _ | refine (Core.sameCsr_wr _ _ _ _).trans ?_ | refine (Core.sameCsr_goto _ _).trans ?_)

theorem pcall_get1 (c ram) : (pcall c ram).get 1 = 0x8001d3b8 := by simp [pcall, Core.wr_get_self]
theorem pcall_get2 (c ram) : (pcall c ram).get 2 = pfp c := by simp [pcall, Core.wr_get_ne, Core.wr_get_self]
theorem pcall_get8 (c ram) : (pcall c ram).get 8 = c.get 10 := by
  simp [pcall, Core.wr_get_ne, Core.wr_get_self, alu_add]
theorem pcall_get9 (c ram) : (pcall c ram).get 9 =
    ramRead (psave c ram) (c.get 10 + 0x4#32) .w - ramRead (psave c ram) (c.get 10) .w := by
  simp [pcall, Core.wr_get_ne, Core.wr_get_self, alu_sub]
theorem pcall_get10 (c ram) : (pcall c ram).get 10 = c.get 11 + c.get 12 -
    (ramRead (psave c ram) (c.get 10 + 0x4#32) .w - ramRead (psave c ram) (c.get 10) .w) := by
  simp [pcall, Core.wr_get_ne, Core.wr_get_self, alu_add, alu_sub]
theorem pcall_get11 (c ram) : (pcall c ram).get 11 = c.get 11 + ramRead (psave c ram) (c.get 10) .w := by
  simp [pcall, Core.wr_get_ne, Core.wr_get_self, alu_add]
theorem pcall_get12 (c ram) : (pcall c ram).get 12 =
    ramRead (psave c ram) (c.get 10 + 0x4#32) .w - ramRead (psave c ram) (c.get 10) .w := by
  simp [pcall, Core.wr_get_ne, Core.wr_get_self, alu_add, alu_sub]
theorem pcall_get (c ram) (r : Reg) (h1 : r ≠ 1) (h2 : r ≠ 2) (h8 : r ≠ 8) (h9 : r ≠ 9) (h10 : r ≠ 10)
    (h11 : r ≠ 11) (h12 : r ≠ 12) (h13 : r ≠ 13) (h14 : r ≠ 14) : (pcall c ram).get r = c.get r := by
  simp [pcall, Core.wr_get_ne, h1, h2, h8, h9, h10, h11, h12, h13, h14]

theorem prerun (c : Core) (ram : Word → BitVec 8) (hpc : c.pc = 0x8001d388) (hq : Quiet c)
    (hal : (c.get 10).toNat % 4 = 0) (hself : B.inRam (c.get 10) 12 = true)
    (hsp : (c.get 2).toNat % 4 = 0)
    (hs : 0x80029bc8 + 0x10 ≤ (c.get 2).toNat ∧ (c.get 2).toNat ≤ 0x81000000)
    (hle : (ramRead (psave c ram) (c.get 10 + 0x4#32) .w).toNat ≤ (c.get 12).toNat)
    (hcf : (ramRead (psave c ram) (c.get 10) .w).toNat ≤ (ramRead (psave c ram) (c.get 10 + 0x4#32) .w).toNat) :
    QRun B img 17 ⟨c, ram⟩ ⟨pcall c ram, psave c ram⟩ := by
  have F := pfp_FP c hsp hs
  have hp := (B_ram _ _).mp hself
  let PS := psave c ram
  let a := ramRead PS (c.get 10) .w
  let v := ramRead PS (c.get 10 + 0x4#32) .w
  let c1 := c.wr 2 (pfp c) 0x8001d38a
  let W1 := ramWrite ram (pfp c + 0xc#32) (c.get 1) .w
  let W2 := ramWrite W1 (pfp c + 0x8#32) (c.get 8) .w
  let c5 := (c1.goto 0x8001d390).wr 14 v 0x8001d392
  let c6 := (c5.goto 0x8001d396).wr 8 (alu .add 0 (c.get 10)) 0x8001d398
  let c7 := c6.wr 10 a 0x8001d39a
  let c9 := (c7.goto 0x8001d39e).wr 9 (alu .sub v a) 0x8001d3a2
  let c10 := c9.wr 13 (alu .add (c.get 11) a) 0x8001d3a6
  let c11 := c10.wr 10 (alu .add (c.get 11) (c.get 12)) 0x8001d3aa
  let c12 := c11.wr 10 (alu .sub (alu .add (c.get 11) (c.get 12)) (alu .sub v a)) 0x8001d3ac
  let c13 := c12.wr 11 (alu .add 0 (alu .add (c.get 11) a)) 0x8001d3ae
  let c14 := c13.wr 12 (alu .add 0 (alu .sub v a)) 0x8001d3b0
  let c15 := c14.wr 1 (0x8001d3b0 + 0x4000#32) 0x8001d3b4
  have q1 : Quiet c1 := Quiet.of_sameCsr (Core.sameCsr_wr _ _ _ _) hq
  have qg1 : ∀ p, Quiet (c1.goto p) := fun p => Quiet.of_sameCsr (Core.sameCsr_goto _ _) q1
  have q5 : Quiet c5 := Quiet.of_sameCsr (Core.sameCsr_wr _ _ _ _) (qg1 _)
  have qg5 : ∀ p, Quiet (c5.goto p) := fun p => Quiet.of_sameCsr (Core.sameCsr_goto _ _) q5
  have q6 : Quiet c6 := Quiet.of_sameCsr (Core.sameCsr_wr _ _ _ _) (qg5 _)
  have q7 : Quiet c7 := Quiet.of_sameCsr (Core.sameCsr_wr _ _ _ _) q6
  have qg7 : ∀ p, Quiet (c7.goto p) := fun p => Quiet.of_sameCsr (Core.sameCsr_goto _ _) q7
  have q9 : Quiet c9 := Quiet.of_sameCsr (Core.sameCsr_wr _ _ _ _) (qg7 _)
  have q10 : Quiet c10 := Quiet.of_sameCsr (Core.sameCsr_wr _ _ _ _) q9
  have q11 : Quiet c11 := Quiet.of_sameCsr (Core.sameCsr_wr _ _ _ _) q10
  have q12 : Quiet c12 := Quiet.of_sameCsr (Core.sameCsr_wr _ _ _ _) q11
  have q13 : Quiet c13 := Quiet.of_sameCsr (Core.sameCsr_wr _ _ _ _) q12
  have q14 : Quiet c14 := Quiet.of_sameCsr (Core.sameCsr_wr _ _ _ _) q13
  have q15 : Quiet c15 := Quiet.of_sameCsr (Core.sameCsr_wr _ _ _ _) q14
  have g2 : ∀ p, (c1.goto p).get 2 = pfp c := fun p => by simp [c1, Core.wr_get_self]
  have gk : ∀ p (r : Reg), r ≠ 2 → (c1.goto p).get r = c.get r := fun p r h => by
    simp [c1, Core.wr_get_ne, h]
  have s0 : DetStep B img ⟨c, ram⟩ ⟨c1, ram⟩ := by
    refine detStep_of (by rw [hpc]; decide) (by rw [hpc]; exact f8001d388) fun o => ?_
    rw [exec_opimm, hpc]; rfl
  have s1 : DetStep B img ⟨c1, ram⟩ ⟨c1.goto 0x8001d38c, W1⟩ := by
    refine detStep_of (by show (0x8001d38a : Word).getLsbD 0 = false; decide) f8001d38a fun o => ?_
    rw [exec_store]
    have e2 : c1.get 2 = pfp c := by simp [c1, Core.wr_get_self]
    have e1 : c1.get 1 = c.get 1 := by simp [c1, Core.wr_get_ne]
    rw [e2, e1, interp_store_ram (w := .w) o (F.slot_al 0xc (by decide)) (F.slot_in 0xc (by decide))]; rfl
  have s2 : DetStep B img ⟨c1.goto 0x8001d38c, W1⟩ ⟨c1.goto 0x8001d38e, W2⟩ := by
    refine detStep_of (by show (0x8001d38c : Word).getLsbD 0 = false; decide) f8001d38c fun o => ?_
    rw [exec_store, g2, gk _ 8 (by decide),
      interp_store_ram (w := .w) o (F.slot_al 0x8 (by decide)) (F.slot_in 0x8 (by decide))]; rfl
  have s3 : DetStep B img ⟨c1.goto 0x8001d38e, W2⟩ ⟨c1.goto 0x8001d390, PS⟩ := by
    refine detStep_of (by show (0x8001d38e : Word).getLsbD 0 = false; decide) f8001d38e fun o => ?_
    rw [exec_store, g2, gk _ 9 (by decide),
      interp_store_ram (w := .w) o (F.slot_al 0x4 (by decide)) (F.slot_in 0x4 (by decide))]; rfl
  have s4 : DetStep B img ⟨c1.goto 0x8001d390, PS⟩ ⟨c5, PS⟩ := by
    refine detStep_of (by show (0x8001d390 : Word).getLsbD 0 = false; decide) f8001d390 fun o => ?_
    rw [exec_load, gk _ 10 (by decide),
      interp_load_ram (w := .w) o (show (c.get 10 + 0x4#32).toNat % 4 = 0 by bv_omega)
        ((B_ram _ _).mpr ⟨by bv_omega, show (c.get 10 + 0x4#32).toNat + 4 ≤ _ by bv_omega⟩)]; rfl
  have s5 : DetStep B img ⟨c5, PS⟩ ⟨c5.goto 0x8001d396, PS⟩ := by
    refine detStep_of (by show (0x8001d392 : Word).getLsbD 0 = false; decide) f8001d392 fun o => ?_
    rw [exec_branch]
    have h12 : c5.get 12 = c.get 12 := by simp [c5, Core.wr_get_ne, gk]
    have h14 : c5.get 14 = ramRead (psave c ram) (c.get 10 + 0x4#32) .w := by simp [c5, Core.wr_get_self, v, PS]
    have hn : (c.get 12).ult (ramRead (psave c ram) (c.get 10 + 0x4#32) .w) = false := by
      simp only [BitVec.ult, decide_eq_false_iff_not]; omega
    rw [h12, h14]; simp only [taken, hn, Bool.false_eq_true, ite_false]; rfl
  have s6 : DetStep B img ⟨c5.goto 0x8001d396, PS⟩ ⟨c6, PS⟩ := by
    refine detStep_of (by show (0x8001d396 : Word).getLsbD 0 = false; decide) f8001d396 fun o => ?_
    rw [exec_op, Core.get_zero]
    have : (c5.goto 0x8001d396).get 10 = c.get 10 := by simp [c5, Core.wr_get_ne, gk]
    rw [this]; rfl
  have s7 : DetStep B img ⟨c6, PS⟩ ⟨c7, PS⟩ := by
    refine detStep_of (by show (0x8001d398 : Word).getLsbD 0 = false; decide) f8001d398 fun o => ?_
    rw [exec_load]
    have : c6.get 10 = c.get 10 := by simp [c6, c5, Core.wr_get_ne, gk]
    rw [this, BitVec.add_zero,
      interp_load_ram (w := .w) o hal ((B_ram _ _).mpr ⟨hp.1, show (c.get 10).toNat + 4 ≤ _ by omega⟩)]; rfl
  have s8 : DetStep B img ⟨c7, PS⟩ ⟨c7.goto 0x8001d39e, PS⟩ := by
    refine detStep_of (by show (0x8001d39a : Word).getLsbD 0 = false; decide) f8001d39a fun o => ?_
    rw [exec_branch]
    have h14 : c7.get 14 = ramRead (psave c ram) (c.get 10 + 0x4#32) .w := by
      simp [c7, c6, c5, Core.wr_get_ne, Core.wr_get_self, v, PS]
    have h10 : c7.get 10 = ramRead (psave c ram) (c.get 10) .w := by simp [c7, Core.wr_get_self, a, PS]
    have hn : (ramRead (psave c ram) (c.get 10 + 0x4#32) .w).ult (ramRead (psave c ram) (c.get 10) .w) = false := by
      simp only [BitVec.ult, decide_eq_false_iff_not]; omega
    rw [h14, h10]; simp only [taken, hn, Bool.false_eq_true, ite_false]; rfl
  have s9 : DetStep B img ⟨c7.goto 0x8001d39e, PS⟩ ⟨c9, PS⟩ := by
    refine detStep_of (by show (0x8001d39e : Word).getLsbD 0 = false; decide) f8001d39e fun o => ?_
    rw [exec_op]
    have h14 : (c7.goto 0x8001d39e).get 14 = v := by simp [c7, c6, c5, Core.wr_get_ne, Core.wr_get_self]
    have h10 : (c7.goto 0x8001d39e).get 10 = a := by simp [c7, Core.wr_get_self]
    rw [h14, h10]; rfl
  have s10 : DetStep B img ⟨c9, PS⟩ ⟨c10, PS⟩ := by
    refine detStep_of (by show (0x8001d3a2 : Word).getLsbD 0 = false; decide) f8001d3a2 fun o => ?_
    rw [exec_op]
    have h11 : c9.get 11 = c.get 11 := by simp [c9, c7, c6, c5, Core.wr_get_ne, gk]
    have h10 : c9.get 10 = a := by simp [c9, c7, Core.wr_get_ne, Core.wr_get_self]
    rw [h11, h10]; rfl
  have s11 : DetStep B img ⟨c10, PS⟩ ⟨c11, PS⟩ := by
    refine detStep_of (by show (0x8001d3a6 : Word).getLsbD 0 = false; decide) f8001d3a6 fun o => ?_
    rw [exec_op]
    have h11 : c10.get 11 = c.get 11 := by simp [c10, c9, c7, c6, c5, Core.wr_get_ne, gk]
    have h12 : c10.get 12 = c.get 12 := by simp [c10, c9, c7, c6, c5, Core.wr_get_ne, gk]
    rw [h11, h12]; rfl
  have s12 : DetStep B img ⟨c11, PS⟩ ⟨c12, PS⟩ := by
    refine detStep_of (by show (0x8001d3aa : Word).getLsbD 0 = false; decide) f8001d3aa fun o => ?_
    rw [exec_op]
    have h10 : c11.get 10 = alu .add (c.get 11) (c.get 12) := by simp [c11, Core.wr_get_self]
    have h9 : c11.get 9 = alu .sub v a := by simp [c11, c10, c9, Core.wr_get_ne, Core.wr_get_self]
    rw [h10, h9]; rfl
  have s13 : DetStep B img ⟨c12, PS⟩ ⟨c13, PS⟩ := by
    refine detStep_of (by show (0x8001d3ac : Word).getLsbD 0 = false; decide) f8001d3ac fun o => ?_
    rw [exec_op, Core.get_zero]
    have h13 : c12.get 13 = alu .add (c.get 11) a := by simp [c12, c11, c10, Core.wr_get_ne, Core.wr_get_self]
    rw [h13]; rfl
  have s14 : DetStep B img ⟨c13, PS⟩ ⟨c14, PS⟩ := by
    refine detStep_of (by show (0x8001d3ae : Word).getLsbD 0 = false; decide) f8001d3ae fun o => ?_
    rw [exec_op, Core.get_zero]
    have h9 : c13.get 9 = alu .sub v a := by simp [c13, c12, c11, c10, c9, Core.wr_get_ne, Core.wr_get_self]
    rw [h9]; rfl
  have s15 : DetStep B img ⟨c14, PS⟩ ⟨c15, PS⟩ := by
    refine detStep_of (by show (0x8001d3b0 : Word).getLsbD 0 = false; decide) f8001d3b0 fun o => ?_
    rw [exec_auipc]; rfl
  have s16 : DetStep B img ⟨c15, PS⟩ ⟨pcall c ram, PS⟩ := by
    refine detStep_of (by show (0x8001d3b4 : Word).getLsbD 0 = false; decide) f8001d3b4 fun o => ?_
    rw [exec_jalr]
    have h1 : c15.get 1 = 0x8001d3b0 + 0x4000#32 := by simp [c15, Core.wr_get_self]
    rw [h1, show (0x8001d3b0 : Word) + 0x4000#32 + 0xfffff86e#32 &&& ~~~1 = 0x80020c1e by decide,
      jump_ok _ _ (by decide)]; rfl
  exact .step hq s0 (.step q1 s1 (.step (qg1 _) s2 (.step (qg1 _) s3 (.step (qg1 _) s4 (.step q5 s5
    (.step (qg5 _) s6 (.step q6 s7 (.step q7 s8 (.step (qg7 _) s9 (.step q9 s10 (.step q10 s11
    (.step q11 s12 (.step q12 s13 (.step q13 s14 (.step q14 s15 (.single q15 s16))))))))))))))))

/-! ## After the call: 0x8001d3b8 .. 0x8001d3ca -/

/-- RAM after `sw zero, 0(s0); sw zero, 4(s0)`. -/
def pstore (M : Word → BitVec 8) (p : Word) : Word → BitVec 8 :=
  ramWrite (ramWrite M p 0 .w) (p + 0x4#32) 0 .w

/-- The core `ret` reaches: a0 = s1, ra, s0, s1 from the slots, sp = f + 0x10. -/
def pfin (e : Core) (R : Word → BitVec 8) (f n : Word) : Core :=
  (((((e.goto 0x8001d3c0).wr 10 (alu .add 0 n) 0x8001d3c2).wr 1 (ramRead R (f + 0xc#32) .w) 0x8001d3c4).wr 8
    (ramRead R (f + 0x8#32) .w) 0x8001d3c6).wr 9 (ramRead R (f + 0x4#32) .w) 0x8001d3c8).wr 2 (f + 0x10#32)
    0x8001d3ca |>.goto (ramRead R (f + 0xc#32) .w)

theorem pfin_sameCsr (e R f n) : (pfin e R f n).sameCsr e := by
  unfold pfin
  repeat (first | exact Core.sameCsr_goto _ _ | refine (Core.sameCsr_wr _ _ _ _).trans ?_ | refine (Core.sameCsr_goto _ _).trans ?_)

theorem pfin_get1 (e R f n) : (pfin e R f n).get 1 = ramRead R (f + 0xc#32) .w := by
  simp [pfin, Core.wr_get_ne, Core.wr_get_self]
theorem pfin_get2 (e R f n) : (pfin e R f n).get 2 = f + 0x10#32 := by
  simp [pfin, Core.wr_get_ne, Core.wr_get_self]
theorem pfin_get8 (e R f n) : (pfin e R f n).get 8 = ramRead R (f + 0x8#32) .w := by
  simp [pfin, Core.wr_get_ne, Core.wr_get_self]
theorem pfin_get9 (e R f n) : (pfin e R f n).get 9 = ramRead R (f + 0x4#32) .w := by
  simp [pfin, Core.wr_get_ne, Core.wr_get_self]
theorem pfin_get10 (e R f n) : (pfin e R f n).get 10 = n := by
  simp [pfin, Core.wr_get_ne, Core.wr_get_self, alu_add]
theorem pfin_get (e R f n) (r : Reg) (h1 : r ≠ 1) (h2 : r ≠ 2) (h8 : r ≠ 8) (h9 : r ≠ 9) (h10 : r ≠ 10) :
    (pfin e R f n).get r = e.get r := by
  simp [pfin, Core.wr_get_ne, h1, h2, h8, h9, h10]

theorem postrun (e : Core) (M : Word → BitVec 8) (p f n : Word) (hpc : e.pc = 0x8001d3b8) (hq : Quiet e)
    (h8 : e.get 8 = p) (h9 : e.get 9 = n) (h2 : e.get 2 = f) (F : FP16 f)
    (hal : p.toNat % 4 = 0) (hp : B.inRam p 12 = true)
    (hra : (ramRead (pstore M p) (f + 0xc#32) .w).getLsbD 0 = false) :
    QRun B img 8 ⟨e, M⟩ ⟨pfin e (pstore M p) f n, pstore M p⟩ := by
  have hp' := (B_ram _ _).mp hp
  let R := pstore M p
  have qg : ∀ t, Quiet (e.goto t) := fun t => Quiet.of_sameCsr (Core.sameCsr_goto _ _) hq
  let d3 := (e.goto 0x8001d3c0).wr 10 (alu .add 0 n) 0x8001d3c2
  let d4 := d3.wr 1 (ramRead R (f + 0xc#32) .w) 0x8001d3c4
  let d5 := d4.wr 8 (ramRead R (f + 0x8#32) .w) 0x8001d3c6
  let d6 := d5.wr 9 (ramRead R (f + 0x4#32) .w) 0x8001d3c8
  let d7 := d6.wr 2 (f + 0x10#32) 0x8001d3ca
  have q3 : Quiet d3 := Quiet.of_sameCsr (Core.sameCsr_wr _ _ _ _) (qg _)
  have q4 : Quiet d4 := Quiet.of_sameCsr (Core.sameCsr_wr _ _ _ _) q3
  have q5 : Quiet d5 := Quiet.of_sameCsr (Core.sameCsr_wr _ _ _ _) q4
  have q6 : Quiet d6 := Quiet.of_sameCsr (Core.sameCsr_wr _ _ _ _) q5
  have q7 : Quiet d7 := Quiet.of_sameCsr (Core.sameCsr_wr _ _ _ _) q6
  have d3sp : ∀ (d : Core), d = d3 ∨ d = d4 ∨ d = d5 ∨ d = d6 → d.get 2 = f := by
    intro d hd; rcases hd with rfl | rfl | rfl | rfl <;> simp [d6, d5, d4, d3, Core.wr_get_ne, h2]
  have s0 : DetStep B img ⟨e, M⟩ ⟨e.goto 0x8001d3bc, ramWrite M p 0 .w⟩ := by
    refine detStep_of (by rw [hpc]; decide) (by rw [hpc]; exact f8001d3b8) fun o => ?_
    rw [exec_store, h8, Core.get_zero, BitVec.add_zero,
      interp_store_ram (w := .w) o hal ((B_ram _ _).mpr ⟨hp'.1, show p.toNat + 4 ≤ _ by omega⟩), hpc]; rfl
  have s1 : DetStep B img ⟨e.goto 0x8001d3bc, ramWrite M p 0 .w⟩ ⟨e.goto 0x8001d3c0, R⟩ := by
    refine detStep_of (by show (0x8001d3bc : Word).getLsbD 0 = false; decide) f8001d3bc fun o => ?_
    rw [exec_store, Core.goto_get, Core.get_zero, h8,
      interp_store_ram (w := .w) o (show (p + 0x4#32).toNat % 4 = 0 by bv_omega)
        ((B_ram _ _).mpr ⟨by bv_omega, show (p + 0x4#32).toNat + 4 ≤ _ by bv_omega⟩)]; rfl
  have s2 : DetStep B img ⟨e.goto 0x8001d3c0, R⟩ ⟨d3, R⟩ := by
    refine detStep_of (by show (0x8001d3c0 : Word).getLsbD 0 = false; decide) f8001d3c0 fun o => ?_
    rw [exec_op, Core.get_zero, Core.goto_get, h9]; rfl
  have s3 : DetStep B img ⟨d3, R⟩ ⟨d4, R⟩ := by
    refine detStep_of (by show (0x8001d3c2 : Word).getLsbD 0 = false; decide) f8001d3c2 fun o => ?_
    rw [exec_load, d3sp d3 (.inl rfl),
      interp_load_ram (w := .w) o (F.slot_al 0xc (by decide)) (F.slot_in 0xc (by decide))]; rfl
  have s4 : DetStep B img ⟨d4, R⟩ ⟨d5, R⟩ := by
    refine detStep_of (by show (0x8001d3c4 : Word).getLsbD 0 = false; decide) f8001d3c4 fun o => ?_
    rw [exec_load, d3sp d4 (.inr (.inl rfl)),
      interp_load_ram (w := .w) o (F.slot_al 0x8 (by decide)) (F.slot_in 0x8 (by decide))]; rfl
  have s5 : DetStep B img ⟨d5, R⟩ ⟨d6, R⟩ := by
    refine detStep_of (by show (0x8001d3c6 : Word).getLsbD 0 = false; decide) f8001d3c6 fun o => ?_
    rw [exec_load, d3sp d5 (.inr (.inr (.inl rfl))),
      interp_load_ram (w := .w) o (F.slot_al 0x4 (by decide)) (F.slot_in 0x4 (by decide))]; rfl
  have s6 : DetStep B img ⟨d6, R⟩ ⟨d7, R⟩ := by
    refine detStep_of (by show (0x8001d3c8 : Word).getLsbD 0 = false; decide) f8001d3c8 fun o => ?_
    rw [exec_opimm, d3sp d6 (.inr (.inr (.inr rfl)))]; rfl
  have s7 : DetStep B img ⟨d7, R⟩ ⟨pfin e R f n, R⟩ := by
    refine detStep_of (by show (0x8001d3ca : Word).getLsbD 0 = false; decide) f8001d3ca fun o => ?_
    rw [exec_jalr, Core.set_zero]
    have : d7.get 1 = ramRead R (f + 0xc#32) .w := by simp [d7, d6, d5, d4, Core.wr_get_ne, Core.wr_get_self]
    rw [this, BitVec.add_zero, Memmove.and_not_one _ hra, jump_ok _ _ hra]; rfl
  exact .step hq s0 (.step (qg _) s1 (.step (qg _) s2 (.step q3 s3 (.step q4 s4 (.step q5 s5
    (.step q6 s6 (.single q7 s7)))))))

theorem pstore_other (M : Word → BitVec 8) (p x : Word) (hp : p.toNat + 12 ≤ 2 ^ 32)
    (hx : x.toNat < p.toNat ∨ p.toNat + 8 ≤ x.toNat) : pstore M p x = M x := by
  unfold pstore
  have e4 : (p + 0x4#32).toNat = p.toNat + 4 := add_toNat p 4 (by omega)
  rw [wr_byte_other _ _ _ _ (by omega) (by omega), wr_byte_other _ _ _ _ (by omega) (by omega)]

theorem pstore_consumed (M : Word → BitVec 8) (p : Word) (hp : p.toNat + 12 ≤ 2 ^ 32) :
    ramRead (pstore M p) p .w = 0 := by
  unfold pstore
  have e4 : (p + 0x4#32).toNat = p.toNat + 4 := add_toNat p 4 (by omega)
  rw [rd_wr_other _ _ _ _ (by omega) (by omega) (by omega), ramRead_ramWrite_w]

theorem pstore_filled (M : Word → BitVec 8) (p : Word) : ramRead (pstore M p) (p + 0x4#32) .w = 0 := by
  unfold pstore; rw [ramRead_ramWrite_w]

/-- Where `moved` reads byte `j` of the parked bytes from. -/
theorem park_addr (buf len n a : Word) (j : Nat) (hb : buf.toNat + len.toNat < 2 ^ 32)
    (hn : n.toNat ≤ len.toNat) (hj : j < n.toNat) (ha : a.toNat + n.toNat ≤ len.toNat) :
    (buf + a) + ((buf + BitVec.ofNat 32 (len.toNat - n.toNat + j)) - (buf + len - n)) =
      buf + BitVec.ofNat 32 (a.toNat + j) := by
  have hbl : (buf + len).toNat = buf.toNat + len.toNat := add_toNat' _ _ hb
  have hd : (buf + len - n).toNat = buf.toNat + len.toNat - n.toNat := by
    rw [sub_toNat _ _ (by omega), hbl]
  have hx : (buf + BitVec.ofNat 32 (len.toNat - n.toNat + j)).toNat = buf.toNat + (len.toNat - n.toNat + j) :=
    add_toNat _ _ (by omega)
  have hxd : ((buf + BitVec.ofNat 32 (len.toNat - n.toNat + j)) - (buf + len - n)).toNat = j := by
    rw [sub_toNat _ _ (by omega), hx, hd]; omega
  have hs : (buf + a).toNat = buf.toNat + a.toNat := add_toNat' _ _ (by omega)
  apply BitVec.eq_of_toNat_eq
  rw [add_toNat' _ _ (by rw [hs, hxd]; omega), hs, hxd, add_toNat _ _ (by omega)]; omega

/-! ## `park_pending` -/

theorem park_from_copy : ParkFromCopy := by
  intro hC m₀ E hI
  obtain ⟨c, R0⟩ := m₀
  have hpc : c.pc = 0x8001d388 := E.pc
  have hst := stack_nat (c.get 2) parkStack E.stack
  have hfr : parkStack = 0x40 := rfl
  rw [hfr] at hst
  have hs : 0x80029bc8 + 0x10 ≤ (c.get 2).toNat ∧ (c.get 2).toNat ≤ 0x81000000 := ⟨by omega, hst.2⟩
  have hp := (B_ram (c.get 10) 12).mp E.self
  have hb := (B_ram (c.get 11) (c.get 12).toNat).mp E.buf
  have hlen : (c.get 12).toNat = bufLen := E.len
  have hsep : (c.get 10).toNat + 12 ≤ (c.get 2).toNat - 0x40 ∧
      (c.get 11).toNat + (c.get 12).toNat ≤ (c.get 2).toNat - 0x40 := E.stackSep
  have hsep2 : (c.get 10).toNat + 12 ≤ (c.get 11).toNat ∨
      (c.get 11).toNat + (c.get 12).toNat ≤ (c.get 10).toNat := E.sep
  have hI : consumed R0 (c.get 10) ≤ filled R0 (c.get 10) ∧ filled R0 (c.get 10) ≤ (c.get 12).toNat := hI
  have F := pfp_FP c E.spAl hs
  have hfp := pfp_toNat c (by omega)
  let R := psave c R0
  let a := ramRead R (c.get 10) .w
  let v := ramRead R (c.get 10 + 0x4#32) .w
  have e4 : (c.get 10 + 0x4#32).toNat = (c.get 10).toNat + 4 := add_toNat _ 4 (by omega)
  have rc : a = ramRead R0 (c.get 10) .w := psave_rd c R0 hs _ (by omega)
  have rf : v = ramRead R0 (c.get 10 + 0x4#32) .w := psave_rd c R0 hs _ (by omega)
  have ca : consumed R0 (c.get 10) = a.toNat := by rw [rc]; rfl
  have fv : filled R0 (c.get 10) = v.toNat := by rw [rf]; rfl
  have hle : v.toNat ≤ (c.get 12).toNat := fv ▸ hI.2
  have hcf : a.toNat ≤ v.toNat := ca ▸ fv ▸ hI.1
  let n := v - a
  have hn : n.toNat = v.toNat - a.toNat := sub_toNat _ _ hcf
  let L := c.get 11 + c.get 12
  have hL : L.toNat = (c.get 11).toNat + (c.get 12).toNat := add_toNat' _ _ (by omega)
  have hdst : (L - n).toNat = (c.get 11).toNat + (c.get 12).toNat - n.toNat := by
    rw [sub_toNat _ _ (by omega), hL]
  have ea : (c.get 11 + a).toNat = (c.get 11).toNat + a.toNat := add_toNat' _ _ (by omega)
  have r1 := prerun c R0 hpc E.quiet E.selfAl E.self E.spAl hs hle hcf
  let K := pcall c R0
  have qK : Quiet K := Quiet.of_sameCsr (pcall_sameCsr c R0) E.quiet
  have hf16 : 0x30 ≤ (pfp c).toNat := by omega
  have env : CopyEnv ⟨K, R⟩ := by
    refine ⟨rfl, qK, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · show (K.get 12).toNat ≤ bufLen; rw [pcall_get12, ← hlen]; show n.toNat ≤ _; omega
    · show B.inRam (K.get 10) (K.get 12).toNat = true
      rw [pcall_get10, pcall_get12, B_ram]
      show 0x80029bc8 ≤ (L - n).toNat ∧ (L - n).toNat + n.toNat ≤ 0x81000000
      rw [hdst]; omega
    · show B.inRam (K.get 11) (K.get 12).toNat = true
      rw [pcall_get11, pcall_get12, B_ram]
      show 0x80029bc8 ≤ (c.get 11 + a).toNat ∧ (c.get 11 + a).toNat + n.toNat ≤ 0x81000000
      rw [ea]; omega
    · show B.inRam (K.get 2 - BitVec.ofNat 32 memmoveFrame) memmoveFrame = true
      rw [pcall_get2, B_ram, show memmoveFrame = 0x30 from rfl, sub_frame _ hf16]; omega
    · show (K.get 10).toNat + (K.get 12).toNat ≤ (K.get 2).toNat - memmoveFrame
      rw [pcall_get10, pcall_get12, pcall_get2]
      show (L - n).toNat + n.toNat ≤ (pfp c).toNat - 0x30
      rw [hdst]; omega
    · show (K.get 11).toNat + (K.get 12).toNat ≤ (K.get 2).toNat - memmoveFrame
      rw [pcall_get11, pcall_get12, pcall_get2]
      show (c.get 11 + a).toNat + n.toNat ≤ (pfp c).toNat - 0x30
      rw [ea]; omega
    · show (K.get 1).getLsbD 0 = false; rw [pcall_get1]; decide
    · show (K.get 2).toNat % 4 = 0; rw [pcall_get2]; exact F.al
  obtain ⟨kc, ⟨e, M⟩, rc2, P⟩ := hC _ env
  have Pregs : ∀ r : Reg, r.val ∉ [5, 6, 7, 11, 12, 13, 14, 15, 16, 17, 28, 29, 30, 31] → e.get r = K.get r :=
    P.regs
  have Pram : ∀ x, ¬ ((pfp c).toNat - 0x30 ≤ x.toNat ∧ x.toNat < (pfp c).toNat) →
      M x = Memmove.moved R (L - n) (c.get 11 + a) n.toNat x := by
    intro x hx
    have := P.ram x (show ¬ (((pcall c R0).get 2).toNat - memmoveFrame ≤ x.toNat ∧
      x.toNat < ((pcall c R0).get 2).toNat) by rw [pcall_get2]; exact hx)
    refine this.trans ?_
    show Memmove.moved R ((pcall c R0).get 10) ((pcall c R0).get 11) ((pcall c R0).get 12).toNat x = _
    rw [pcall_get10, pcall_get11, pcall_get12]
  have g8 : e.get 8 = c.get 10 := (Pregs 8 (by decide)).trans (pcall_get8 c R0)
  have g9 : e.get 9 = n := (Pregs 9 (by decide)).trans (pcall_get9 c R0)
  have g2 : e.get 2 = pfp c := (Pregs 2 (by decide)).trans (pcall_get2 c R0)
  have epc : e.pc = 0x8001d3b8 := P.pc.trans (pcall_get1 c R0)
  have qe : Quiet e := Quiet.of_sameCsr P.csr qK
  -- RAM after the call and the stores: outside the deframer, memmove's frame and the destination
  have keep : ∀ x : Word, (x.toNat < (c.get 10).toNat ∨ (c.get 10).toNat + 8 ≤ x.toNat) →
      ¬ ((pfp c).toNat - 0x30 ≤ x.toNat ∧ x.toNat < (pfp c).toNat) →
      ¬ ((L - n).toNat ≤ x.toNat ∧ x.toNat < (L - n).toNat + n.toNat) → pstore M (c.get 10) x = R x := by
    intro x h1 h2 h3
    rw [pstore_other M (c.get 10) x (by omega) h1, Pram x h2, Memmove.moved, if_neg h3]
  have slot : ∀ k : Nat, k = 0xc ∨ k = 0x8 ∨ k = 0x4 →
      ramRead (pstore M (c.get 10)) (pfp c + BitVec.ofNat 32 k) .w = ramRead R (pfp c + BitVec.ofNat 32 k) .w := by
    intro k hk
    have hk' : k + 4 ≤ 0x10 := by rcases hk with rfl | rfl | rfl <;> decide
    have ek : (pfp c + BitVec.ofNat 32 k).toNat = (pfp c).toNat + k := add_toNat _ k (by omega)
    apply rd_congr _ (by omega)
    intro x h1 h2
    exact keep x (.inr (by omega)) (by omega) (by rw [hdst]; omega)
  have hra : (ramRead (pstore M (c.get 10)) (pfp c + 0xc#32) .w).getLsbD 0 = false := by
    rw [slot 0xc (by decide), psave_c c R0 hs]; exact E.ra
  have r2 := postrun e M (c.get 10) (pfp c) n epc qe g8 g9 g2 F E.selfAl E.self hra
  refine ⟨_, _, (r1.trans rc2).trans r2, ?_⟩
  have hcons : consumed (pstore M (c.get 10)) (c.get 10) = 0 := by
    show (ramRead (pstore M (c.get 10)) (c.get 10) .w).toNat = 0
    rw [pstore_consumed M _ (by omega)]; rfl
  have hfill : filled (pstore M (c.get 10)) (c.get 10) = 0 := by
    show (ramRead (pstore M (c.get 10)) (c.get 10 + 4) .w).toNat = 0
    exact congrArg BitVec.toNat (pstore_filled M (c.get 10))
  let T := pfin e (pstore M (c.get 10)) (pfp c) n
  refine ⟨?_, ?_, ?_, ?_, hcons, hfill, ?_, ?_, ?_⟩
  · show T.pc = c.get 1
    exact (slot 0xc (by decide)).trans (psave_c c R0 hs)
  · exact (pfin_sameCsr _ _ _ _).trans (P.csr.trans (pcall_sameCsr c R0))
  · exact (pfin_get2 _ _ _ _).trans (pfp_add c)
  · intro r hr
    show T.get r = c.get r
    by_cases h1 : r = 1
    · subst h1; exact (pfin_get1 _ _ _ _).trans ((slot 0xc (by decide)).trans (psave_c c R0 hs))
    by_cases h2 : r = 2
    · subst h2; exact (pfin_get2 _ _ _ _).trans (pfp_add c)
    by_cases h8 : r = 8
    · subst h8; exact (pfin_get8 _ _ _ _).trans ((slot 0x8 (by decide)).trans (psave_8 c R0 hs))
    by_cases h9 : r = 9
    · subst h9; exact (pfin_get9 _ _ _ _).trans ((slot 0x4 (by decide)).trans (psave_4 c R0))
    have hcs : r.val ∉ [5, 6, 7, 11, 12, 13, 14, 15, 16, 17, 28, 29, 30, 31] := fun hm =>
      hr (by simp only [callerSaved, List.mem_cons, List.not_mem_nil, or_false] at hm ⊢; omega)
    have h10 : r ≠ 10 := fun e => hr (by subst e; decide)
    have h11 : r ≠ 11 := fun e => hr (by subst e; decide)
    have h12 : r ≠ 12 := fun e => hr (by subst e; decide)
    have h13 : r ≠ 13 := fun e => hr (by subst e; decide)
    have h14 : r ≠ 14 := fun e => hr (by subst e; decide)
    rw [pfin_get _ _ _ _ r h1 h2 h8 h9 h10, Pregs r hcs, pcall_get c R0 r h1 h2 h8 h9 h10 h11 h12 h13 h14]
  · show (T.get 10).toNat = filled R0 (c.get 10) - consumed R0 (c.get 10)
    rw [pfin_get10, hn, ca, fv]
  · intro j hj
    rw [show (T.get 10) = n from pfin_get10 _ _ _ _] at hj ⊢
    show pstore M (c.get 10) (c.get 11 + BitVec.ofNat 32 ((c.get 12).toNat - n.toNat + j)) =
      R0 (c.get 11 + BitVec.ofNat 32 (consumed R0 (c.get 10) + j))
    have ex : (c.get 11 + BitVec.ofNat 32 ((c.get 12).toNat - n.toNat + j)).toNat =
        (c.get 11).toNat + ((c.get 12).toNat - n.toNat + j) := add_toNat _ _ (by omega)
    have hin : (L - n).toNat ≤ (c.get 11 + BitVec.ofNat 32 ((c.get 12).toNat - n.toNat + j)).toNat ∧
        (c.get 11 + BitVec.ofNat 32 ((c.get 12).toNat - n.toNat + j)).toNat < (L - n).toNat + n.toNat := by
      rw [ex, hdst]; omega
    rw [pstore_other M (c.get 10) _ (by omega) (by rw [ex]; omega), Pram _ (by rw [ex]; omega),
      Memmove.moved, if_pos hin, park_addr (c.get 11) (c.get 12) n a j (by omega) (by omega) hj (by omega), ca]
    have ek : (c.get 11 + BitVec.ofNat 32 (a.toNat + j)).toNat = (c.get 11).toNat + (a.toNat + j) :=
      add_toNat _ _ (by omega)
    have hx : (c.get 11 + BitVec.ofNat 32 (a.toNat + j)).toNat < (c.get 2).toNat - 0x10 := by rw [ek]; omega
    exact psave_other c R0 hs _ (.inl hx)
  · intro x hx
    show pstore M (c.get 10) x = R0 x
    have h1 : ¬ ((c.get 10).toNat ≤ x.toNat ∧ x.toNat < (c.get 10).toNat + 12) := hx.1
    have h2 : ¬ ((c.get 11).toNat ≤ x.toNat ∧ x.toNat < (c.get 11).toNat + (c.get 12).toNat) := hx.2.1
    have h3 : ¬ ((c.get 2).toNat - 0x40 ≤ x.toNat ∧ x.toNat < (c.get 2).toNat) := hx.2.2
    rw [keep x (by omega) (by omega) (by rw [hdst]; omega)]
    exact psave_other c R0 hs x (by omega)

end E5R.Rmk.Deframer.Park
