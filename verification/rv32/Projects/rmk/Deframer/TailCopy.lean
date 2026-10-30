/-
  `Deframer::tail` on the pinned RMK image: the path with a copy (consumed ≠ 0), proved against
  memmove's contract as an explicit hypothesis, and the whole of `tail` from both paths.

  Original e5r code, Apache-2.0.

  PROVED here, CONDITIONAL ON `CopyContract` (a hypothesis of every theorem below,
  not proved here; the peer's memmove proofs discharge it only for the cases `Memmove.PreB` allows,
  which do not yet cover every deframer call):
  * `withCopy`: from `TailPre frame` (frame ≥ 0x50: tail's 0x20 bytes and memmove's 0x30) with
    consumed ≠ 0, a quiet run reaches `TailPost frame`;
  * `tail_from_copy : TailFromCopy`, i.e. `CopyContract → TailContract tailStack`, with the
    consumed = 0 case from `Tail.nocopy` (which needs no hypothesis).
-/
import Projects.rmk.Deframer.TailNoCopy

set_option maxRecDepth 100000

namespace E5R.Rmk.Deframer.Tail
open E5R E5R.Rmk.TailFetch

/-! ## Before the call: 0x8001d58c .. 0x8001d5a4 -/

/-- The core at memmove's entry: a0 = buf, a1 = buf + consumed, a2 = s1 = filled - consumed,
    ra = 0x8001d5a8. -/
def tcall (c : Core) (ram : Word → BitVec 8) : Core :=
  let P := tpro c ram
  let a := ramRead (tsave c ram) (c.get 10) .w
  let v := ramRead (tsave c ram) (c.get 10 + 0x4#32) .w
  ((((((P.goto 0x8001d596).wr 9 (alu .sub v a) 0x8001d598).wr 11 (alu .add (c.get 11) a) 0x8001d59c).wr 10
    (alu .add 0 (c.get 11)) 0x8001d59e).wr 12 (alu .add 0 (alu .sub v a)) 0x8001d5a0).wr 1
    (0x8001d5a0 + 0x3000#32) 0x8001d5a4).wr 1 0x8001d5a8 0x80020c1e

theorem tcall_sameCsr (c ram) : (tcall c ram).sameCsr c :=
  (Core.sameCsr_wr _ _ _ _).trans ((Core.sameCsr_wr _ _ _ _).trans ((Core.sameCsr_wr _ _ _ _).trans ((Core.sameCsr_wr _ _ _ _).trans
    ((Core.sameCsr_wr _ _ _ _).trans ((Core.sameCsr_wr _ _ _ _).trans ((Core.sameCsr_goto _ _).trans
      (tpro_sameCsr c ram)))))))

theorem precall (c : Core) (ram : Word → BitVec 8) (hq : Quiet c)
    (ha : ramRead (tsave c ram) (c.get 10) .w ≠ 0)
    (hle : (ramRead (tsave c ram) (c.get 10 + 0x4#32) .w).toNat ≤ (c.get 12).toNat)
    (hcf : (ramRead (tsave c ram) (c.get 10) .w).toNat ≤ (ramRead (tsave c ram) (c.get 10 + 0x4#32) .w).toNat) :
    QRun B img 9 ⟨tpro c ram, tsave c ram⟩ ⟨tcall c ram, tsave c ram⟩ := by
  let P := tpro c ram
  let R := tsave c ram
  let a := ramRead R (c.get 10) .w
  let v := ramRead R (c.get 10 + 0x4#32) .w
  have qP : Quiet P := Quiet.of_sameCsr (tpro_sameCsr c ram) hq
  have qg : ∀ p, Quiet (P.goto p) := fun p => Quiet.of_sameCsr (Core.sameCsr_goto _ _) qP
  let k4 := (P.goto 0x8001d596).wr 9 (alu .sub v a) 0x8001d598
  let k5 := k4.wr 11 (alu .add (c.get 11) a) 0x8001d59c
  let k6 := k5.wr 10 (alu .add 0 (c.get 11)) 0x8001d59e
  let k7 := k6.wr 12 (alu .add 0 (alu .sub v a)) 0x8001d5a0
  let k8 := k7.wr 1 (0x8001d5a0 + 0x3000#32) 0x8001d5a4
  have q4 : Quiet k4 := Quiet.of_sameCsr (Core.sameCsr_wr _ _ _ _) (qg _)
  have q5 : Quiet k5 := Quiet.of_sameCsr (Core.sameCsr_wr _ _ _ _) q4
  have q6 : Quiet k6 := Quiet.of_sameCsr (Core.sameCsr_wr _ _ _ _) q5
  have q7 : Quiet k7 := Quiet.of_sameCsr (Core.sameCsr_wr _ _ _ _) q6
  have q8 : Quiet k8 := Quiet.of_sameCsr (Core.sameCsr_wr _ _ _ _) q7
  have s0 : DetStep B img ⟨P, R⟩ ⟨P.goto 0x8001d58e, R⟩ := by
    refine detStep_of (by show (0x8001d58c : Word).getLsbD 0 = false; decide) f8001d58c fun o => ?_
    rw [exec_branch, Core.get_zero, tpro_get10]
    have : taken .eq (ramRead (tsave c ram) (c.get 10) .w) 0 = false := by
      simp only [taken, beq_eq_false_iff_ne]; exact ha
    rw [this]; rfl
  have s1 : DetStep B img ⟨P.goto 0x8001d58e, R⟩ ⟨P.goto 0x8001d592, R⟩ := by
    refine detStep_of (by show (0x8001d58e : Word).getLsbD 0 = false; decide) f8001d58e fun o => ?_
    rw [exec_branch, Core.goto_get, Core.goto_get, tpro_get18, tpro_get9]
    have hn : (c.get 12).ult (ramRead (tsave c ram) (c.get 10 + 0x4#32) .w) = false := by
      simp only [BitVec.ult, decide_eq_false_iff_not]; omega
    simp only [taken, hn, Bool.false_eq_true, ite_false]; rfl
  have s2 : DetStep B img ⟨P.goto 0x8001d592, R⟩ ⟨P.goto 0x8001d596, R⟩ := by
    refine detStep_of (by show (0x8001d592 : Word).getLsbD 0 = false; decide) f8001d592 fun o => ?_
    rw [exec_branch, Core.goto_get, Core.goto_get, tpro_get9, tpro_get10]
    have hn : (ramRead (tsave c ram) (c.get 10 + 0x4#32) .w).ult (ramRead (tsave c ram) (c.get 10) .w) = false := by
      simp only [BitVec.ult, decide_eq_false_iff_not]; omega
    simp only [taken, hn, Bool.false_eq_true, ite_false]; rfl
  have s3 : DetStep B img ⟨P.goto 0x8001d596, R⟩ ⟨k4, R⟩ := by
    refine detStep_of (by show (0x8001d596 : Word).getLsbD 0 = false; decide) f8001d596 fun o => ?_
    rw [exec_op, Core.goto_get, Core.goto_get, tpro_get9, tpro_get10]; rfl
  have s4 : DetStep B img ⟨k4, R⟩ ⟨k5, R⟩ := by
    refine detStep_of (by show (0x8001d598 : Word).getLsbD 0 = false; decide) f8001d598 fun o => ?_
    rw [exec_op]
    have h19 : k4.get 19 = c.get 11 := by simp [k4, P, Core.wr_get_ne, tpro_get19]
    have h10 : k4.get 10 = a := by simp [k4, P, Core.wr_get_ne, tpro_get10, a, R]
    rw [h19, h10]; rfl
  have s5 : DetStep B img ⟨k5, R⟩ ⟨k6, R⟩ := by
    refine detStep_of (by show (0x8001d59c : Word).getLsbD 0 = false; decide) f8001d59c fun o => ?_
    rw [exec_op, Core.get_zero]
    have h19 : k5.get 19 = c.get 11 := by simp [k5, k4, P, Core.wr_get_ne, tpro_get19]
    rw [h19]; rfl
  have s6 : DetStep B img ⟨k6, R⟩ ⟨k7, R⟩ := by
    refine detStep_of (by show (0x8001d59e : Word).getLsbD 0 = false; decide) f8001d59e fun o => ?_
    rw [exec_op, Core.get_zero]
    have h9 : k6.get 9 = alu .sub v a := by simp [k6, k5, k4, Core.wr_get_ne, Core.wr_get_self]
    rw [h9]; rfl
  have s7 : DetStep B img ⟨k7, R⟩ ⟨k8, R⟩ := by
    refine detStep_of (by show (0x8001d5a0 : Word).getLsbD 0 = false; decide) f8001d5a0 fun o => ?_
    rw [exec_auipc]; rfl
  have s8 : DetStep B img ⟨k8, R⟩ ⟨tcall c ram, R⟩ := by
    refine detStep_of (by show (0x8001d5a4 : Word).getLsbD 0 = false; decide) f8001d5a4 fun o => ?_
    rw [exec_jalr]
    have h1 : k8.get 1 = 0x8001d5a0 + 0x3000#32 := by simp [k8, Core.wr_get_self]
    rw [h1, show (0x8001d5a0 : Word) + 0x3000#32 + 0x67e#32 &&& ~~~1 = 0x80020c1e by decide,
      jump_ok _ _ (by decide)]; rfl
  exact .step qP s0 (.step (qg _) s1 (.step (qg _) s2 (.step (qg _) s3 (.step q4 s4 (.step q5 s5
    (.step q6 s6 (.step q7 s7 (.single q8 s8))))))))

theorem tcall_get2 (c ram) : (tcall c ram).get 2 = fp c := by
  simp [tcall, Core.wr_get_ne, tpro_get2]
theorem tcall_get8 (c ram) : (tcall c ram).get 8 = c.get 10 := by
  simp [tcall, Core.wr_get_ne, tpro_get8]
theorem tcall_get9 (c ram) : (tcall c ram).get 9 =
    ramRead (tsave c ram) (c.get 10 + 0x4#32) .w - ramRead (tsave c ram) (c.get 10) .w := by
  simp [tcall, Core.wr_get_ne, Core.wr_get_self, alu_sub]
theorem tcall_get10 (c ram) : (tcall c ram).get 10 = c.get 11 := by
  simp [tcall, Core.wr_get_ne, Core.wr_get_self, alu_add]
theorem tcall_get11 (c ram) : (tcall c ram).get 11 = c.get 11 + ramRead (tsave c ram) (c.get 10) .w := by
  simp [tcall, Core.wr_get_ne, Core.wr_get_self, alu_add]
theorem tcall_get12 (c ram) : (tcall c ram).get 12 =
    ramRead (tsave c ram) (c.get 10 + 0x4#32) .w - ramRead (tsave c ram) (c.get 10) .w := by
  simp [tcall, Core.wr_get_ne, Core.wr_get_self, alu_add, alu_sub]
theorem tcall_get1 (c ram) : (tcall c ram).get 1 = 0x8001d5a8 := by
  simp [tcall, Core.wr_get_self]
theorem tcall_get18 (c ram) : (tcall c ram).get 18 = c.get 12 := by
  simp [tcall, Core.wr_get_ne, tpro_get18]
theorem tcall_get19 (c ram) : (tcall c ram).get 19 = c.get 11 := by
  simp [tcall, Core.wr_get_ne, tpro_get19]
theorem tcall_get (c ram) (r : Reg) (h1 : r ≠ 1) (h2 : r ≠ 2) (h8 : r ≠ 8) (h9 : r ≠ 9) (h10 : r ≠ 10)
    (h11 : r ≠ 11) (h12 : r ≠ 12) (h18 : r ≠ 18) (h19 : r ≠ 19) : (tcall c ram).get r = c.get r := by
  simp [tcall, Core.wr_get_ne, h1, h9, h10, h11, h12, tpro_get c ram r h2 h8 h9 h10 h18 h19]

/-! ## After the call: 0x8001d5a8 .. 0x8001d5ba -/

/-- RAM after `sw zero, 0(s0); sw s1, 4(s0)`. -/
def tstore (M : Word → BitVec 8) (p n : Word) : Word → BitVec 8 :=
  ramWrite (ramWrite M p 0 .w) (p + 0x4#32) n .w

/-- The core at 0x8001d5ba after the call: a1 = len - n, a0 = buf + n. -/
def tafter (e : Core) (len buf n : Word) : Core :=
  ((e.goto 0x8001d5b2).wr 11 (alu .sub len n) 0x8001d5b6).wr 10 (alu .add buf n) 0x8001d5ba

theorem postcall (e : Core) (M : Word → BitVec 8) (p len buf n : Word) (hpc : e.pc = 0x8001d5a8)
    (hq : Quiet e) (h8 : e.get 8 = p) (h9 : e.get 9 = n) (h18 : e.get 18 = len) (h19 : e.get 19 = buf)
    (hal : p.toNat % 4 = 0) (hp : B.inRam p 12 = true) (hn : n.toNat ≤ len.toNat) :
    QRun B img 5 ⟨e, M⟩ ⟨tafter e len buf n, tstore M p n⟩ := by
  have hp' := (B_ram _ _).mp hp
  have qg : ∀ t, Quiet (e.goto t) := fun t => Quiet.of_sameCsr (Core.sameCsr_goto _ _) hq
  let e4 := (e.goto 0x8001d5b2).wr 11 (alu .sub len n) 0x8001d5b6
  have q4 : Quiet e4 := Quiet.of_sameCsr (Core.sameCsr_wr _ _ _ _) (qg _)
  have s0 : DetStep B img ⟨e, M⟩ ⟨e.goto 0x8001d5ac, ramWrite M p 0 .w⟩ := by
    refine detStep_of (by rw [hpc]; decide) (by rw [hpc]; exact f8001d5a8) fun o => ?_
    rw [exec_store, h8, Core.get_zero, BitVec.add_zero,
      interp_store_ram (w := .w) o hal ((B_ram _ _).mpr ⟨hp'.1, show p.toNat + 4 ≤ _ by omega⟩), hpc]; rfl
  have s1 : DetStep B img ⟨e.goto 0x8001d5ac, ramWrite M p 0 .w⟩ ⟨e.goto 0x8001d5ae, tstore M p n⟩ := by
    refine detStep_of (by show (0x8001d5ac : Word).getLsbD 0 = false; decide) f8001d5ac fun o => ?_
    rw [exec_store, Core.goto_get, Core.goto_get, h8, h9,
      interp_store_ram (w := .w) o (show (p + 0x4#32).toNat % 4 = 0 by bv_omega)
        ((B_ram _ _).mpr ⟨by bv_omega, show (p + 0x4#32).toNat + 4 ≤ _ by bv_omega⟩)]; rfl
  have s2 : DetStep B img ⟨e.goto 0x8001d5ae, tstore M p n⟩ ⟨e.goto 0x8001d5b2, tstore M p n⟩ := by
    refine detStep_of (by show (0x8001d5ae : Word).getLsbD 0 = false; decide) f8001d5ae fun o => ?_
    rw [exec_branch, Core.goto_get, Core.goto_get, h18, h9]
    have hb : len.ult n = false := by simp only [BitVec.ult, decide_eq_false_iff_not]; omega
    simp only [taken, hb, Bool.false_eq_true, ite_false]; rfl
  have s3 : DetStep B img ⟨e.goto 0x8001d5b2, tstore M p n⟩ ⟨e4, tstore M p n⟩ := by
    refine detStep_of (by show (0x8001d5b2 : Word).getLsbD 0 = false; decide) f8001d5b2 fun o => ?_
    rw [exec_op, Core.goto_get, Core.goto_get, h18, h9]; rfl
  have s4 : DetStep B img ⟨e4, tstore M p n⟩ ⟨tafter e len buf n, tstore M p n⟩ := by
    refine detStep_of (by show (0x8001d5b6 : Word).getLsbD 0 = false; decide) f8001d5b6 fun o => ?_
    rw [exec_op]
    have g19 : e4.get 19 = buf := by simp [e4, Core.wr_get_ne, h19]
    have g9 : e4.get 9 = n := by simp [e4, Core.wr_get_ne, h9]
    rw [g19, g9]; rfl
  exact .step hq s0 (.step (qg _) s1 (.step (qg _) s2 (.step (qg _) s3 (.single q4 s4))))

theorem tafter_get (e len buf n) (r : Reg) (h10 : r ≠ 10) (h11 : r ≠ 11) :
    (tafter e len buf n).get r = e.get r := by
  simp [tafter, Core.wr_get_ne, h10, h11]
theorem tafter_get10 (e len buf n) : (tafter e len buf n).get 10 = buf + n := by
  simp [tafter, Core.wr_get_self, alu_add]
theorem tafter_get11 (e len buf n) : (tafter e len buf n).get 11 = len - n := by
  simp [tafter, Core.wr_get_ne, Core.wr_get_self, alu_sub]
theorem tafter_sameCsr (e len buf n) : (tafter e len buf n).sameCsr e :=
  (Core.sameCsr_wr _ _ _ _).trans ((Core.sameCsr_wr _ _ _ _).trans (Core.sameCsr_goto _ _))

/-- Bytes the two field stores leave alone. -/
theorem tstore_other (M : Word → BitVec 8) (p n x : Word) (hp : p.toNat + 12 ≤ 2 ^ 32)
    (hx : x.toNat < p.toNat ∨ p.toNat + 8 ≤ x.toNat) : tstore M p n x = M x := by
  unfold tstore
  have e4 : (p + 0x4#32).toNat = p.toNat + 4 := add_toNat p 4 (by omega)
  rw [wr_byte_other _ _ _ _ (by omega) (by omega), wr_byte_other _ _ _ _ (by omega) (by omega)]

theorem tstore_consumed (M : Word → BitVec 8) (p n : Word) (hp : p.toNat + 12 ≤ 2 ^ 32) :
    ramRead (tstore M p n) p .w = 0 := by
  unfold tstore
  have e4 : (p + 0x4#32).toNat = p.toNat + 4 := add_toNat p 4 (by omega)
  rw [rd_wr_other _ _ _ _ (by omega) (by omega) (by omega), ramRead_ramWrite_w]

theorem tstore_filled (M : Word → BitVec 8) (p n : Word) :
    ramRead (tstore M p n) (p + 0x4#32) .w = n := by
  unfold tstore; rw [ramRead_ramWrite_w]

/-! ## Arithmetic, kept out of the large contexts below -/

theorem addr_eq (b a : Word) (k : Nat) :
    b + a + (b + BitVec.ofNat 32 k - b) = b + BitVec.ofNat 32 (a.toNat + k) := by
  rw [BitVec.add_comm b (BitVec.ofNat 32 k), BitVec.add_sub_cancel, BitVec.ofNat_add, ofNat_toNat,
    BitVec.add_assoc]

theorem add_toNat' (x y : Word) (h : x.toNat + y.toNat < 2 ^ 32) : (x + y).toNat = x.toNat + y.toNat := by
  rw [BitVec.toNat_add]; omega

theorem sub_frame (f : Word) (h : 0x30 ≤ f.toNat) : (f - BitVec.ofNat 32 0x30).toNat = f.toNat - 0x30 := by
  rw [BitVec.toNat_sub_of_le (BitVec.le_def.mpr (by simpa using h))]; rfl

/-! ## The path with a copy, and the whole of `tail` -/

/-- `tail` with consumed ≠ 0 meets `TailPost`, given memmove's contract, for any frame of at least
    0x50 bytes (tail's own 0x20 and memmove's 0x30). -/
theorem withCopy (hC : CopyContract) (frame : Nat) (hf : 0x50 ≤ frame) (m₀ : Machine)
    (h : TailPre frame m₀) (hc : consumed m₀.ram (m₀.core.get 10) ≠ 0) :
    ∃ k m, QRun B img k m₀ m ∧ TailPost frame m₀ m := by
  obtain ⟨c, R0⟩ := m₀
  obtain ⟨E, hI⟩ := h
  have hpc : c.pc = 0x8001d576 := E.pc
  have hst := stack_nat (c.get 2) frame E.stack
  have hs : 0x80029bc8 + 0x20 ≤ (c.get 2).toNat ∧ (c.get 2).toNat ≤ 0x81000000 := ⟨by omega, hst.2⟩
  have hp := (B_ram (c.get 10) 12).mp E.self
  have hb := (B_ram (c.get 11) (c.get 12).toNat).mp E.buf
  have hlen : (c.get 12).toNat = bufLen := E.len
  have hsep : (c.get 10).toNat + 12 ≤ (c.get 2).toNat - frame ∧
      (c.get 11).toNat + (c.get 12).toNat ≤ (c.get 2).toNat - frame := E.stackSep
  have hI : consumed R0 (c.get 10) ≤ filled R0 (c.get 10) ∧ filled R0 (c.get 10) ≤ (c.get 12).toNat := hI
  have hc : consumed R0 (c.get 10) ≠ 0 := hc
  have hsep2 : (c.get 10).toNat + 12 ≤ (c.get 11).toNat ∨
      (c.get 11).toNat + (c.get 12).toNat ≤ (c.get 10).toNat := E.sep
  have F := fp_FP c E.spAl hs
  have hfp := fp_toNat c (by omega)
  let R := tsave c R0
  let a := ramRead R (c.get 10) .w
  let v := ramRead R (c.get 10 + 0x4#32) .w
  have e4 : (c.get 10 + 0x4#32).toNat = (c.get 10).toNat + 4 := add_toNat _ 4 (by omega)
  have rc : a = ramRead R0 (c.get 10) .w := tsave_rd c R0 hs _ (by omega)
  have rf : v = ramRead R0 (c.get 10 + 0x4#32) .w := tsave_rd c R0 hs _ (by omega)
  have ca : consumed R0 (c.get 10) = a.toNat := by rw [rc]; rfl
  have fv : filled R0 (c.get 10) = v.toNat := by rw [rf]; rfl
  have ha : a ≠ 0 := fun e => hc (by rw [ca, e]; rfl)
  have hle : v.toNat ≤ (c.get 12).toNat := fv ▸ hI.2
  have hcf : a.toNat ≤ v.toNat := ca ▸ fv ▸ hI.1
  let n := v - a
  have hn : n.toNat = v.toNat - a.toNat := sub_toNat _ _ hcf
  have ea : (c.get 11 + a).toNat = (c.get 11).toNat + a.toNat := add_toNat' _ _ (by omega)
  -- to memmove's entry
  have r1 := (prologue c R0 hpc E.quiet E.selfAl E.self E.spAl hs).trans (precall c R0 E.quiet ha hle hcf)
  let K := tcall c R0
  have qK : Quiet K := Quiet.of_sameCsr (tcall_sameCsr c R0) E.quiet
  have hfr : 0x30 ≤ (fp c).toNat := by omega
  have env : CopyEnv ⟨K, R⟩ := by
    refine ⟨rfl, qK, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · show (K.get 12).toNat ≤ bufLen; rw [tcall_get12, ← hlen]; show n.toNat ≤ _; omega
    · show B.inRam (K.get 10) (K.get 12).toNat = true
      rw [tcall_get10, tcall_get12, B_ram]; show _ ∧ _ + n.toNat ≤ _; omega
    · show B.inRam (K.get 11) (K.get 12).toNat = true
      rw [tcall_get11, tcall_get12, B_ram]
      show 0x80029bc8 ≤ (c.get 11 + a).toNat ∧ (c.get 11 + a).toNat + n.toNat ≤ 0x81000000
      rw [ea]; omega
    · show B.inRam (K.get 2 - BitVec.ofNat 32 memmoveFrame) memmoveFrame = true
      rw [tcall_get2, B_ram, show memmoveFrame = 0x30 from rfl, sub_frame _ hfr]; omega
    · show (K.get 10).toNat + (K.get 12).toNat ≤ (K.get 2).toNat - memmoveFrame
      rw [tcall_get10, tcall_get12, tcall_get2, show memmoveFrame = 0x30 from rfl]
      show _ + n.toNat ≤ _; omega
    · show (K.get 11).toNat + (K.get 12).toNat ≤ (K.get 2).toNat - memmoveFrame
      rw [tcall_get11, tcall_get12, tcall_get2]
      show (c.get 11 + a).toNat + n.toNat ≤ (fp c).toNat - 0x30
      rw [ea]; omega
    · show (K.get 1).getLsbD 0 = false; rw [tcall_get1]; decide
    · show (K.get 2).toNat % 4 = 0; rw [tcall_get2]; exact F.al
  obtain ⟨kc, ⟨e, M⟩, rc2, P⟩ := hC _ env
  have Pregs : ∀ r : Reg, r.val ∉ [5, 6, 7, 11, 12, 13, 14, 15, 16, 17, 28, 29, 30, 31] → e.get r = K.get r :=
    P.regs
  have Pram : ∀ x, ¬ ((fp c).toNat - 0x30 ≤ x.toNat ∧ x.toNat < (fp c).toNat) →
      M x = Memmove.moved R (c.get 11) (c.get 11 + a) n.toNat x := by
    intro x hx
    have := P.ram x (show ¬ (((tcall c R0).get 2).toNat - memmoveFrame ≤ x.toNat ∧
      x.toNat < ((tcall c R0).get 2).toNat) by rw [tcall_get2]; exact hx)
    refine this.trans ?_
    show Memmove.moved R ((tcall c R0).get 10) ((tcall c R0).get 11) ((tcall c R0).get 12).toNat x = _
    rw [tcall_get10, tcall_get11, tcall_get12]
  have g8 : e.get 8 = c.get 10 := (Pregs 8 (by decide)).trans (tcall_get8 c R0)
  have g9 : e.get 9 = n := (Pregs 9 (by decide)).trans (tcall_get9 c R0)
  have g18 : e.get 18 = c.get 12 := (Pregs 18 (by decide)).trans (tcall_get18 c R0)
  have g19 : e.get 19 = c.get 11 := (Pregs 19 (by decide)).trans (tcall_get19 c R0)
  have g2 : e.get 2 = fp c := (Pregs 2 (by decide)).trans (tcall_get2 c R0)
  have epc : e.pc = 0x8001d5a8 := P.pc.trans (tcall_get1 c R0)
  have qe : Quiet e := Quiet.of_sameCsr P.csr qK
  have r2 := postcall e M (c.get 10) (c.get 12) (c.get 11) n epc qe g8 g9 g18 g19 E.selfAl E.self
    (by omega)
  -- RAM after the call: outside the deframer, memmove's frame and the destination, as on entry
  have keep : ∀ x : Word, (x.toNat < (c.get 10).toNat ∨ (c.get 10).toNat + 8 ≤ x.toNat) →
      ¬ ((fp c).toNat - 0x30 ≤ x.toNat ∧ x.toNat < (fp c).toNat) →
      ¬ ((c.get 11).toNat ≤ x.toNat ∧ x.toNat < (c.get 11).toNat + n.toNat) → (tstore M (c.get 10) n) x = R x := by
    intro x h1 h2 h3
    rw [tstore_other M (c.get 10) n x (by omega) h1, Pram x h2, Memmove.moved, if_neg h3]
  have slot : ∀ k : Nat, k = 0x1c ∨ k = 0x18 ∨ k = 0x14 ∨ k = 0x10 ∨ k = 0xc →
      ramRead (tstore M (c.get 10) n) (fp c + BitVec.ofNat 32 k) .w = ramRead R (fp c + BitVec.ofNat 32 k) .w := by
    intro k hk
    have hk' : k + 4 ≤ 0x20 := by rcases hk with rfl | rfl | rfl | rfl | rfl <;> decide
    have ek : (fp c + BitVec.ofNat 32 k).toNat = (fp c).toNat + k := add_toNat _ k (by omega)
    apply rd_congr _ (by omega)
    intro x h1 h2
    exact keep x (.inr (by omega)) (by omega) (by omega)
  have hra : (ramRead (tstore M (c.get 10) n) (fp c + 0x1c#32) .w).getLsbD 0 = false := by
    rw [slot 0x1c (by decide), tsave_1c c R0 hs]; exact E.ra
  have r3 := epilogue (tafter e (c.get 12) (c.get 11) n) (tstore M (c.get 10) n) (fp c) rfl
    (Quiet.of_sameCsr (tafter_sameCsr _ _ _ _) qe) (by rw [tafter_get _ _ _ _ 2 (by decide) (by decide)]; exact g2)
    F hra
  refine ⟨_, _, ((r1.trans rc2).trans r2).trans r3, ?_⟩
  -- the deframer fields after the stores
  have hcons : consumed (tstore M (c.get 10) n) (c.get 10) = 0 := by
    show (ramRead (tstore M (c.get 10) n) (c.get 10) .w).toNat = 0; rw [tstore_consumed M _ n (by omega)]; rfl
  have hfill : filled (tstore M (c.get 10) n) (c.get 10) = n.toNat := by
    show (ramRead (tstore M (c.get 10) n) (c.get 10 + 4) .w).toNat = n.toNat
    exact congrArg BitVec.toNat (tstore_filled M (c.get 10) n)
  let T := tafter e (c.get 12) (c.get 11) n
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show (tepi T (tstore M (c.get 10) n) (fp c)).pc = c.get 1
    exact (slot 0x1c (by decide)).trans (tsave_1c c R0 hs)
  · exact (tepi_sameCsr _ _ _).trans ((tafter_sameCsr _ _ _ _).trans (P.csr.trans (tcall_sameCsr c R0)))
  · exact (tepi_get2 _ _ _).trans (fp_add c)
  · intro r hr
    show (tepi T (tstore M (c.get 10) n) (fp c)).get r = c.get r
    by_cases h1 : r = 1
    · subst h1; exact (tepi_get1 _ _ _).trans ((slot 0x1c (by decide)).trans (tsave_1c c R0 hs))
    by_cases h2 : r = 2
    · subst h2; exact (tepi_get2 _ _ _).trans (fp_add c)
    by_cases h8 : r = 8
    · subst h8; exact (tepi_get8 _ _ _).trans ((slot 0x18 (by decide)).trans (tsave_18 c R0 hs))
    by_cases h9 : r = 9
    · subst h9; exact (tepi_get9 _ _ _).trans ((slot 0x14 (by decide)).trans (tsave_14 c R0 hs))
    by_cases h18 : r = 18
    · subst h18; exact (tepi_get18 _ _ _).trans ((slot 0x10 (by decide)).trans (tsave_10 c R0 hs))
    by_cases h19 : r = 19
    · subst h19; exact (tepi_get19 _ _ _).trans ((slot 0xc (by decide)).trans (tsave_0c c R0))
    have hcs : r.val ∉ [5, 6, 7, 11, 12, 13, 14, 15, 16, 17, 28, 29, 30, 31] := fun hm =>
      hr (by simp only [callerSaved, List.mem_cons, List.not_mem_nil, or_false] at hm ⊢; omega)
    have h10 : r ≠ 10 := fun e => hr (by subst e; decide)
    have h11 : r ≠ 11 := fun e => hr (by subst e; decide)
    have h12 : r ≠ 12 := fun e => hr (by subst e; decide)
    rw [tepi_get _ _ _ r h1 h2 h8 h9 h18 h19, tafter_get _ _ _ _ r h10 h11, Pregs r hcs,
      tcall_get c R0 r h1 h2 h8 h9 h10 h11 h12 h18 h19]
  · exact hcons
  · show filled (tstore M (c.get 10) n) (c.get 10) = filled R0 (c.get 10) - consumed R0 (c.get 10)
    rw [hfill, hn, ca, fv]
  · show (tepi T (tstore M (c.get 10) n) (fp c)).get 10 = c.get 11 + BitVec.ofNat 32 (filled (tstore M (c.get 10) n) (c.get 10)) ∧
      ((tepi T (tstore M (c.get 10) n) (fp c)).get 11).toNat = (c.get 12).toNat - filled (tstore M (c.get 10) n) (c.get 10)
    rw [tepi_get _ _ _ 10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      tepi_get _ _ _ 11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      tafter_get10, tafter_get11, hfill, ofNat_toNat]
    exact ⟨rfl, sub_toNat _ _ (by omega)⟩
  · intro k hk
    show (tstore M (c.get 10) n) (c.get 11 + BitVec.ofNat 32 k) = R0 (c.get 11 + BitVec.ofNat 32 (consumed R0 (c.get 10) + k))
    have hk : k < n.toNat := by rw [← hfill]; exact hk
    have ek : (c.get 11 + BitVec.ofNat 32 k).toNat = (c.get 11).toNat + k := add_toNat _ k (by omega)
    have hin : (c.get 11).toNat ≤ (c.get 11 + BitVec.ofNat 32 k).toNat ∧
        (c.get 11 + BitVec.ofNat 32 k).toNat < (c.get 11).toNat + n.toNat := by omega
    rw [tstore_other M (c.get 10) n (c.get 11 + BitVec.ofNat 32 k) (by omega) (by omega),
      Pram (c.get 11 + BitVec.ofNat 32 k) (by omega), Memmove.moved, if_pos hin, addr_eq, ca]
    have ek' : (c.get 11 + BitVec.ofNat 32 (a.toNat + k)).toNat = (c.get 11).toNat + (a.toNat + k) :=
      add_toNat _ _ (by omega)
    have hx : (c.get 11 + BitVec.ofNat 32 (a.toNat + k)).toNat < (c.get 2).toNat - 0x20 := by
      rw [ek']; omega
    exact tsave_other c R0 hs _ (.inl hx)
  · show consumed (tstore M (c.get 10) n) (c.get 10) ≤ filled (tstore M (c.get 10) n) (c.get 10) ∧ filled (tstore M (c.get 10) n) (c.get 10) ≤ (c.get 12).toNat
    rw [hcons, hfill]; omega
  · intro x hx
    show (tstore M (c.get 10) n) x = R0 x
    have h1 : ¬ ((c.get 10).toNat ≤ x.toNat ∧ x.toNat < (c.get 10).toNat + 12) := hx.1
    have h2 : ¬ ((c.get 11).toNat ≤ x.toNat ∧ x.toNat < (c.get 11).toNat + (c.get 12).toNat) := hx.2.1
    have h3 : ¬ ((c.get 2).toNat - frame ≤ x.toNat ∧ x.toNat < (c.get 2).toNat) := hx.2.2
    rw [keep x (by omega) (by omega) (by omega)]
    exact tsave_other c R0 hs x (by omega)
  · show ((tstore M (c.get 10) n) (c.get 10 + 8)).toNat = (R0 (c.get 10 + 8)).toNat
    have e8 : (c.get 10 + 8).toNat = (c.get 10).toNat + 8 := add_toNat _ 8 (by omega)
    rw [keep (c.get 10 + 8) (by omega) (by omega) (by omega)]
    exact congrArg BitVec.toNat (tsave_other c R0 hs (c.get 10 + 8) (.inl (by omega)))

/-- `tail`'s contract with the 80-byte frame, given memmove's contract (the dependency is the
    hypothesis `CopyContract`; it is not proved here). -/
theorem tail_from_copy : TailFromCopy := fun hC m₀ h => by
  by_cases hc : consumed m₀.ram (m₀.core.get 10) = 0
  · exact nocopy tailStack (by decide) m₀ h hc
  · exact withCopy hC tailStack (by decide) m₀ h hc

end E5R.Rmk.Deframer.Tail
