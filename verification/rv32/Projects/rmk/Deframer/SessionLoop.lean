/-
  The Rynk session loop, closing step: the unpark call site (0x80003fd8) back to the loop head
  (0x80003e1a), on the pinned RMK image.

  Original e5r code, Apache-2.0.

  PROVED here, CONDITIONAL ON `CopyContract` (memmove; a hypothesis, not proved):
  `unpark_step`: from 0x80003fd8 with the session bases, a stack as in `SessPre`, a parked count
  (the word at s6+0x2db) of at most 488 and discarding ≤ 1, a quiet run through `unpark_pending`
  reaches the loop head with `SessPre` again (consumed = 0, filled = parked), at the same sp,
  writing RAM only in the deframer, the buffer and 0x40 stack bytes.

  The session path from `recv_step`'s Some point 0x80003e70 to 0x80003fd8 (`RynkService::dispatch`,
  `encode_frame`, the UART response writes, yields to the executor) is NOT proved; nor is the None
  path from 0x80003f7c through the UART read future back to the loop head. `SessionSafe` is not
  proved.
-/
import Projects.rmk.Deframer.Session
import Projects.rmk.Deframer.UnparkSiteSegs

set_option maxRecDepth 100000

namespace E5R.Rmk.Deframer.Session
open E5R E5R.Rmk.Deframer.Tail

/-- A method call from the session: the deframer and buffer at their fixed addresses, len = 488,
    the call made at the session's sp. -/
theorem callEnv_of (sp : Word) (hsp : 0x8002a798 + 0x70 ≤ sp.toNat ∧ sp.toNat ≤ 0x81000000)
    (hspa : sp.toNat % 4 = 0) (K : Core) (M : Word → BitVec 8) (pc frame : Nat) (hf : frame ≤ 0x70)
    (a : K.pc = BitVec.ofNat 32 pc) (b : Quiet K) (d10 : K.get 10 = dfr) (d11 : K.get 11 = bufA)
    (d12 : K.get 12 = 0x1e8#32) (d2 : K.get 2 = sp) (dra : (K.get 1).getLsbD 0 = false) :
    CallEnv pc frame ⟨K, M⟩ := by
  have hsb : (sp - BitVec.ofNat 32 frame).toNat = sp.toNat - frame := by bv_omega
  refine ⟨a, b, ?_, ?_, ?_, ?_, ?_, ?_, dra, ?_, ?_⟩
  · show B.inRam (K.get 10) 12 = true; rw [d10]; decide
  · show B.inRam (K.get 11) (K.get 12).toNat = true; rw [d11, d12]; decide
  · show (K.get 12).toNat = bufLen; rw [d12]; rfl
  · show (K.get 10).toNat + 12 ≤ (K.get 11).toNat ∨ (K.get 11).toNat + (K.get 12).toNat ≤ (K.get 10).toNat
    rw [d10, d11, d12]; decide
  · show B.inRam (K.get 2 - BitVec.ofNat 32 frame) frame = true; rw [d2, B_ram, hsb]; omega
  · show (K.get 10).toNat + 12 ≤ (K.get 2).toNat - frame ∧ (K.get 11).toNat + (K.get 12).toNat ≤ (K.get 2).toNat - frame
    rw [d10, d11, d12, d2]
    exact ⟨by rw [show dfr.toNat = 0x8002a78c from rfl]; omega, by
      rw [show bufA.toNat = 0x8002a590 from rfl, show (0x1e8#32 : Word).toNat = 0x1e8 from rfl]; omega⟩
  · show (K.get 10).toNat % 4 = 0; rw [d10]; decide
  · show (K.get 2).toNat % 4 = 0; rw [d2]; exact hspa

/-- The unpark call site. -/
structure UnparkAt (m : Machine) : Prop where
  pc : m.core.pc = 0x80003fd8
  quiet : Quiet m.core
  s6 : m.core.get 22 = s6v
  s7 : m.core.get 23 = s7v
  spAl : (m.core.get 2).toNat % 4 = 0
  sp : 0x8002a798 + 0x70 ≤ (m.core.get 2).toNat ∧ (m.core.get 2).toNat ≤ 0x81000000
  parked : (ramRead m.ram 0x8002a798 .w).toNat ≤ bufLen
  disc : discarding m.ram dfr ≤ 1

theorem unpark_step (hC : CopyContract) (m₀ : Machine) (h : UnparkAt m₀) :
    ∃ k m, QRun B img k m₀ m ∧ SessPre m ∧ m.core.get 2 = m₀.core.get 2 ∧
      filled m.ram dfr = (ramRead m₀.ram 0x8002a798 .w).toNat ∧
      ∀ x, ¬ ((dfr.toNat ≤ x.toNat ∧ x.toNat < dfr.toNat + 12) ∨
              (bufA.toNat ≤ x.toNat ∧ x.toNat < bufA.toNat + bufLen) ∨
              ((m₀.core.get 2).toNat - 0x40 ≤ x.toNat ∧ x.toNat < (m₀.core.get 2).toNat)) →
        m.ram x = m₀.ram x := by
  obtain ⟨c, R0⟩ := m₀
  have h22 : c.get 22 = s6v := h.s6
  have h23 : c.get 23 = s7v := h.s7
  have hsp : 0x8002a798 + 0x70 ≤ (c.get 2).toNat ∧ (c.get 2).toNat ≤ 0x81000000 := h.sp
  have hspa : (c.get 2).toNat % 4 = 0 := h.spAl
  have hpk : (ramRead R0 0x8002a798 .w).toNat ≤ bufLen := h.parked
  have hdc : (R0 (dfr + 8)).toNat ≤ 1 := h.disc
  have r1 := sunpk c R0 h.pc h.quiet (by rw [h22]; decide) (by rw [h22]; decide)
  let K := sunpkCore c R0
  have csK : K.sameCsr c := by unfold K sunpkCore; (repeat (first | exact Core.sameCsr_wr _ _ _ _ | exact Core.sameCsr_goto _ _ | refine (Core.sameCsr_wr _ _ _ _).trans ?_ | refine (Core.sameCsr_goto _ _).trans ?_))
  have qK : Quiet K := Quiet.of_sameCsr csK h.quiet
  have K10 : K.get 10 = dfr := by simp [K, sunpkCore, Core.wr_get_ne, Core.wr_get_self, alu_add, h23]; rfl
  have K11 : K.get 11 = bufA := by simp [K, sunpkCore, Core.wr_get_ne, Core.wr_get_self, alu_add, h23]; rfl
  have K12 : K.get 12 = 0x1e8#32 := by simp [K, sunpkCore, Core.wr_get_ne, Core.wr_get_self, alu_add]
  have K13 : K.get 13 = ramRead R0 0x8002a798 .w := by
    simp [K, sunpkCore, Core.wr_get_ne, Core.wr_get_self, h22]; rfl
  have K1 : K.get 1 = 0x80003ff0 := by simp [K, sunpkCore, Core.wr_get_self]
  have K2 : K.get 2 = c.get 2 := by simp [K, sunpkCore, Core.wr_get_ne]
  have K22 : K.get 22 = s6v := by simp [K, sunpkCore, Core.wr_get_ne, h22]
  have K23 : K.get 23 = s7v := by simp [K, sunpkCore, Core.wr_get_ne, h23]
  have E : CallEnv unparkPc parkStack ⟨K, R0⟩ :=
    callEnv_of (c.get 2) hsp hspa K R0 unparkPc parkStack (by decide) rfl qK K10 K11 K12 K2 (by rw [K1]; decide)
  obtain ⟨ku, ⟨e, M⟩, ru, UP⟩ := Unpark.unpark_from_copy hC ⟨K, R0⟩ E (by
    show (K.get 13).toNat ≤ bufLen; rw [K13]; exact hpk)
  have UPs : ∀ r : Reg, r.val ∉ callerSaved → e.get r = K.get r := UP.saved
  have qe : Quiet e := Quiet.of_sameCsr UP.csr qK
  have r2 := sback e M (UP.pc.trans K1) qe
  refine ⟨_, _, (r1.trans ru).trans r2, ?_, ?_, ?_, ?_⟩
  · have hc := UP.hconsumed
    have hf := UP.hfilled
    have hd := UP.hdisc
    rw [show (⟨K, R0⟩ : Machine).core.get 10 = dfr from K10] at hc hf hd
    rw [show (⟨K, R0⟩ : Machine).core.get 13 = ramRead R0 0x8002a798 .w from K13] at hf
    refine ⟨rfl, Quiet.of_sameCsr (Core.sameCsr_goto _ _) qe, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · show e.get 22 = s6v; exact (UPs 22 (by decide)).trans K22
    · show e.get 23 = s7v; exact (UPs 23 (by decide)).trans K23
    · show (e.get 2).toNat % 4 = 0; rw [UP.sp, K2]; exact hspa
    · show 0x8002a798 + 0x70 ≤ (e.get 2).toNat ∧ (e.get 2).toNat ≤ 0x81000000; rw [UP.sp, K2]; exact hsp
    · show consumed M dfr ≤ filled M dfr ∧ filled M dfr ≤ bufLen; rw [hc, hf]; omega
    · show (M (dfr + 8)).toNat ≤ 1; rw [hd]; exact hdc
  · show e.get 2 = c.get 2; rw [UP.sp, K2]
  · have hf := UP.hfilled
    rw [show (⟨K, R0⟩ : Machine).core.get 10 = dfr from K10,
      show (⟨K, R0⟩ : Machine).core.get 13 = ramRead R0 0x8002a798 .w from K13] at hf
    exact hf
  · intro x hx
    show M x = R0 x
    refine UP.ram x ⟨?_, ?_, ?_⟩
    · show ¬ ((K.get 10).toNat ≤ x.toNat ∧ x.toNat < (K.get 10).toNat + 12); rw [K10]; exact fun h' => hx (.inl h')
    · show ¬ ((K.get 11).toNat ≤ x.toNat ∧ x.toNat < (K.get 11).toNat + (K.get 12).toNat)
      rw [K11, K12]; exact fun h' => hx (.inr (.inl h'))
    · show ¬ ((K.get 2).toNat - parkStack ≤ x.toNat ∧ x.toNat < (K.get 2).toNat)
      rw [K2]; exact fun h' => hx (.inr (.inr h'))

end E5R.Rmk.Deframer.Session
