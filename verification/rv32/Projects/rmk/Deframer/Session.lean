/-
  The Rynk session's receive step (main task poll, loop head 0x80003e1a) on the pinned RMK image,
  composed from the deframer contracts at their real call sites.

  Original e5r code, Apache-2.0.

  PROVED here, CONDITIONAL ON `CopyContract` (memmove; a hypothesis, not proved):
  `recv_step`: from every machine at the session loop head with the deframer invariant
  (`SessPre`: the session's s6/s7 bases, a stack below which the deframer and buffer lie), a quiet
  run (so: no panic on the way, whatever bytes the buffer holds) reaches
  * `Some(k)`: 0x80003e70, back from `RynkMessage::from_decoded` (0x8001c3c6, whose length check,
    len = 488 - parked ≥ 3, is not taken: next's `k < consumed` gives parked ≤ 484), with the
    message at 0x8002a580 = (buffer, 488 - parked, header, k), 2 < k ≤ 488, the deframer emptied
    and its pending bytes parked (bounds check 0x80003e5a not taken); or
  * `None`: 0x80003f7c after `tail`, with the invariant again and consumed = 0;
  writing RAM only in the deframer, the buffer, 0x70 stack bytes, the session word s6+0x2db and the
  16-byte message.

  NOT proved: what follows either point (the message dispatch from 0x80003e70, the response, unpark,
  the UART read future and the executor between polls), so this is a step toward `SessionSafe`, not
  `SessionSafe`.
-/
import Projects.rmk.Deframer.CobsDischarge
import Projects.rmk.Deframer.TailCopy
import Projects.rmk.Deframer.Unpark
import Projects.rmk.Deframer.SessionSegs
import Projects.rmk.Deframer.FromDecodedSeg

set_option maxRecDepth 100000

namespace E5R.Rmk.Deframer.Session
open E5R E5R.Rmk.SessionFetch E5R.Rmk.Deframer.Tail

/-- The session bases in s6/s7 (task future statics) and where the deframer and buffer are. -/
def s6v : Word := 0x8002a4bd
def s7v : Word := 0x8002a3cf
def dfr : Word := 0x8002a78c
def bufA : Word := 0x8002a590
/-- The `RynkMessage` that `from_decoded` fills (s7 + 0x1b1), just below the buffer. -/
def msgA : Word := 0x8002a580

/-- A word read is unaffected by a store of any width that does not overlap it. -/
theorem rd_wr_far (ram : Word → BitVec 8) (a v b : Word) (wd : Width) (ha : a.toNat + 4 ≤ 2 ^ 32)
    (hb : b.toNat + 4 ≤ 2 ^ 32) (h : b.toNat + 4 ≤ a.toNat ∨ a.toNat + 4 ≤ b.toNat) :
    ramRead (ramWrite ram a v wd) b .w = ramRead ram b .w := by
  cases wd with
  | w => exact rd_wr_other ram a v b ha hb h
  | b =>
    apply rd_congr b hb; intro x h1 h2
    exact ramPut_ne _ (fun e => by subst e; omega)
  | h =>
    apply rd_congr b hb; intro x h1 h2
    have e1 : (a + 1).toNat = a.toNat + 1 := by bv_omega
    simp only [ramWrite]
    rw [ramPut_ne _ (fun e => by subst e; omega), ramPut_ne _ (fun e => by subst e; omega)]

structure SessPre (m : Machine) : Prop where
  pc : m.core.pc = 0x80003e1a
  quiet : Quiet m.core
  s6 : m.core.get 22 = s6v
  s7 : m.core.get 23 = s7v
  spAl : (m.core.get 2).toNat % 4 = 0
  sp : 0x8002a798 + 0x70 ≤ (m.core.get 2).toNat ∧ (m.core.get 2).toNat ≤ 0x81000000
  inv : Inv m.ram dfr bufLen
  disc : discarding m.ram dfr ≤ 1

/-- RAM the receive step may write. -/
def RecvW (sp : Word) (x : Word) : Prop :=
  (dfr.toNat ≤ x.toNat ∧ x.toNat < dfr.toNat + 12) ∨ (bufA.toNat ≤ x.toNat ∧ x.toNat < bufA.toNat + bufLen) ∨
  (sp.toNat - 0x70 ≤ x.toNat ∧ x.toNat < sp.toNat) ∨ (0x8002a798 ≤ x.toNat ∧ x.toNat < 0x8002a798 + 4) ∨
  (msgA.toNat ≤ x.toNat ∧ x.toNat < msgA.toNat + 16)

structure RecvOut (m₀ m : Machine) : Prop where
  quiet : Quiet m.core
  s6 : m.core.get 22 = s6v
  s7 : m.core.get 23 = s7v
  sp : m.core.get 2 = m₀.core.get 2
  ram : ∀ x, ¬ RecvW (m₀.core.get 2) x → m.ram x = m₀.ram x
  out : (m.core.pc = 0x80003e70 ∧ ramRead m.ram msgA .w = bufA ∧
          3 ≤ (ramRead m.ram (msgA + 4) .w).toNat ∧ (ramRead m.ram (msgA + 4) .w).toNat ≤ bufLen ∧
          2 < (ramRead m.ram (msgA + 0xc) .w).toNat ∧ (ramRead m.ram (msgA + 0xc) .w).toNat ≤ bufLen ∧
          consumed m.ram dfr = 0 ∧ filled m.ram dfr = 0) ∨
        (m.core.pc = 0x80003f7c ∧ Inv m.ram dfr bufLen ∧ consumed m.ram dfr = 0 ∧
          m.core.get 18 = bufA + BitVec.ofNat 32 (filled m.ram dfr) ∧
          (m.core.get 20).toNat = bufLen - filled m.ram dfr ∧ discarding m.ram dfr ≤ 1 ∧
          (m.core.get 25).toNat = discarding m.ram dfr ∧ (m.core.get 21).toNat ≤ (m.core.get 24).toNat ∧
          (m.core.get 24).toNat - (m.core.get 21).toNat = filled m.ram dfr ∧
          m.core.get 19 = ramRead m₀.ram 0x8002a784 .w)

theorem recv_step (hC : CopyContract) (m₀ : Machine) (h : SessPre m₀) :
    ∃ k m, QRun B img k m₀ m ∧ RecvOut m₀ m := by
  obtain ⟨c, R0⟩ := m₀
  have h22 : c.get 22 = s6v := h.s6
  have h23 : c.get 23 = s7v := h.s7
  have hsp : 0x8002a798 + 0x70 ≤ (c.get 2).toNat ∧ (c.get 2).toNat ≤ 0x81000000 := h.sp
  have hspa : (c.get 2).toNat % 4 = 0 := h.spAl
  -- the call of next
  have r1 := scall c R0 h.pc h.quiet
  let K1 := scallCore c R0
  have csK1 : K1.sameCsr c := by unfold K1 scallCore; (repeat (first | exact Core.sameCsr_wr _ _ _ _ | exact Core.sameCsr_goto _ _ | refine (Core.sameCsr_wr _ _ _ _).trans ?_ | refine (Core.sameCsr_goto _ _).trans ?_))
  have K1_10 : K1.get 10 = dfr := by simp [K1, scallCore, Core.wr_get_ne, Core.wr_get_self, alu_add, h22]; rfl
  have K1_11 : K1.get 11 = bufA := by simp [K1, scallCore, Core.wr_get_ne, Core.wr_get_self, alu_add, h23]; rfl
  have K1_12 : K1.get 12 = 0x1e8#32 := by simp [K1, scallCore, Core.wr_get_ne, Core.wr_get_self, alu_add]
  have K1_1 : K1.get 1 = 0x80003e36 := by simp [K1, scallCore, Core.wr_get_self]
  have K1_2 : K1.get 2 = c.get 2 := by simp [K1, scallCore, Core.wr_get_ne]
  have K1_9 : K1.get 9 = dfr := by simp [K1, scallCore, Core.wr_get_ne, Core.wr_get_self, alu_add, h22]; rfl
  have K1_8 : K1.get 8 = bufA := by simp [K1, scallCore, Core.wr_get_ne, Core.wr_get_self, alu_add, h23]; rfl
  have K1_19 : K1.get 19 = 0x1e8#32 := by simp [K1, scallCore, Core.wr_get_ne, Core.wr_get_self, alu_add]
  have K1_22 : K1.get 22 = s6v := by simp [K1, scallCore, Core.wr_get_ne, h22]
  have K1_23 : K1.get 23 = s7v := by simp [K1, scallCore, Core.wr_get_ne, h23]
  have qK1 : Quiet K1 := Quiet.of_sameCsr csK1 h.quiet
  -- a call environment at this session's sp, for each method's frame
  have env : ∀ (K : Core) (pc : Nat) (frame : Nat), frame ≤ 0x70 → K.pc = BitVec.ofNat 32 pc → Quiet K →
      K.get 10 = dfr → K.get 11 = bufA → K.get 12 = 0x1e8#32 → K.get 2 = c.get 2 → (K.get 1).getLsbD 0 = false →
      CallEnv pc frame ⟨K, R0⟩ := by
    intro K pc frame hf a b d10 d11 d12 d2 dra
    have hsb : (c.get 2 - BitVec.ofNat 32 frame).toNat = (c.get 2).toNat - frame := by bv_omega
    refine ⟨a, b, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
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
    · exact dra
    · show (K.get 10).toNat % 4 = 0; rw [d10]; decide
    · show (K.get 2).toNat % 4 = 0; rw [d2]; exact hspa
  -- the env only depends on the core: the same lemma works for any RAM
  have envM : ∀ (K : Core) (M : Word → BitVec 8) (pc : Nat) (frame : Nat), frame ≤ 0x70 →
      K.pc = BitVec.ofNat 32 pc → Quiet K → K.get 10 = dfr → K.get 11 = bufA → K.get 12 = 0x1e8#32 →
      K.get 2 = c.get 2 → (K.get 1).getLsbD 0 = false → CallEnv pc frame ⟨K, M⟩ := by
    intro K M pc frame hf a b d10 d11 d12 d2 dra
    have := env K pc frame hf a b d10 d11 d12 d2 dra
    exact ⟨this.pc, this.quiet, this.self, this.buf, this.len, this.sep, this.stack, this.stackSep, this.ra,
      this.selfAl, this.spAl⟩
  have E1 : CallEnv nextPc nextStack ⟨K1, R0⟩ :=
    env K1 nextPc nextStack (by decide) rfl qK1 K1_10 K1_11 K1_12 K1_2 (by rw [K1_1]; decide)
  have hI : Inv R0 dfr bufLen := h.inv
  have hD : discarding R0 dfr ≤ 1 := h.disc
  obtain ⟨kn, ⟨e1, M1⟩, rn, NP⟩ := next_from_copy hC ⟨K1, R0⟩ E1 (by rw [show (⟨K1, R0⟩ : Machine).core.get 10 = dfr from K1_10,
      show ((⟨K1, R0⟩ : Machine).core.get 12).toNat = bufLen from by rw [show (⟨K1, R0⟩ : Machine).core.get 12 = 0x1e8#32 from K1_12]; rfl]; exact hI)
    (by rw [show (⟨K1, R0⟩ : Machine).core.get 10 = dfr from K1_10]; exact hD)
  -- after next
  have NPs : ∀ r : Reg, r.val ∉ callerSaved → e1.get r = K1.get r := NP.saved
  have e1pc : e1.pc = 0x80003e36 := NP.pc.trans K1_1
  have qe1 : Quiet e1 := Quiet.of_sameCsr NP.csr qK1
  have e1_9 : e1.get 9 = dfr := (NPs 9 (by decide)).trans K1_9
  have e1_8 : e1.get 8 = bufA := (NPs 8 (by decide)).trans K1_8
  have e1_19 : e1.get 19 = 0x1e8#32 := (NPs 19 (by decide)).trans K1_19
  have e1_22 : e1.get 22 = s6v := (NPs 22 (by decide)).trans K1_22
  have e1_23 : e1.get 23 = s7v := (NPs 23 (by decide)).trans K1_23
  have e1_2 : e1.get 2 = c.get 2 := NP.sp.trans K1_2
  have tag : (e1.get 10).toNat ≤ 1 := NP.tag
  have inv1 : Inv M1 dfr bufLen := by
    have := NP.inv
    rw [show (⟨K1, R0⟩ : Machine).core.get 10 = dfr from K1_10,
      show ((⟨K1, R0⟩ : Machine).core.get 12).toNat = bufLen from by
        rw [show (⟨K1, R0⟩ : Machine).core.get 12 = 0x1e8#32 from K1_12]; rfl] at this
    exact this
  have ram1 : ∀ x, ¬ RecvW (c.get 2) x → M1 x = R0 x := by
    intro x hx
    refine NP.ram x ⟨?_, ?_, ?_⟩
    · show ¬ ((K1.get 10).toNat ≤ x.toNat ∧ x.toNat < (K1.get 10).toNat + 12); rw [K1_10]; exact fun h' => hx (.inl h')
    · show ¬ ((K1.get 11).toNat ≤ x.toNat ∧ x.toNat < (K1.get 11).toNat + (K1.get 12).toNat)
      rw [K1_11, K1_12]; exact fun h' => hx (.inr (.inl h'))
    · show ¬ ((K1.get 2).toNat - nextStack ≤ x.toNat ∧ x.toNat < (K1.get 2).toNat)
      rw [K1_2]; exact fun h' => hx (.inr (.inr (.inl h')))
  have hraeven : ∀ v : Word, v.toNat % 2 = 0 → v.getLsbD 0 = false := fun v hv => lsb_lit v hv
  by_cases hz : (e1.get 10).toNat = 0
  · -- None: tail
    have a0z : e1.get 10 = 0 := BitVec.eq_of_toNat_eq hz
    have r2 := snone e1 M1 e1pc qe1 (by rw [a0z]; rfl)
      (by rw [e1_22]; decide) (by rw [e1_22]; decide) (by rw [e1_22]; decide) (by rw [e1_22]; decide)
      (by rw [e1_22]; decide) (by rw [e1_22]; decide) (by rw [e1_22]; decide) (by rw [e1_22]; decide)
    let K2 := snoneCore e1 M1
    have csK2 : K2.sameCsr e1 := by unfold K2 snoneCore; (repeat (first | exact Core.sameCsr_wr _ _ _ _ | exact Core.sameCsr_goto _ _ | refine (Core.sameCsr_wr _ _ _ _).trans ?_ | refine (Core.sameCsr_goto _ _).trans ?_))
    have qK2 : Quiet K2 := Quiet.of_sameCsr csK2 qe1
    have K2_10 : K2.get 10 = dfr := by simp [K2, snoneCore, Core.wr_get_ne, Core.wr_get_self, alu_add, e1_9]
    have K2_11 : K2.get 11 = bufA := by simp [K2, snoneCore, Core.wr_get_ne, Core.wr_get_self, alu_add, e1_8]
    have K2_12 : K2.get 12 = 0x1e8#32 := by simp [K2, snoneCore, Core.wr_get_ne, Core.wr_get_self, alu_add]
    have K2_1 : K2.get 1 = 0x80003f78 := by simp [K2, snoneCore, Core.wr_get_self]
    have K2_2 : K2.get 2 = c.get 2 := by simp [K2, snoneCore, Core.wr_get_ne, e1_2]
    have K2_22 : K2.get 22 = s6v := by simp [K2, snoneCore, Core.wr_get_ne, e1_22]
    have K2_23 : K2.get 23 = s7v := by simp [K2, snoneCore, Core.wr_get_ne, e1_23]
    have E2 : CallEnv tailPc tailStack ⟨K2, M1⟩ :=
      envM K2 M1 tailPc tailStack (by decide) rfl qK2 K2_10 K2_11 K2_12 K2_2 (by rw [K2_1]; decide)
    obtain ⟨kt, ⟨e2, M2⟩, rt, TP⟩ := tail_from_copy hC ⟨K2, M1⟩ ⟨E2, by
      show Inv M1 (K2.get 10) (K2.get 12).toNat; rw [K2_10, K2_12]; exact inv1⟩
    have TPs : ∀ r : Reg, r.val ∉ callerSaved → e2.get r = K2.get r := TP.saved
    have r3 := stail e2 M2 (TP.pc.trans K2_1) (Quiet.of_sameCsr TP.csr qK2)
    refine ⟨_, _, (((r1.trans rn).trans r2).trans rt).trans r3, ?_⟩
    have cs3 : (stailCore e2 M2).sameCsr e2 := by unfold stailCore; (repeat (first | exact Core.sameCsr_wr _ _ _ _ | exact Core.sameCsr_goto _ _ | refine (Core.sameCsr_wr _ _ _ _).trans ?_ | refine (Core.sameCsr_goto _ _).trans ?_))
    -- what snone loaded before the call, kept by tail (callee-saved)
    have K2_19 : K2.get 19 = ramRead M1 (s6v + 0x000002c7#32) .w := by
      simp [K2, snoneCore, Core.wr_get_ne, Core.wr_get_self, e1_22]
    have K2_21 : K2.get 21 = ramRead M1 (s6v + 0x000002cf#32) .w := by
      simp [K2, snoneCore, Core.wr_get_ne, Core.wr_get_self, e1_22]
    have K2_24 : K2.get 24 = ramRead M1 (s6v + 0x000002d3#32) .w := by
      simp [K2, snoneCore, Core.wr_get_ne, Core.wr_get_self, e1_22]
    have K2_25 : K2.get 25 = extend .b false (ramRead M1 (s6v + 0x000002d7#32) .b) := by
      simp [K2, snoneCore, Core.wr_get_ne, Core.wr_get_self, e1_22]
    have gS : ∀ r : Reg, r ≠ 18 → r ≠ 20 → (stailCore e2 M2).get r = e2.get r := fun r a b => by
      simp [stailCore, Core.wr_get_ne, a, b]
    have hcI : consumed M1 dfr ≤ filled M1 dfr := inv1.1
    have hfl := TP.hfilled
    have hds := TP.hdisc
    have hret := TP.ret
    rw [show (⟨K2, M1⟩ : Machine).core.get 10 = dfr from K2_10] at hfl hds hret
    rw [show (⟨K2, M1⟩ : Machine).core.get 11 = bufA from K2_11,
      show ((⟨K2, M1⟩ : Machine).core.get 12).toNat = bufLen from by
        rw [show (⟨K2, M1⟩ : Machine).core.get 12 = 0x1e8#32 from K2_12]; rfl] at hret
    have dsc1 : discarding M1 dfr ≤ 1 := by
      have := NP.disc; rw [show (⟨K1, R0⟩ : Machine).core.get 10 = dfr from K1_10] at this; exact this
    refine ⟨Quiet.of_sameCsr (cs3.trans TP.csr) qK2, ?_, ?_, ?_, ?_, .inr ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
    · simp [stailCore, Core.wr_get_ne]; exact (TPs 22 (by decide)).trans K2_22
    · simp [stailCore, Core.wr_get_ne]; exact (TPs 23 (by decide)).trans K2_23
    · simp [stailCore, Core.wr_get_ne]; exact TP.sp.trans K2_2
    · intro x hx
      have hx : ¬ RecvW (c.get 2) x := hx
      show M2 x = R0 x
      refine (TP.ram x ⟨?_, ?_, ?_⟩).trans (ram1 x hx)
      · show ¬ ((K2.get 10).toNat ≤ x.toNat ∧ x.toNat < (K2.get 10).toNat + 12); rw [K2_10]; exact fun h' => hx (.inl h')
      · show ¬ ((K2.get 11).toNat ≤ x.toNat ∧ x.toNat < (K2.get 11).toNat + (K2.get 12).toNat)
        rw [K2_11, K2_12]; exact fun h' => hx (.inr (.inl h'))
      · show ¬ ((K2.get 2).toNat - tailStack ≤ x.toNat ∧ x.toNat < (K2.get 2).toNat)
        rw [K2_2, show tailStack = 0x50 from rfl]; exact fun h' => hx (.inr (.inr (.inl ⟨by have := h'.1; omega, h'.2⟩)))
    · have := TP.inv
      show Inv M2 dfr bufLen
      rw [show (⟨K2, M1⟩ : Machine).core.get 10 = dfr from K2_10,
        show ((⟨K2, M1⟩ : Machine).core.get 12).toNat = bufLen from by
          rw [show (⟨K2, M1⟩ : Machine).core.get 12 = 0x1e8#32 from K2_12]; rfl] at this
      exact this
    · have := TP.hconsumed
      rw [show (⟨K2, M1⟩ : Machine).core.get 10 = dfr from K2_10] at this
      exact this
    · show (stailCore e2 M2).get 18 = _
      simp only [stailCore, Core.wr_get_ne _ _ _ _ _ (show (18 : Reg) ≠ 20 by decide),
        Core.wr_get_self _ _ _ _ (show (18 : Reg).val ≠ 0 by decide), alu_add]
      exact (BitVec.zero_add _).trans hret.1
    · show ((stailCore e2 M2).get 20).toNat = _
      simp only [stailCore, Core.wr_get_self _ _ _ _ (show (20 : Reg).val ≠ 0 by decide), alu_add]
      exact (congrArg BitVec.toNat (BitVec.zero_add _)).trans hret.2
    · show (M2 (dfr + 8)).toNat ≤ 1; rw [hds]; exact dsc1
    · show ((stailCore e2 M2).get 25).toNat = (M2 (dfr + 8)).toNat
      rw [gS 25 (by decide) (by decide), TPs 25 (by decide), K2_25, Next.lbu_val, hds]
      simp only [BitVec.toNat_ofNat]
      have := (M1 (dfr + 8)).isLt
      rw [show s6v + 0x000002d7#32 = dfr + 8 from rfl]; omega
    · show ((stailCore e2 M2).get 21).toNat ≤ ((stailCore e2 M2).get 24).toNat
      rw [gS 21 (by decide) (by decide), gS 24 (by decide) (by decide), TPs 21 (by decide), TPs 24 (by decide),
        K2_21, K2_24]
      exact hcI
    · show ((stailCore e2 M2).get 24).toNat - ((stailCore e2 M2).get 21).toNat = filled M2 dfr
      rw [gS 21 (by decide) (by decide), gS 24 (by decide) (by decide), TPs 21 (by decide), TPs 24 (by decide),
        K2_21, K2_24, hfl]
      rfl
    · show (stailCore e2 M2).get 19 = ramRead R0 0x8002a784 .w
      rw [gS 19 (by decide) (by decide), TPs 19 (by decide), K2_19]
      exact rd_congr _ (by decide) fun x h1 h2 => ram1 x (by
        rw [show (s6v + 0x000002c7#32).toNat = 0x8002a784 from rfl] at h1 h2
        unfold RecvW; rw [show dfr.toNat = 0x8002a78c from rfl, show bufA.toNat = 0x8002a590 from rfl,
          show msgA.toNat = 0x8002a580 from rfl]
        have : bufLen = 488 := rfl
        omega)
  · -- Some: park, bounds check, the request decoder
    have a01 : (e1.get 10).toNat = 1 := by omega
    have val := NP.val a01
    have a0o : e1.get 10 = 1 := BitVec.eq_of_toNat_eq a01
    have r2 := ssome e1 M1 e1pc qe1 (by rw [a0o]; rfl)
    let K3 := ssomeCore e1 M1
    have csK3 : K3.sameCsr e1 := by unfold K3 ssomeCore; (repeat (first | exact Core.sameCsr_wr _ _ _ _ | exact Core.sameCsr_goto _ _ | refine (Core.sameCsr_wr _ _ _ _).trans ?_ | refine (Core.sameCsr_goto _ _).trans ?_))
    have qK3 : Quiet K3 := Quiet.of_sameCsr csK3 qe1
    have K3_10 : K3.get 10 = dfr := by simp [K3, ssomeCore, Core.wr_get_ne, Core.wr_get_self, alu_add, e1_9]
    have K3_11 : K3.get 11 = bufA := by simp [K3, ssomeCore, Core.wr_get_ne, Core.wr_get_self, alu_add, e1_8]
    have K3_12 : K3.get 12 = 0x1e8#32 := by simp [K3, ssomeCore, Core.wr_get_ne, Core.wr_get_self, alu_add]
    have K3_1 : K3.get 1 = 0x80003e4e := by simp [K3, ssomeCore, Core.wr_get_self]
    have K3_2 : K3.get 2 = c.get 2 := by simp [K3, ssomeCore, Core.wr_get_ne, e1_2]
    have K3_18 : K3.get 18 = e1.get 11 := by simp [K3, ssomeCore, Core.wr_get_ne, Core.wr_get_self, alu_add]
    have K3_19 : K3.get 19 = 0x1e8#32 := by simp [K3, ssomeCore, Core.wr_get_ne, e1_19]
    have K3_22 : K3.get 22 = s6v := by simp [K3, ssomeCore, Core.wr_get_ne, e1_22]
    have K3_23 : K3.get 23 = s7v := by simp [K3, ssomeCore, Core.wr_get_ne, e1_23]
    have K3_8 : K3.get 8 = bufA := by simp [K3, ssomeCore, Core.wr_get_ne, e1_8]
    have E3 : CallEnv parkPc parkStack ⟨K3, M1⟩ :=
      envM K3 M1 parkPc parkStack (by decide) rfl qK3 K3_10 K3_11 K3_12 K3_2 (by rw [K3_1]; decide)
    obtain ⟨kp, ⟨e3, M3⟩, rp, PP⟩ := Park.park_from_copy hC ⟨K3, M1⟩ E3 (by
      show Inv M1 (K3.get 10) (K3.get 12).toNat; rw [K3_10, K3_12]; exact inv1)
    have PPs : ∀ r : Reg, r.val ∉ callerSaved → e3.get r = K3.get r := PP.saved
    have qe3 : Quiet e3 := Quiet.of_sameCsr PP.csr qK3
    have e3_19 : e3.get 19 = 0x1e8#32 := (PPs 19 (by decide)).trans K3_19
    have e3_22 : e3.get 22 = s6v := (PPs 22 (by decide)).trans K3_22
    have hret := PP.ret
    have hinv1 := inv1
    have hpark : (e3.get 10).toNat ≤ 0x1e8 := by
      have : filled M1 dfr ≤ bufLen := inv1.2
      have eq : (e3.get 10).toNat = filled M1 dfr - consumed M1 dfr := by
        have := PP.ret; rw [show (⟨K3, M1⟩ : Machine).core.get 10 = dfr from K3_10] at this; exact this
      have : bufLen = 0x1e8 := rfl
      omega
    have r3 := sdec e3 M3 (PP.pc.trans K3_1) qe3 (by rw [e3_22]; decide) (by rw [e3_22]; decide)
      (by rw [e3_19]; simp only [taken, alu_add, alu_sub, BitVec.ult, Bool.not_eq_false', decide_eq_true_eq]
          refine decide_eq_true ?_
          show ((0x1e8#32 : Word) - e3.get 10).toNat < (0 + 0x1e9#32 : Word).toNat
          rw [show (0 + 0x1e9#32 : Word).toNat = 0x1e9 from rfl]; bv_omega)
    let D := sdecCore e3 M3
    let R4 := sdecRam e3 M3
    have csD : D.sameCsr e3 := by unfold D sdecCore; (repeat (first | exact Core.sameCsr_wr _ _ _ _ | exact Core.sameCsr_goto _ _ | refine (Core.sameCsr_wr _ _ _ _).trans ?_ | refine (Core.sameCsr_goto _ _).trans ?_))
    have qD : Quiet D := Quiet.of_sameCsr csD qe3
    have gD : ∀ r : Reg, r ≠ 1 → r ≠ 9 → r ≠ 10 → r ≠ 11 → r ≠ 12 → r ≠ 13 → D.get r = e3.get r := fun r a b c' d' f' g' => by
      simp [D, sdecCore, Core.wr_get_ne, a, b, c', d', f', g']
    have e3_23 : e3.get 23 = s7v := (PPs 23 (by decide)).trans K3_23
    have D10 : D.get 10 = msgA := by simp [D, sdecCore, Core.wr_get_ne, Core.wr_get_self, alu_add, e3_23]; rfl
    have D11 : D.get 11 = bufA := by
      simp [D, sdecCore, Core.wr_get_ne, Core.wr_get_self, alu_add]; exact (PPs 8 (by decide)).trans K3_8
    have D12 : D.get 12 = 0x1e8#32 - e3.get 10 := by
      simp [D, sdecCore, Core.wr_get_ne, Core.wr_get_self, alu_sub, e3_19]
    have D13 : D.get 13 = e1.get 11 := by
      simp [D, sdecCore, Core.wr_get_ne, Core.wr_get_self, alu_add]; exact (PPs 18 (by decide)).trans K3_18
    have D1 : D.get 1 = 0x80003e70 := by simp [D, sdecCore, Core.wr_get_self]
    -- parked <= 484: the Some frame's bytes were consumed
    have hk := val.2.2
    rw [show (⟨K1, R0⟩ : Machine).core.get 10 = dfr from K1_10] at hk
    have hk' : (e1.get 11).toNat < consumed M1 dfr := hk
    have hpk : (e3.get 10).toNat + 4 ≤ 0x1e8 := by
      have eq : (e3.get 10).toNat = filled M1 dfr - consumed M1 dfr := by
        have := PP.ret; rw [show (⟨K3, M1⟩ : Machine).core.get 10 = dfr from K3_10] at this; exact this
      have hf : filled M1 dfr ≤ bufLen := inv1.2
      have : bufLen = 0x1e8 := rfl
      have v1 : 2 < (e1.get 11).toNat := val.1
      omega
    have hl : (D.get 12).toNat = 0x1e8 - (e3.get 10).toNat := by rw [D12]; exact sub_toNat _ _ (by
      rw [show (0x1e8#32 : Word).toNat = 0x1e8 from rfl]; omega)
    have r4 := sfrom D R4 rfl qD
      (by show taken .ltu (D.get 12) (alu .add 0 0x00000003#32) = false
          simp only [taken, BitVec.ult, decide_eq_false_iff_not]
          show ¬ ((D.get 12).toNat < (alu .add 0 0x00000003#32 : Word).toNat)
          rw [show (alu .add 0 0x00000003#32 : Word).toNat = 3 from rfl]; omega)
      (by rw [D11]; decide) (by rw [D11]; decide) (by rw [D11]; decide) (by rw [D11]; decide)
      (by rw [D11]; decide) (by rw [D11]; decide)
      (by rw [D10]; decide) (by rw [D10]; decide) (by rw [D10]; decide) (by rw [D10]; decide)
      (by rw [D10]; decide) (by rw [D10]; decide) (by rw [D10]; decide) (by rw [D10]; decide)
      (by rw [D10]; decide) (by rw [D10]; decide) (by rw [D1]; decide)
    refine ⟨_, _, ((((r1.trans rn).trans r2).trans rp).trans r3).trans r4, ?_⟩
    have M4 : R4 = ramWrite M3 (e3.get 22 + 0x000002db#32) (e3.get 10) .w := rfl
    have w4 : ∀ x : Word, ¬ (0x8002a798 ≤ x.toNat ∧ x.toNat < 0x8002a798 + 4) → R4 x = M3 x := by
      intro x hx; rw [M4, e3_22]; exact wr_byte_other _ _ _ _ (by decide) (by
        rw [show (s6v + 0x000002db#32).toNat = 0x8002a798 from rfl]; omega)
    -- from_decoded writes only the 16-byte message
    have w5 : ∀ x : Word, ¬ (msgA.toNat ≤ x.toNat ∧ x.toNat < msgA.toNat + 16) → sfromRam D R4 x = R4 x := by
      intro x hx
      have hx' : x.toNat < 0x8002a580 ∨ 0x8002a590 ≤ x.toNat := by
        rw [show msgA.toNat = 0x8002a580 from rfl] at hx; omega
      simp only [sfromRam, D10]
      rw [wr_byte_other _ _ _ _ (by decide) (by rw [show (msgA + 0x0000000c#32).toNat = 0x8002a58c from rfl]; omega)]
      rw [ramWrite, ramPut_ne _ (fun e => by subst e; rw [show (msgA + 0x0000000a#32).toNat = 0x8002a58a from rfl] at hx'; omega)]
      rw [ramWrite, ramPut_ne _ (fun e => by subst e; rw [show (msgA + 0x00000008#32 + 1).toNat = 0x8002a589 from rfl] at hx'; omega),
        ramPut_ne _ (fun e => by subst e; rw [show (msgA + 0x00000008#32).toNat = 0x8002a588 from rfl] at hx'; omega)]
      rw [wr_byte_other _ _ _ _ (by decide) (by rw [show (msgA + 0x00000004#32).toNat = 0x8002a584 from rfl]; omega),
        wr_byte_other _ _ _ _ (by decide) (by rw [show msgA.toNat = 0x8002a580 from rfl]; omega)]
    have hp3 := PP.hconsumed
    have hf3 := PP.hfilled
    rw [show (⟨K3, M1⟩ : Machine).core.get 10 = dfr from K3_10] at hp3 hf3
    let Fc := sfromCore D R4
    have gF : ∀ r : Reg, r ≠ 14 → r ≠ 15 → r ≠ 16 → Fc.get r = D.get r := fun r a b c' => by
      simp [Fc, sfromCore, Core.wr_get_ne, a, b, c']
    have csF : Fc.sameCsr D := by unfold Fc sfromCore; (repeat (first | exact Core.sameCsr_wr _ _ _ _ | exact Core.sameCsr_goto _ _ | refine (Core.sameCsr_wr _ _ _ _).trans ?_ | refine (Core.sameCsr_goto _ _).trans ?_))
    refine ⟨Quiet.of_sameCsr csF qD, ?_, ?_, ?_, ?_, .inl ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
    · rw [gF 22 (by decide) (by decide) (by decide), gD 22 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
      exact e3_22
    · rw [gF 23 (by decide) (by decide) (by decide), gD 23 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
      exact e3_23
    · rw [gF 2 (by decide) (by decide) (by decide), gD 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
      exact PP.sp.trans K3_2
    · intro x hx
      have hx : ¬ RecvW (c.get 2) x := hx
      show sfromRam D R4 x = R0 x
      rw [w5 x (fun h' => hx (.inr (.inr (.inr (.inr h'))))), w4 x (fun h' => hx (.inr (.inr (.inr (.inl h')))))]
      refine (PP.ram x ⟨?_, ?_, ?_⟩).trans (ram1 x hx)
      · show ¬ ((K3.get 10).toNat ≤ x.toNat ∧ x.toNat < (K3.get 10).toNat + 12); rw [K3_10]; exact fun h' => hx (.inl h')
      · show ¬ ((K3.get 11).toNat ≤ x.toNat ∧ x.toNat < (K3.get 11).toNat + (K3.get 12).toNat)
        rw [K3_11, K3_12]; exact fun h' => hx (.inr (.inl h'))
      · show ¬ ((K3.get 2).toNat - parkStack ≤ x.toNat ∧ x.toNat < (K3.get 2).toNat)
        rw [K3_2, show parkStack = 0x40 from rfl]; exact fun h' => hx (.inr (.inr (.inl ⟨by have := h'.1; omega, h'.2⟩)))
    · show Fc.pc = 0x80003e70
      simp only [Fc, sfromCore, Core.goto_pc]; exact D1
    · show ramRead (sfromRam D R4) msgA .w = bufA
      simp only [sfromRam, D10, D11]
      rw [rd_wr_far _ _ _ _ _ (by decide) (by decide) (by decide), rd_wr_far _ _ _ _ _ (by decide) (by decide) (by decide),
        rd_wr_far _ _ _ _ _ (by decide) (by decide) (by decide), rd_wr_far _ _ _ _ _ (by decide) (by decide) (by decide),
        ramRead_ramWrite_w]
    · show 3 ≤ (ramRead (sfromRam D R4) (msgA + 4) .w).toNat
      simp only [sfromRam, D10]
      rw [rd_wr_far _ _ _ _ _ (by decide) (by decide) (by decide), rd_wr_far _ _ _ _ _ (by decide) (by decide) (by decide),
        rd_wr_far _ _ _ _ _ (by decide) (by decide) (by decide), show (msgA + 4 : Word) = msgA + 0x00000004#32 from rfl,
        ramRead_ramWrite_w, hl]; omega
    · show (ramRead (sfromRam D R4) (msgA + 4) .w).toNat ≤ bufLen
      simp only [sfromRam, D10]
      rw [rd_wr_far _ _ _ _ _ (by decide) (by decide) (by decide), rd_wr_far _ _ _ _ _ (by decide) (by decide) (by decide),
        rd_wr_far _ _ _ _ _ (by decide) (by decide) (by decide), show (msgA + 4 : Word) = msgA + 0x00000004#32 from rfl,
        ramRead_ramWrite_w, hl]; have : bufLen = 0x1e8 := rfl; omega
    · show 2 < (ramRead (sfromRam D R4) (msgA + 0xc) .w).toNat
      simp only [sfromRam, D10]
      rw [show (msgA + 0xc : Word) = msgA + 0x0000000c#32 from rfl, ramRead_ramWrite_w, D13]; exact val.1
    · show (ramRead (sfromRam D R4) (msgA + 0xc) .w).toNat ≤ bufLen
      simp only [sfromRam, D10]
      rw [show (msgA + 0xc : Word) = msgA + 0x0000000c#32 from rfl, ramRead_ramWrite_w, D13]
      have := val.2.1
      rw [show ((⟨K1, R0⟩ : Machine).core.get 12).toNat = bufLen from by
        rw [show (⟨K1, R0⟩ : Machine).core.get 12 = 0x1e8#32 from K1_12]; rfl] at this
      exact this
    · show (ramRead (sfromRam D R4) dfr .w).toNat = 0
      rw [rd_congr dfr (by decide) (ram' := sfromRam D R4) (ram := M3) fun x h1 h2 => by
        rw [show dfr.toNat = 0x8002a78c from rfl] at h1 h2
        rw [w5 x (by rw [show msgA.toNat = 0x8002a580 from rfl]; omega), w4 x (by omega)]]
      exact hp3
    · show (ramRead (sfromRam D R4) (dfr + 4) .w).toNat = 0
      rw [rd_congr (dfr + 4) (by decide) (ram' := sfromRam D R4) (ram := M3) fun x h1 h2 => by
        rw [show (dfr + 4).toNat = 0x8002a790 from rfl] at h1 h2
        rw [w5 x (by rw [show msgA.toNat = 0x8002a580 from rfl]; omega), w4 x (by omega)]]
      exact hf3

end E5R.Rmk.Deframer.Session
