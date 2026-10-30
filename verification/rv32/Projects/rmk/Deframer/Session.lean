/-
  The Rynk session's receive step (main task poll, loop head 0x80003e1a) on the pinned RMK image,
  composed from the deframer contracts at their real call sites.

  Original e5r code, Apache-2.0.

  PROVED here, CONDITIONAL ON `CopyContract` (memmove; a hypothesis, not an axiom, not proved):
  `recv_step`: from every machine at the session loop head with the deframer invariant
  (`SessPre`: the session's s6/s7 bases, a stack below which the deframer and buffer lie), a quiet
  run (so: no panic on the way, whatever bytes the buffer holds) reaches
  * `Some(k)`: the request decoder's call 0x8001c3c6 with a1 = buffer, a3 = k, 2 < k ≤ 488, the
    deframer emptied and its pending bytes parked (bounds check 0x80003e5a not taken); or
  * `None`: 0x80003f7c after `tail`, with the invariant again and consumed = 0;
  writing RAM only in the deframer, the buffer, 0x70 stack bytes and the session word s6+0x2db.

  NOT proved: what follows either point (the request decoder and dispatch, the response, unpark,
  the UART read future and the executor between polls), so this is a step toward `SessionSafe`, not
  `SessionSafe`.
-/
import Projects.rmk.Deframer.CobsDischarge
import Projects.rmk.Deframer.TailCopy
import Projects.rmk.Deframer.Unpark
import Projects.rmk.Deframer.SessionSegs

set_option maxRecDepth 100000

namespace E5R.Rmk.Deframer.Session
open E5R E5R.Rmk.SessionFetch E5R.Rmk.Deframer.Tail

/-- The session bases in s6/s7 (task future statics) and where the deframer and buffer are. -/
def s6v : Word := 0x8002a4bd
def s7v : Word := 0x8002a3cf
def dfr : Word := 0x8002a78c
def bufA : Word := 0x8002a590

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
  (sp.toNat - 0x70 ≤ x.toNat ∧ x.toNat < sp.toNat) ∨ (0x8002a798 ≤ x.toNat ∧ x.toNat < 0x8002a798 + 4)

structure RecvOut (m₀ m : Machine) : Prop where
  quiet : Quiet m.core
  s6 : m.core.get 22 = s6v
  s7 : m.core.get 23 = s7v
  sp : m.core.get 2 = m₀.core.get 2
  ram : ∀ x, ¬ RecvW (m₀.core.get 2) x → m.ram x = m₀.ram x
  out : (m.core.pc = 0x8001c3c6 ∧ m.core.get 11 = bufA ∧ 2 < (m.core.get 13).toNat ∧
          (m.core.get 13).toNat ≤ bufLen ∧ consumed m.ram dfr = 0 ∧ filled m.ram dfr = 0) ∨
        (m.core.pc = 0x80003f7c ∧ Inv m.ram dfr bufLen ∧ consumed m.ram dfr = 0)

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
  have csK1 : K1.sameCsr c := by unfold K1 scallCore; csr_chain
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
    have csK2 : K2.sameCsr e1 := by unfold K2 snoneCore; csr_chain
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
    have cs3 : (stailCore e2 M2).sameCsr e2 := by unfold stailCore; csr_chain
    refine ⟨Quiet.of_sameCsr (cs3.trans TP.csr) qK2, ?_, ?_, ?_, ?_, .inr ⟨rfl, ?_, ?_⟩⟩
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
  · -- Some: park, bounds check, the request decoder
    have a01 : (e1.get 10).toNat = 1 := by omega
    have val := NP.val a01
    have a0o : e1.get 10 = 1 := BitVec.eq_of_toNat_eq a01
    have r2 := ssome e1 M1 e1pc qe1 (by rw [a0o]; rfl)
    let K3 := ssomeCore e1 M1
    have csK3 : K3.sameCsr e1 := by unfold K3 ssomeCore; csr_chain
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
    refine ⟨_, _, (((r1.trans rn).trans r2).trans rp).trans r3, ?_⟩
    let D := sdecCore e3 M3
    have csD : D.sameCsr e3 := by unfold D sdecCore; csr_chain
    have gD : ∀ r : Reg, r ≠ 1 → r ≠ 9 → r ≠ 10 → r ≠ 11 → r ≠ 12 → r ≠ 13 → D.get r = e3.get r := fun r a b c' d' f' g' => by
      simp [D, sdecCore, Core.wr_get_ne, a, b, c', d', f', g']
    have M4 : sdecRam e3 M3 = ramWrite M3 (e3.get 22 + 0x000002db#32) (e3.get 10) .w := rfl
    have w4 : ∀ x : Word, ¬ (0x8002a798 ≤ x.toNat ∧ x.toNat < 0x8002a798 + 4) → sdecRam e3 M3 x = M3 x := by
      intro x hx; rw [M4, e3_22]; exact wr_byte_other _ _ _ _ (by decide) (by
        rw [show (s6v + 0x000002db#32).toNat = 0x8002a798 from rfl]; omega)
    have hp3 := PP.hconsumed
    have hf3 := PP.hfilled
    rw [show (⟨K3, M1⟩ : Machine).core.get 10 = dfr from K3_10] at hp3 hf3
    refine ⟨Quiet.of_sameCsr csD qe3, ?_, ?_, ?_, ?_, .inl ⟨rfl, ?_, ?_, ?_, ?_, ?_⟩⟩
    · rw [gD 22 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact e3_22
    · rw [gD 23 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
      exact (PPs 23 (by decide)).trans K3_23
    · rw [gD 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
      exact PP.sp.trans K3_2
    · intro x hx
      have hx : ¬ RecvW (c.get 2) x := hx
      show sdecRam e3 M3 x = R0 x
      rw [w4 x (fun h' => hx (.inr (.inr (.inr h'))))]
      refine (PP.ram x ⟨?_, ?_, ?_⟩).trans (ram1 x hx)
      · show ¬ ((K3.get 10).toNat ≤ x.toNat ∧ x.toNat < (K3.get 10).toNat + 12); rw [K3_10]; exact fun h' => hx (.inl h')
      · show ¬ ((K3.get 11).toNat ≤ x.toNat ∧ x.toNat < (K3.get 11).toNat + (K3.get 12).toNat)
        rw [K3_11, K3_12]; exact fun h' => hx (.inr (.inl h'))
      · show ¬ ((K3.get 2).toNat - parkStack ≤ x.toNat ∧ x.toNat < (K3.get 2).toNat)
        rw [K3_2, show parkStack = 0x40 from rfl]; exact fun h' => hx (.inr (.inr (.inl ⟨by have := h'.1; omega, h'.2⟩)))
    · simp [D, sdecCore, Core.wr_get_ne, Core.wr_get_self, alu_add]
      exact (PPs 8 (by decide)).trans K3_8
    · have : D.get 13 = e1.get 11 := by
        simp [D, sdecCore, Core.wr_get_ne, Core.wr_get_self, alu_add]
        exact (PPs 18 (by decide)).trans K3_18
      rw [this]; exact val.1
    · have : D.get 13 = e1.get 11 := by
        simp [D, sdecCore, Core.wr_get_ne, Core.wr_get_self, alu_add]
        exact (PPs 18 (by decide)).trans K3_18
      rw [this]
      have := val.2.1
      rw [show ((⟨K1, R0⟩ : Machine).core.get 12).toNat = bufLen from by
        rw [show (⟨K1, R0⟩ : Machine).core.get 12 = 0x1e8#32 from K1_12]; rfl] at this
      exact this
    · show (ramRead (sdecRam e3 M3) dfr .w).toNat = 0
      rw [rd_congr dfr (by decide) (ram' := sdecRam e3 M3) (ram := M3) fun x h1 h2 => w4 x (by
        rw [show dfr.toNat = 0x8002a78c from rfl] at h1 h2; omega)]
      exact hp3
    · show (ramRead (sdecRam e3 M3) (dfr + 4) .w).toNat = 0
      rw [rd_congr (dfr + 4) (by decide) (ram' := sdecRam e3 M3) (ram := M3) fun x h1 h2 => w4 x (by
        rw [show (dfr + 4).toNat = 0x8002a790 from rfl] at h1 h2; omega)]
      exact hf3

end E5R.Rmk.Deframer.Session
