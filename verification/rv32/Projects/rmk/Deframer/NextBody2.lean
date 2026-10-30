/-
  `Deframer::next`: one turn of the frame loop, part 2: a delimiter found while not discarding.
  The frame is COBS-decoded in place by the wrapper (0x8001e006, `Wrap.wrap`), and then
  * an error or a frame of at most 2 bytes: back to the loop head, cursor := z + 1;
  * a longer frame: `Some(len)`, moved to the buffer's front by memmove unless already there.

  Original e5r code, Apache-2.0.

  PROVED here, CONDITIONAL ON `CopyContract` AND `CobsReportContract` (hypotheses, not axioms, not
  proved here): `call_case`.
-/
import Projects.rmk.Deframer.NextBody1
import Projects.rmk.Deframer.Wrap

set_option maxRecDepth 100000

namespace E5R.Rmk.Deframer.Next
open E5R E5R.Rmk.NextFetch E5R.Rmk.Deframer.Tail

theorem s5_toNat (cur : Word) (j : Nat) (h : cur.toNat + j < 2 ^ 32) :
    (alu .sub cur (0 - BitVec.ofNat 32 j)).toNat = cur.toNat + j := by
  simp only [alu_sub]; bv_omega

theorem negj_toNat (j : Nat) (h : j < 2 ^ 32) : (alu .sub 0 (0 - BitVec.ofNat 32 j)).toNat = j := by
  simp only [alu_sub]; bv_omega

theorem ng4 (c : Core) : ng c + 0x00000004#32 + 0x4#32 = ng c + 0x00000008#32 := by
  rw [BitVec.add_assoc]; rfl

theorem call_case (hC : CopyContract) (hR : CobsReportContract) (c : Core) (R0 : Word → BitVec 8)
    (E : CallEnv nextPc nextStack ⟨c, R0⟩) (d : Core) (M : Word → BitVec 8) (h : LoopInv c R0 d M)
    (e : Core) (j : Nat) (hf : FoundAt c d e M j) (h0 : d.get 23 = 0) :
    (∃ k m, QRun B img k ⟨e, M⟩ m ∧ NextPost ⟨c, R0⟩ m) ∨
    (∃ k d' M', QRun B img k ⟨e, M⟩ ⟨d', M'⟩ ∧ LoopInv c R0 d' M' ∧
      (d'.get 8).toNat - (d'.get 9).toNat < (d.get 8).toNat - (d.get 9).toNat) := by
  have hE := envNat c R0 E
  have hsp := hE.sp
  have hp := hE.self
  have hb := hE.buf
  have hS := hE.sepS
  have hsep := hE.sep
  have hlen := hE.len
  have hcl := h.curle
  have hfl := h.fle
  have hj := hf.jlt
  rw [sub_toNat _ _ hcl] at hj
  have eg := ng_toNat c hE
  -- the found core
  have es : ∀ r : Reg, r ≠ 11 → r ≠ 12 → r ≠ 13 → r ≠ 14 → r ≠ 15 → e.get r = d.get r := hf.same
  have e19 : e.get 19 = c.get 10 := (es 19 (by decide) (by decide) (by decide) (by decide) (by decide)).trans h.self
  have e9 : e.get 9 = d.get 9 := es 9 (by decide) (by decide) (by decide) (by decide) (by decide)
  have e8 : e.get 8 = d.get 8 := es 8 (by decide) (by decide) (by decide) (by decide) (by decide)
  have e18 : e.get 18 = c.get 12 := (es 18 (by decide) (by decide) (by decide) (by decide) (by decide)).trans h.len
  have e10 : e.get 10 = 0 := by
    rw [es 10 (by decide) (by decide) (by decide) (by decide) (by decide), h.a0, h0]
  have e2 : e.get 2 = ng c := (es 2 (by decide) (by decide) (by decide) (by decide) (by decide)).trans h.sp
  let s5 := alu .sub (d.get 9) (0 - BitVec.ofNat 32 j)
  let s11 := alu .add s5 0x00000001#32
  have hs5 : s5.toNat = (d.get 9).toNat + j := s5_toNat _ _ (by omega)
  have hs11 : s11.toNat = (d.get 9).toNat + j + 1 := s11_toNat _ _ (by omega)
  have e8a : (c.get 10 + 0x00000008#32).toNat = (c.get 10).toNat + 8 := add_toNat _ 8 (by omega)
  have e4a : (c.get 10 + 4).toNat = (c.get 10).toNat + 4 := add_toNat _ 4 (by omega)
  have e8b : (c.get 10 + 8).toNat = (c.get 10).toNat + 8 := add_toNat _ 8 (by omega)
  -- to the wrapper
  have r1 := ncall e M hf.pc hf.quiet (by rw [e19]; exact E.selfAl) (by rw [e19, B_ram]; omega)
    (by rw [e10]; rfl)
    (by rw [e9, hf.a2]; simp only [taken, BitVec.ult, decide_eq_false_iff_not]
        rw [show alu .sub (d.get 9) (0 - BitVec.ofNat 32 j) = s5 from rfl, hs5]; omega)
    (by rw [e18, e9, hf.a2]; simp only [taken, BitVec.ult, decide_eq_false_iff_not]
        rw [show alu .sub (d.get 9) (0 - BitVec.ofNat 32 j) = s5 from rfl, hs5]; omega)
  let K := ncallCore e M
  let M1 := ncallRam e M
  have csK : K.sameCsr e := by unfold K ncallCore; csr_chain
  have gK : ∀ r : Reg, r ≠ 1 → r ≠ 10 → r ≠ 12 → r ≠ 21 → r ≠ 27 → K.get r = e.get r := fun r a b c' d' f' => by
    simp [K, ncallCore, Core.wr_get_ne, a, b, c', d', f']
  have K10 : K.get 10 = ng c + 0x00000004#32 := by
    simp [K, ncallCore, Core.wr_get_ne, Core.wr_get_self, alu_add, e2]
  have K11 : K.get 11 = c.get 11 + d.get 9 := by
    rw [gK 11 (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hf.a1
  have K12' : K.get 12 = alu .sub 0 (e.get 12) := by
    simp only [K, ncallCore, Core.wr_get_ne _ _ _ _ _ (show (12 : Reg) ≠ 1 by decide),
      Core.wr_get_ne _ _ _ _ _ (show (12 : Reg) ≠ 10 by decide),
      Core.wr_get_self _ _ _ _ (show (12 : Reg).val ≠ 0 by decide)]
  have K12 : (K.get 12).toNat = j := by rw [K12', hf.a2]; exact negj_toNat j (by omega)
  have K27 : K.get 27 = s11 := by simp [K, ncallCore, Core.wr_get_ne, Core.wr_get_self, e9, hf.a2, s11, s5]
  have K2 : K.get 2 = ng c := (gK 2 (by decide) (by decide) (by decide) (by decide) (by decide)).trans e2
  have M1eq : M1 = ramWrite M (c.get 10) s11 .w := by simp only [M1, ncallRam, e19, e9, hf.a2, s11, s5]
  have M1o : ∀ x : Word, (x.toNat < (c.get 10).toNat ∨ (c.get 10).toNat + 4 ≤ x.toNat) → M1 x = M x := by
    intro x hx; rw [M1eq]; exact wr_byte_other _ _ _ _ (by omega) hx
  have qK : Quiet K := Quiet.of_sameCsr csK hf.quiet
  have eo : (ng c + 0x00000004#32).toNat = (ng c).toNat + 4 := add_toNat _ _ (by omega)
  have ed : (c.get 11 + d.get 9).toNat = (c.get 11).toNat + (d.get 9).toNat := add_toNat' _ _ (by omega)
  have env : Wrap.WrapEnv ⟨K, M1⟩ := by
    refine ⟨rfl, qK, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · show (K.get 12).toNat ≤ bufLen; rw [K12, ← hlen]; omega
    · show B.inRam (K.get 11) (K.get 12).toNat = true; rw [K11, K12, B_ram, ed]; omega
    · show B.inRam (K.get 10) 8 = true; rw [K10, B_ram, eo]; omega
    · show (K.get 10).toNat % 4 = 0; rw [K10, eo]; have := E.spAl; unfold ng at eg ⊢; bv_omega
    · show 0x80029bc8 + 0x30 ≤ (K.get 2).toNat ∧ (K.get 2).toNat ≤ 0x81000000; rw [K2]; omega
    · show (K.get 2).toNat % 4 = 0; rw [K2]; have := E.spAl; unfold ng at eg ⊢; bv_omega
    · show (K.get 11).toNat + (K.get 12).toNat ≤ (K.get 2).toNat - 0x30 ∨ (K.get 2).toNat ≤ (K.get 11).toNat
      rw [K11, K12, K2, ed]; omega
    · show (K.get 10).toNat + 8 ≤ (K.get 2).toNat - 0x30 ∨ (K.get 2).toNat ≤ (K.get 10).toNat
      rw [K10, K2, eo]; omega
    · show (K.get 11).toNat + (K.get 12).toNat ≤ (K.get 10).toNat ∨ (K.get 10).toNat + 8 ≤ (K.get 11).toNat
      rw [K11, K12, K10, ed, eo]; omega
    · show (K.get 1).getLsbD 0 = false
      simp only [K, ncallCore, Core.wr_get_self _ _ _ _ (show (1 : Reg).val ≠ 0 by decide)]; decide
  obtain ⟨kw, ⟨e2', M2⟩, rw2, P⟩ := Wrap.wrap hR _ env
  -- after the wrapper
  have Preg : ∀ r : Reg, r.val ∉ callerSaved → e2'.get r = K.get r := P.regs
  have P2 : ∀ x : Word, ¬ ((c.get 11).toNat + (d.get 9).toNat ≤ x.toNat ∧ x.toNat < (c.get 11).toNat + (d.get 9).toNat + j) →
      ¬ ((ng c).toNat + 4 ≤ x.toNat ∧ x.toNat < (ng c).toNat + 4 + 8) →
      ¬ ((ng c).toNat - 0x30 ≤ x.toNat ∧ x.toNat < (ng c).toNat) → M2 x = M1 x := by
    intro x a b c'
    refine P.ram x ?_ ?_ ?_
    · show ¬ ((K.get 11).toNat ≤ x.toNat ∧ x.toNat < (K.get 11).toNat + (K.get 12).toNat)
      rw [K11, K12, ed]; exact a
    · show ¬ ((K.get 10).toNat ≤ x.toNat ∧ x.toNat < (K.get 10).toNat + 8); rw [K10, eo]; exact b
    · show ¬ ((K.get 2).toNat - 0x30 ≤ x.toNat ∧ x.toNat < (K.get 2).toNat); rw [K2]; exact c'
  have pc2 : e2'.pc = 0x8001d4c8 := P.pc.trans (by simp [K, ncallCore, Core.wr_get_self])
  have q2 : Quiet e2' := Quiet.of_sameCsr P.csr qK
  have cs2 : e2'.sameCsr d := P.csr.trans (csK.trans hf.csr)
  -- the registers next keeps across the call
  have keepK : ∀ r : Reg, r.val ∉ callerSaved → r ≠ 1 → r ≠ 21 → r ≠ 27 → e2'.get r = d.get r := by
    intro r hr a b c'
    have h10 : r ≠ 10 := fun he => hr (by subst he; decide)
    have h12 : r ≠ 12 := fun he => hr (by subst he; decide)
    rw [Preg r hr, gK r a h10 h12 b c']
    exact es r (fun he => hr (by subst he; decide)) h12 (fun he => hr (by subst he; decide))
      (fun he => hr (by subst he; decide)) (fun he => hr (by subst he; decide))
  have f2 : e2'.get 2 = ng c := (Preg 2 (by decide)).trans K2
  have f8 : e2'.get 8 = d.get 8 := keepK 8 (by decide) (by decide) (by decide) (by decide)
  have f9 : e2'.get 9 = d.get 9 := keepK 9 (by decide) (by decide) (by decide) (by decide)
  have f18 : e2'.get 18 = c.get 12 := (keepK 18 (by decide) (by decide) (by decide) (by decide)).trans h.len
  have f20 : e2'.get 20 = c.get 11 := (keepK 20 (by decide) (by decide) (by decide) (by decide)).trans h.buf
  have f23 : e2'.get 23 = 0 := (keepK 23 (by decide) (by decide) (by decide) (by decide)).trans h0
  have f25 : e2'.get 25 = 0xffffffff#32 := (keepK 25 (by decide) (by decide) (by decide) (by decide)).trans h.s9
  have f26 : e2'.get 26 = 2#32 := (keepK 26 (by decide) (by decide) (by decide) (by decide)).trans h.s10
  have f27 : e2'.get 27 = s11 := (Preg 27 (by decide)).trans K27
  have hal4 : (e2'.get 2 + 0x00000004#32).toNat % 4 = 0 := by
    rw [f2, eo]; have := E.spAl; unfold ng at eg ⊢; bv_omega
  have hin4 : B.inRam (e2'.get 2 + 0x00000004#32) 4 = true := by rw [f2, B_ram, eo]; omega
  have e8o : (ng c + 0x00000008#32).toNat = (ng c).toNat + 8 := add_toNat _ _ (by omega)
  have hal8 : (e2'.get 2 + 0x00000008#32).toNat % 4 = 0 := by
    rw [f2, e8o]; have := E.spAl; unfold ng at eg ⊢; bv_omega
  have hin8 : B.inRam (e2'.get 2 + 0x00000008#32) 4 = true := by rw [f2, B_ram, e8o]; omega
  have geu : taken .geu (e2'.get 8) (e2'.get 27) = true := by
    rw [f8, f27]; simp only [taken, BitVec.ult, Bool.not_eq_true', decide_eq_false_iff_not]; omega
  -- RAM after the call, outside the decoded frame and the wrapper's stack
  have M2o : ∀ x : Word, ¬ ((c.get 11).toNat ≤ x.toNat ∧ x.toNat < (c.get 11).toNat + (c.get 12).toNat) →
      ¬ ((c.get 2).toNat - 0x70 ≤ x.toNat ∧ x.toNat < (c.get 2).toNat - 0x34) →
      (x.toNat < (c.get 10).toNat ∨ (c.get 10).toNat + 4 ≤ x.toNat) → M2 x = M x := by
    intro x a b c'
    rw [P2 x (by omega) (by omega) (by omega)]; exact M1o x c'
  have fcur2 : ramRead M2 (c.get 10) .w = s11 := by
    rw [rd_congr (c.get 10) (by omega) (ram' := M2) (ram := M1) fun x h1 h2 => P2 x (by omega) (by omega) (by omega),
      M1eq, ramRead_ramWrite_w]
  have ffil2 : ramRead M2 (c.get 10 + 4) .w = ramRead M (c.get 10 + 4) .w :=
    rd_congr _ (by omega) fun x h1 h2 => M2o x (by omega) (by omega) (by omega)
  have fdisc2 : M2 (c.get 10 + 8) = M (c.get 10 + 8) := M2o _ (by omega) (by omega) (by omega)
  have slot2 : ∀ x : Word, (c.get 2).toNat - 0x40 + 0xc ≤ x.toNat → x.toNat < (c.get 2).toNat → M2 x = M x :=
    fun x a b => M2o x (by omega) (by omega) (by omega)
  have ram2 : ∀ x, Outside (c.get 10) (c.get 11) (c.get 12).toNat (c.get 2) nextStack x → M2 x = M x := by
    intro x hx
    have a : ¬ ((c.get 10).toNat ≤ x.toNat ∧ x.toNat < (c.get 10).toNat + 12) := hx.1
    have b : ¬ ((c.get 11).toNat ≤ x.toNat ∧ x.toNat < (c.get 11).toNat + (c.get 12).toNat) := hx.2.1
    have c' : ¬ ((c.get 2).toNat - 0x70 ≤ x.toNat ∧ x.toNat < (c.get 2).toNat) := hx.2.2
    exact M2o x b (by omega) (by omega)
  -- back to the loop head (decode error, or a frame of at most 2 bytes)
  have back : ∀ (d' : Core), d'.pc = 0x8001d476 → d'.sameCsr e2' → (∀ r : Reg, r ≠ 9 → r ≠ 10 → r ≠ 22 → d'.get r = e2'.get r) →
      d'.get 9 = s11 → d'.get 10 = 0 → LoopInv c R0 d' M2 ∧
        (d'.get 8).toNat - (d'.get 9).toNat < (d.get 8).toNat - (d.get 9).toNat := by
    intro d' a b c' f' g'
    have gd : ∀ r : Reg, r.val ∉ callerSaved → r ≠ 1 → r ≠ 9 → r ≠ 21 → r ≠ 22 → r ≠ 27 → d'.get r = d.get r :=
      fun r hr h1 h9 h21 h22 h27 => (c' r h9 (fun he => hr (by subst he; decide)) h22).trans (keepK r hr h1 h21 h27)
    refine ⟨loopInv_next c R0 hE d M h d' M2 a (b.trans cs2) ?_ ?_ ?_ ?_ slot2 ?_ ffil2 ?_ ram2, ?_⟩
    · intro r hr
      have : r.val ∉ callerSaved ∧ r ≠ 1 ∧ r ≠ 9 ∧ r ≠ 21 ∧ r ≠ 22 ∧ r ≠ 27 := by
        refine ⟨fun hm => ?_, ?_, ?_, ?_, ?_, ?_⟩
        · simp only [callerSaved, List.mem_cons, List.not_mem_nil, or_false] at hm hr; omega
        all_goals intro he; subst he; exact absurd hr (by decide)
      exact gd r this.1 this.2.1 this.2.2.1 this.2.2.2.1 this.2.2.2.2.1 this.2.2.2.2.2
    · rw [c' 23 (by decide) (by decide) (by decide), f23]; decide
    · rw [g', c' 23 (by decide) (by decide) (by decide), f23]
    · rw [f', hs11]; omega
    · rw [fcur2, f']
    · rw [fdisc2, h.fdisc, h0, c' 23 (by decide) (by decide) (by decide), f23]
    · rw [c' 8 (by decide) (by decide) (by decide), f8, f', hs11]; omega
  -- the Ok test
  let w0 := ramRead M2 (e2'.get 2 + 0x00000004#32) .w
  let w1 := ramRead M2 (e2'.get 2 + 0x00000008#32) .w
  by_cases hok : w0 = e2'.get 25
  · have wok : w0 = 0xffffffff#32 := hok.trans f25
    have hw1 : w1.toNat ≤ j := by
      have := P.ok (by show ramRead M2 (K.get 10) .w = _; rw [K10, ← f2]; exact wok)
      rw [show K.get 12 = K.get 12 from rfl, K12, K10, ng4] at this
      show (ramRead M2 (e2'.get 2 + 0x00000008#32) .w).toNat ≤ j; rw [f2]; exact this
    have t4ca : taken .ne w0 (e2'.get 25) = false := by simp [taken, hok]
    by_cases hshort : w1.toNat ≤ 2
    · -- a frame of at most 2 bytes: dropped
      have r3 := nshort e2' M2 pc2 q2 hal4 hin4 t4ca hal8 hin8
        (by rw [f26]; simp only [taken, BitVec.ult, decide_eq_false_iff_not]; show ¬ (2 < w1.toNat); omega) geu
      obtain ⟨li, me⟩ := back (nshortCore e2' M2) rfl (by unfold nshortCore; csr_chain)
        (fun r a b c' => by simp [nshortCore, Core.wr_get_ne, a, b, c'])
        (by simp [nshortCore, Core.wr_get_ne, Core.wr_get_self, alu_add, f27])
        (by simp [nshortCore, Core.wr_get_ne, Core.wr_get_self, alu_add])
      exact .inr ⟨_, _, _, (r1.trans rw2).trans r3, li, me⟩
    · -- Some(w1)
      have r3 := nsome e2' M2 pc2 q2 hal4 hin4 t4ca hal8 hin8
        (by rw [f26]; simp only [taken, BitVec.ult, decide_eq_true_eq]; show 2 < w1.toNat; omega)
      let e3 := nsomeCore e2' M2
      have cs3 : e3.sameCsr e2' := by unfold e3 nsomeCore; csr_chain
      have g3 : ∀ r : Reg, r ≠ 10 → r ≠ 22 → e3.get r = e2'.get r := fun r a b => by
        simp [e3, nsomeCore, Core.wr_get_ne, a, b]
      have e3_22 : e3.get 22 = w1 := by simp [e3, nsomeCore, Core.wr_get_ne, Core.wr_get_self, w1]
      have q3 : Quiet e3 := Quiet.of_sameCsr cs3 q2
      have hw1' : 2 < w1.toNat := by omega
      -- RetAt for both Some exits, from the RAM they leave
      have some_ret : ∀ (e' : Core) (M' : Word → BitVec 8), e'.pc = 0x8001d510 → e'.sameCsr e3 →
          (∀ r : Reg, r.val ∈ nkept → e'.get r = e3.get r) → e'.get 2 = e3.get 2 → e'.get 10 = 1#32 →
          e'.get 22 = w1 →
          (∀ x : Word, ¬ ((c.get 11).toNat ≤ x.toNat ∧ x.toNat < (c.get 11).toNat + (c.get 12).toNat) →
            ¬ ((c.get 2).toNat - 0x70 ≤ x.toNat ∧ x.toNat < (c.get 2).toNat - 0x40) → M' x = M2 x) →
          RetAt c R0 e' M' := by
        intro e' M' a b k' sp' t' v' mo
        have mo2 : ∀ x : Word, ¬ ((c.get 11).toNat ≤ x.toNat ∧ x.toNat < (c.get 11).toNat + (c.get 12).toNat) →
            ¬ ((c.get 2).toNat - 0x70 ≤ x.toNat ∧ x.toNat < (c.get 2).toNat) →
            (x.toNat < (c.get 10).toNat ∨ (c.get 10).toNat + 4 ≤ x.toNat) → M' x = M x :=
          fun x u v w => (mo x u (by omega)).trans (M2o x u (by omega) w)
        refine ⟨a, Quiet.of_sameCsr b q3, b.trans (cs3.trans cs2) |>.trans h.csr, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · rw [sp', g3 2 (by decide) (by decide), f2]
        · intro r hr
          have n10 : r ≠ 10 := fun he => by subst he; exact absurd hr (by decide)
          have n22 : r ≠ 22 := fun he => by subst he; exact absurd hr (by decide)
          have n1 : r ≠ 1 := fun he => by subst he; exact absurd hr (by decide)
          have n21 : r ≠ 21 := fun he => by subst he; exact absurd hr (by decide)
          have n27 : r ≠ 27 := fun he => by subst he; exact absurd hr (by decide)
          have ncs : r.val ∉ callerSaved := fun hm => by
            simp only [nkept, callerSaved, List.mem_cons, List.not_mem_nil, or_false] at hm hr; omega
          rw [k' r hr, g3 r n10 n22, keepK r ncs n1 n21 n27]
          exact h.kept r hr
        · intro o r hm
          rw [← h.slots o r hm]
          have ho : 0xc ≤ o ∧ o + 4 ≤ 0x40 := by
            simp only [nslots, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hm
            rcases hm with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ |
              ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> decide
          have eo' : (ng c + BitVec.ofNat 32 o).toNat = (ng c).toNat + o := add_toNat _ _ (by omega)
          exact rd_congr _ (by omega) fun x h1 h2 => (mo x (by omega) (by omega)).trans (slot2 x (by omega) (by omega))
        · rw [t']; decide
        · intro _; rw [v']
          refine ⟨by omega, by omega, ?_⟩
          show w1.toNat < (ramRead M' (c.get 10) .w).toNat
          rw [rd_congr (c.get 10) (by omega) (ram' := M') (ram := M2) fun x h1 h2 => mo x (by omega) (by omega),
            fcur2, hs11]
          omega
        · show (ramRead M' (c.get 10) .w).toNat ≤ (ramRead M' (c.get 10 + 4) .w).toNat ∧
            (ramRead M' (c.get 10 + 4) .w).toNat ≤ (c.get 12).toNat
          rw [rd_congr (c.get 10) (by omega) (ram' := M') (ram := M2) fun x h1 h2 => mo x (by omega) (by omega),
            fcur2, rd_congr (c.get 10 + 4) (by omega) (ram' := M') (ram := M) fun x h1 h2 => mo2 x (by omega) (by omega) (by omega),
            h.ffil, hs11]
          omega
        · show (M' (c.get 10 + 8)).toNat ≤ 1
          rw [mo2 _ (by omega) (by omega) (by omega), h.fdisc, h0]; decide
        · intro x hx
          have a1 : ¬ ((c.get 10).toNat ≤ x.toNat ∧ x.toNat < (c.get 10).toNat + 12) := hx.1
          have a2 : ¬ ((c.get 11).toNat ≤ x.toNat ∧ x.toNat < (c.get 11).toNat + (c.get 12).toNat) := hx.2.1
          have a3 : ¬ ((c.get 2).toNat - nextStack ≤ x.toNat ∧ x.toNat < (c.get 2).toNat) := hx.2.2
          rw [show nextStack = 0x70 from rfl] at a3
          rw [mo2 x a2 a3 (by omega)]; exact h.ram x hx
      by_cases hc0 : e3.get 9 = 0
      · -- the frame is already at the front
        have r4 := nfront e3 M2 rfl q3 (by simp [taken, hc0])
        left
        obtain ⟨k, m, r5, post⟩ := ret_post c R0 E (nfrontCore e3 M2) M2
          (some_ret _ _ rfl (by unfold nfrontCore; csr_chain)
            (fun r hr => by
              have n10 : r ≠ 10 := fun he => by subst he; exact absurd hr (by decide)
              simp [nfrontCore, Core.wr_get_ne, n10])
            (by simp [nfrontCore, Core.wr_get_ne]) (by simp [nfrontCore, Core.wr_get_self, alu_add]; try rfl)
            (by simp [nfrontCore, Core.wr_get_ne]; exact e3_22) (fun _ _ _ => rfl))
        exact ⟨_, m, (((r1.trans rw2).trans r3).trans r4).trans r5, post⟩
      · -- move the frame to the front: range check, memmove
        have e3_9 : e3.get 9 = d.get 9 := (g3 9 (by decide) (by decide)).trans f9
        have r4 := nmove1 e3 M2 rfl q3 (by simp only [taken, beq_eq_false_iff_ne]; exact hc0)
        let e5 := nmove1Core e3 M2
        have cs5 : e5.sameCsr e3 := by unfold e5 nmove1Core; csr_chain
        have e5_10 : e5.get 10 = d.get 9 := by simp [e5, nmove1Core, Core.wr_get_ne, Core.wr_get_self, alu_add, e3_9]
        have e5_11 : e5.get 11 = w1 + d.get 9 := by
          simp [e5, nmove1Core, Core.wr_get_ne, Core.wr_get_self, alu_add, e3_22, e3_9]
        have e5_12 : e5.get 12 = c.get 12 := by
          simp [e5, nmove1Core, Core.wr_get_ne, Core.wr_get_self, alu_add, g3 18 (by decide) (by decide), f18]
        have e5_1 : e5.get 1 = 0x8001d54a := by simp [e5, nmove1Core, Core.wr_get_self]
        have g5 : ∀ r : Reg, r ≠ 1 → r ≠ 10 → r ≠ 11 → r ≠ 12 → r ≠ 13 → e5.get r = e3.get r := fun r a b c' d' f' => by
          simp [e5, nmove1Core, Core.wr_get_ne, a, b, c', d', f']
        have q5 : Quiet e5 := Quiet.of_sameCsr cs5 q3
        have ew : (w1 + d.get 9).toNat = w1.toNat + (d.get 9).toNat := add_toNat' _ _ (by omega)
        have r5 := nmove2 e5 M2 rfl q5
          (by rw [e5_12, e5_11]; simp only [taken, BitVec.ult, decide_eq_false_iff_not]; rw [ew]; omega)
          (by rw [e5_11, e5_10]; simp only [taken, BitVec.ult, decide_eq_false_iff_not]; rw [ew]; omega)
          (by rw [e5_1]; decide)
        let e6 := nmove2Core e5 M2
        have cs6 : e6.sameCsr e5 := by unfold e6 nmove2Core; csr_chain
        have g6 : ∀ r : Reg, e6.get r = e5.get r := fun r => by simp [e6, nmove2Core]
        have q6 : Quiet e6 := Quiet.of_sameCsr cs6 q5
        have r6 := nmove3 e6 M2 (by simp [e6, nmove2Core, e5_1]) q6
        let K2 := nmove3Core e6 M2
        have csK2 : K2.sameCsr e6 := by unfold K2 nmove3Core; csr_chain
        have K2_10 : K2.get 10 = c.get 11 := by
          simp [K2, nmove3Core, Core.wr_get_ne, Core.wr_get_self, alu_add, g6, g5 20 (by decide) (by decide)
            (by decide) (by decide) (by decide), g3 20 (by decide) (by decide), f20]
        have K2_11 : K2.get 11 = c.get 11 + d.get 9 := by
          simp [K2, nmove3Core, Core.wr_get_ne, Core.wr_get_self, alu_add, g6, e5_10, g5 20 (by decide) (by decide)
            (by decide) (by decide) (by decide), g3 20 (by decide) (by decide), f20]
        have K2_12 : K2.get 12 = w1 := by
          simp [K2, nmove3Core, Core.wr_get_ne, Core.wr_get_self, alu_sub, g6, e5_10, e5_11]
          exact BitVec.add_sub_cancel _ _
        have K2_1 : K2.get 1 = 0x8001d55c := by simp [K2, nmove3Core, Core.wr_get_self]
        have gK2 : ∀ r : Reg, r ≠ 1 → r ≠ 10 → r ≠ 11 → r ≠ 12 → r ≠ 13 → K2.get r = e3.get r := fun r a b c' d' f' => by
          simp [K2, nmove3Core, Core.wr_get_ne, a, b, c', d', g6, g5 r a b c' d' f']
        have K2_2 : K2.get 2 = ng c := by
          rw [gK2 2 (by decide) (by decide) (by decide) (by decide) (by decide), g3 2 (by decide) (by decide), f2]
        have qK2 : Quiet K2 := Quiet.of_sameCsr csK2 q6
        have cenv : CopyEnv ⟨K2, M2⟩ := by
          refine ⟨rfl, qK2, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
          · show (K2.get 12).toNat ≤ bufLen; rw [K2_12, ← hlen]; omega
          · show B.inRam (K2.get 10) (K2.get 12).toNat = true; rw [K2_10, K2_12, B_ram]; omega
          · show B.inRam (K2.get 11) (K2.get 12).toNat = true; rw [K2_11, K2_12, B_ram, ed]; omega
          · show B.inRam (K2.get 2 - BitVec.ofNat 32 memmoveFrame) memmoveFrame = true
            rw [K2_2, B_ram, show memmoveFrame = 0x30 from rfl,
              BitVec.toNat_sub_of_le (BitVec.le_def.mpr (by simp; omega))]; simp; omega
          · show (K2.get 10).toNat + (K2.get 12).toNat ≤ (K2.get 2).toNat - memmoveFrame
            rw [K2_10, K2_12, K2_2, show memmoveFrame = 0x30 from rfl]; omega
          · show (K2.get 11).toNat + (K2.get 12).toNat ≤ (K2.get 2).toNat - memmoveFrame
            rw [K2_11, K2_12, K2_2, ed, show memmoveFrame = 0x30 from rfl]; omega
          · show (K2.get 1).getLsbD 0 = false; rw [K2_1]; decide
          · show (K2.get 2).toNat % 4 = 0; rw [K2_2]; have := E.spAl; unfold ng at eg ⊢; bv_omega
        obtain ⟨kc, ⟨e7, M3⟩, r7, CP⟩ := hC _ cenv
        have q7 : Quiet e7 := Quiet.of_sameCsr CP.csr qK2
        have pc7 : e7.pc = 0x8001d55c := CP.pc.trans K2_1
        have r8 := nmoved e7 M3 pc7 q7
        have Creg : ∀ r : Reg, r.val ∉ [5, 6, 7, 11, 12, 13, 14, 15, 16, 17, 28, 29, 30, 31] → e7.get r = K2.get r :=
          CP.regs
        have M3o : ∀ x : Word, ¬ ((c.get 11).toNat ≤ x.toNat ∧ x.toNat < (c.get 11).toNat + (c.get 12).toNat) →
            ¬ ((c.get 2).toNat - 0x70 ≤ x.toNat ∧ x.toNat < (c.get 2).toNat - 0x40) → M3 x = M2 x := by
          intro x a b
          have := CP.ram x (show ¬ ((K2.get 2).toNat - memmoveFrame ≤ x.toNat ∧ x.toNat < (K2.get 2).toNat) by
            rw [K2_2, show memmoveFrame = 0x30 from rfl]; omega)
          refine this.trans ?_
          show Memmove.moved M2 (K2.get 10) (K2.get 11) (K2.get 12).toNat x = M2 x
          rw [K2_10, K2_11, K2_12, Memmove.moved, if_neg (by omega)]
        left
        have cs8 : (nmovedCore e7 M3).sameCsr e3 :=
          ((by unfold nmovedCore; csr_chain : (nmovedCore e7 M3).sameCsr e7).trans CP.csr).trans
            (csK2.trans (cs6.trans cs5))
        have gk8 : ∀ r : Reg, r.val ∈ nkept → (nmovedCore e7 M3).get r = e3.get r := by
          intro r hr
          have n10 : r ≠ 10 := fun he => by subst he; exact absurd hr (by decide)
          rw [show (nmovedCore e7 M3).get r = e7.get r by simp [nmovedCore, Core.wr_get_ne, n10],
            Creg r (fun hm => by simp only [nkept, List.mem_cons, List.not_mem_nil, or_false] at hm hr; omega),
            gK2 r (fun he => by subst he; exact absurd hr (by decide)) n10 (fun he => by subst he; exact absurd hr (by decide))
              (fun he => by subst he; exact absurd hr (by decide)) (fun he => by subst he; exact absurd hr (by decide))]
        obtain ⟨k, m, r9, post⟩ := ret_post c R0 E (nmovedCore e7 M3) M3
          (some_ret _ _ rfl cs8 gk8
            (by rw [show (nmovedCore e7 M3).get 2 = e7.get 2 by simp [nmovedCore, Core.wr_get_ne], Creg 2 (by decide),
              K2_2, g3 2 (by decide) (by decide), f2])
            (by simp [nmovedCore, Core.wr_get_self, alu_add]; try rfl)
            (by rw [show (nmovedCore e7 M3).get 22 = e7.get 22 by simp [nmovedCore, Core.wr_get_ne], Creg 22 (by decide),
              gK2 22 (by decide) (by decide) (by decide) (by decide) (by decide), e3_22])
            M3o)
        exact ⟨_, m, ((((((((r1.trans rw2).trans r3).trans r4).trans r5).trans r6).trans r7).trans r8).trans r9), post⟩
  · -- a decode error: dropped
    have r3 := nerr e2' M2 pc2 q2 hal4 hin4 (by simp only [taken, bne_iff_ne, ne_eq]; exact hok) geu
    obtain ⟨li, me⟩ := back (nerrCore e2' M2) rfl (by unfold nerrCore; csr_chain)
      (fun r a b c' => by simp [nerrCore, Core.wr_get_ne, a, b])
      (by simp [nerrCore, Core.wr_get_ne, Core.wr_get_self, alu_add, f27])
      (by simp [nerrCore, Core.wr_get_ne, Core.wr_get_self, alu_add])
    exact .inr ⟨_, _, _, (r1.trans rw2).trans r3, li, me⟩

end E5R.Rmk.Deframer.Next
