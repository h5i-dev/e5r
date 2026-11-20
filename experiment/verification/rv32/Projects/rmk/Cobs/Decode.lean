/-
  **`cobs::dec::decode_in_place_report` (pinned RMK image, 0x8001e02e): the whole
  function.** Original e5r code, Apache-2.0.

  `decode`: from every machine meeting `CobsEnv` (a0 = 12-byte result slot, a1 = buffer,
  a2 = len ≤ 488, a 16-byte frame below sp; all in model RAM, aligned and pairwise
  disjoint; a quiet core; an even return address) a quiet deterministic run returns to
  ra and meets
    * `Returns`: sp, ra, s0-s11, gp, tp and CSRs as at entry; RAM unchanged outside the
      result slot, the buffer and the frame;
    * `Res`: the result words and the decoded buffer, as functions of the ORIGINAL
      buffer bytes alone (`Spec.run` on `bufByte R buf`, the first zero `firstZero`).
  A run of the model that returns is the model's only behaviour from that machine, so
  neither panic site (0x8001e12a, 0x8001e140: `panic_bounds_check`) is reached, every
  store lands in the result slot, the buffer or the frame, and the outcome does not
  depend on any RAM byte outside the buffer (the bound on reads, up to the frame's own
  save/restore).
-/
import Projects.rmk.Cobs.Loop
import Projects.rmk.Cobs.Empty

set_option maxRecDepth 100000

namespace E5R.Rmk.Cobs
open E5R E5R.Rmk E5R.Rmk.CobsFetch

theorem firstZero_congr (f g : Nat → Nat) (len : Nat) (hfg : ∀ j, j < len → f j = g j) :
    ∀ k i, i + k = len → firstZero f i len = firstZero g i len
  | 0, i, h => by rw [firstZero_eq f i, firstZero_eq g i, if_neg (by omega), if_neg (by omega)]
  | k + 1, i, h => by
    rw [firstZero_eq f i, firstZero_eq g i]
    simp only [show i < len from by omega, if_true, hfg i (by omega), firstZero_congr f g len hfg k (i + 1) (by omega)]

/-- The result: words of the slot and the decoded buffer, from the original bytes. -/
def Res (m₀ m : Machine) : Prop :=
  let a0 := m₀.core.get 10
  let buf := m₀.core.get 11
  let len := (m₀.core.get 12).toNat
  let orig := bufByte m₀.ram buf
  let n := firstZero orig 0 len
  let r := run orig n (n + 1) 0 []
  (len = 0 → ramRead m.ram a0 .w = 1 ∧ ramRead m.ram (a0 + 4) .w = 0) ∧
  (0 < len →
    ramRead m.ram a0 .w = (if r.1 = .ok then 0 else 1) ∧
    ramRead m.ram (a0 + 4) .w = BitVec.ofNat 32 (if r.1 = .ok then n else 1) ∧
    ramRead m.ram (a0 + 8) .w = BitVec.ofNat 32 r.2.length ∧
    ∀ j, j < len → bufByte m.ram buf j = if h : j < r.2.length then r.2[j] else orig j)

/-- From the loop's exit state to the caller, with the result words and buffer. -/
theorem fromExit (c : Core) (R : Word → BitVec 8) (h : CobsEnv ⟨c, R⟩) (tag w4 : Nat) (acc : List Nat)
    (e : Core) (S : Word → BitVec 8) (hx : ExitPrep c R tag w4 acc e S) :
    ∃ m, QRun B img 9 ⟨e, S⟩ m ∧ Returns ⟨c, R⟩ m ∧
      ramRead m.ram (c.get 10) .w = BitVec.ofNat 32 tag ∧
      ramRead m.ram (c.get 10 + 4) .w = BitVec.ofNat 32 w4 ∧
      ramRead m.ram (c.get 10 + 8) .w = BitVec.ofNat 32 acc.length ∧
      ∀ j, j < (c.get 12).toNat →
        bufByte m.ram (c.get 11) j = if h : j < acc.length then acc[j] else bufByte R (c.get 11) j := by
  obtain ⟨m, hr, hret, r0, r8, -, r4, hm⟩ := finish c R S e h hx.pc (Quiet.of_sameCsr hx.csr h.quiet) hx.csr
    hx.sp hx.ra hx.a0 (Or.inr hx.a6) hx.keep hx.slots hx.outside
  have ho := h.out; have hb := h.buf; have hob := h.outBuf
  rw [B_ram] at ho hb; simp only at ho hb hob
  refine ⟨m, hr, hret, by rw [r0, hx.a1], ?_, ?_, fun j hj => ?_⟩
  · show ramRead m.ram (c.get 10 + 4#32) .w = _
    rw [r4 hx.a6, hx.w4]
  · show ramRead m.ram (c.get 10 + 8#32) .w = _
    rw [← hx.a6, r8, hx.t2]
  unfold bufByte
  rw [hm _ (by simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega)]
  exact hx.bytes j hj

theorem bufByte_saved (c : Core) (R : Word → BitVec 8) (h : CobsEnv ⟨c, R⟩) (j : Nat)
    (hj : j < (c.get 12).toNat) : bufByte (saved c R) (c.get 11) j = bufByte R (c.get 11) j := by
  have hb := h.buf; have hbf := h.bufFrame; have hf := h.frame
  rw [B_ram] at hb hf; simp only at hb hbf hf
  unfold bufByte
  rw [saved_out c R h.frame _ (by
    have : (c.get 2 - 16).toNat = (c.get 2).toNat - 16 := by bv_omega
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega)]

/-- **The decoder's contract.** -/
theorem decode (m₀ : Machine) (h : CobsEnv m₀) : ∃ k m, QRun B img k m₀ m ∧ Returns m₀ m ∧ Res m₀ m := by
  obtain ⟨c, R⟩ := m₀
  by_cases hz : (c.get 12).toNat = 0
  · obtain ⟨k, m, hr, hret, w0, w4⟩ := empty ⟨c, R⟩ h hz
    exact ⟨k, m, hr, hret, fun _ => ⟨w0, w4⟩, fun hp => absurd hp (by simp only; omega)⟩
  have hl := h.len
  have hb := h.buf; rw [B_ram] at hb; simp only at hb hl hz
  let len := (c.get 12).toNat
  let orig := bufByte R (c.get 11)
  let S0 := saved c R
  have q := fun (x : Core) (hx : x.sameCsr c) => Quiet.of_sameCsr hx h.quiet
  have hpro := prologue c R h.pc h.quiet h.frame h.spAl
  -- 0x8001e03a: len ≠ 0; 0x8001e03c: li a4,0
  let e0 := pro c
  have nt : ¬ (taken .eq (e0.get 12) (e0.get 0) = true) := by
    simp only [taken, e0, pro_get c 12 (by decide) (by decide), Core.get_zero, beq_iff_eq]
    intro e; apply hz; rw [e]; rfl
  let e1 := e0.goto 0x8001e03c
  let e2 := e1.wr 14 (alu .add (e1.get 0) 0x0#32) 0x8001e03e
  have p1 : DetStep B img ⟨e0, S0⟩ ⟨e1, S0⟩ := dstep f8001e03a rfl (by rw [exec_branch, if_neg nt]; rfl)
  have p2 : DetStep B img ⟨e1, S0⟩ ⟨e2, S0⟩ := dstep f8001e03c rfl (by rw [exec_opimm]; rfl)
  have k0 : e0.sameCsr c := pro_sameCsr c
  have k2 : e2.sameCsr c := (Core.sameCsr_wr _ _ _ _).trans ((Core.sameCsr_goto _ _).trans k0)
  have g2 : ∀ r : Reg, r ≠ 2 → r ≠ 14 → r ≠ 16 → e2.get r = c.get r := fun r a b c' => by
    simp only [e2, e1, Core.wr_get_ne _ _ _ _ _ b, Core.goto_get]; exact pro_get c r a c'
  -- the scan
  obtain ⟨ns, e3, hr3, hpc3, h14, hcs3, hg3⟩ :=
    scan (c.get 11) len (by rw [B_ram]; exact hb) (len - 1) e2 S0 rfl (q _ k2)
      (g2 11 (by decide) (by decide) (by decide)) (by rw [g2 12 (by decide) (by decide) (by decide)])
      (by simp [e2, Core.wr_get_self, alu]; omega)
  have he2 : (e2.get 14).toNat = 0 := by simp [e2, Core.wr_get_self, alu]
  let n := firstZero orig 0 len
  have hn : (e3.get 14).toNat = n := by
    rw [h14, he2]; exact firstZero_congr _ _ len (fun j hj => bufByte_saved c R h j hj) len 0 (by omega)
  obtain ⟨-, hnl, -, -⟩ := firstZero_spec orig len len 0 (by omega)
  have k3 : e3.sameCsr c := hcs3.trans k2
  have g3 : ∀ r : Reg, r ≠ 2 → r ≠ 13 → r ≠ 14 → r ≠ 16 → e3.get r = c.get r := fun r a b c' d' => by
    rw [hg3 r b c']; exact g2 r a c' d'
  -- 0x8001e050: li t4,0 ; li t2,0 ; beqz a4
  let e4 := e3.wr 29 (alu .add (e3.get 0) 0x0#32) 0x8001e052
  let e5 := e4.wr 7 (alu .add (e4.get 0) 0x0#32) 0x8001e054
  have p4 : DetStep B img ⟨e3, S0⟩ ⟨e4, S0⟩ := dstep f8001e050 hpc3 (by rw [exec_opimm, hpc3]; rfl)
  have p5 : DetStep B img ⟨e4, S0⟩ ⟨e5, S0⟩ := dstep f8001e052 rfl (by rw [exec_opimm]; rfl)
  have k5 : e5.sameCsr c := (Core.sameCsr_wr _ _ _ _).trans ((Core.sameCsr_wr _ _ _ _).trans k3)
  have e5_14 : e5.get 14 = BitVec.ofNat 32 n := by
    rw [show e5.get 14 = e3.get 14 by simp [e5, e4, Core.wr_get_ne], ← hn, ofNat_toNat]
  have run5 : QRun B img _ ⟨c, R⟩ ⟨e5, S0⟩ :=
    (hpro.trans (.step (q _ k0) p1 (.single (q _ ((Core.sameCsr_goto _ _).trans k0)) p2))).trans
      (hr3.trans (.step (q _ k3) p4 (.single (q _ ((Core.sameCsr_wr _ _ _ _).trans k3)) p5)))
  have g5 : ∀ r : Reg, r ≠ 2 → r ≠ 7 → r ≠ 13 → r ≠ 14 → r ≠ 16 → r ≠ 29 → e5.get r = c.get r :=
    fun r a b c' d' e' f' => by
      simp only [e5, e4, Core.wr_get_ne _ _ _ _ _ b, Core.wr_get_ne _ _ _ _ _ f']; exact g3 r a c' d' e'
  -- the run of the loop, whichever way it starts
  have fin : ∃ k e S', QRun B img k ⟨c, R⟩ ⟨e, S'⟩ ∧ Final c R n (run orig n (n + 1) 0 []) e S' := by
    by_cases n0 : n = 0
    · -- beqz taken → 0x8001e0ee ; li a1,0 ; the success exit with nothing decoded
      have tk : taken .eq (e5.get 14) (e5.get 0) = true := by rw [e5_14, n0]; simp [taken]
      let e6 := e5.goto 0x8001e0ee
      let e7 := e6.wr 11 (alu .add (e6.get 0) 0x0#32) 0x8001e0f0
      have p6 : DetStep B img ⟨e5, S0⟩ ⟨e6, S0⟩ := dstep f8001e054 rfl (by
        rw [exec_branch, if_pos tk]; exact jump_lit _ 0x8001e054 _ 0x8001e0ee rfl (by decide) (by decide))
      have p7 : DetStep B img ⟨e6, S0⟩ ⟨e7, S0⟩ := dstep f8001e0ee rfl (by rw [exec_opimm]; rfl)
      have k7 : e7.sameCsr c := (Core.sameCsr_wr _ _ _ _).trans ((Core.sameCsr_goto _ _).trans k5)
      have g7 : ∀ r : Reg, r ≠ 11 → e7.get r = e5.get r := fun r a => by simp [e7, e6, Core.wr_get_ne, a]
      obtain ⟨e, S', hr, hx⟩ := exit_from c R h [] e7 S0 rfl k7
        (by rw [g7 10 (by decide), g5 10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)])
        (by rw [g7 2 (by decide)]; simp [e5, e4, Core.wr_get_ne]; rw [hg3 2 (by decide) (by decide)]
            simp [e2, e1, Core.wr_get_ne]; exact pro_sp c)
        (by rw [g7 1 (by decide), g5 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)])
        (fun j hj => by rw [dif_neg (by simp)]; exact bufByte_saved c R h j hj) (fun _ _ => rfl) 0 0
        (by simp [e7, Core.wr_get_self, alu]) (by rw [g7 29 (by decide)]; simp [e5, e4, Core.wr_get_ne, Core.wr_get_self, alu])
        (fun r hr hr' => by
          have a : r ≠ 11 := fun e => hr (by subst e; decide)
          rw [g7 r a]
          exact g5 r (fun e => hr' (by subst e; decide)) (fun e => hr (by subst e; decide))
            (fun e => hr (by subst e; decide)) (fun e => hr (by subst e; decide)) (fun e => hr (by subst e; decide))
            (fun e => hr (by subst e; decide)))
        (by rw [g7 7 (by decide)]; simp [e5, Core.wr_get_self, alu])
      refine ⟨_, e, S', run5.trans (.step (q _ k5) p6 (.step (q _ ((Core.sameCsr_goto _ _).trans k5)) p7 hr)), ?_⟩
      rw [run_done _ _ _ _ _ (by omega)]; simp only [Final]; rw [n0]; exact hx
    · -- beqz not taken; 0x8001e056..0x8001e062: a3 = 1, a7 = 2, t0 = 1 - len, t1 = 0xff, j 0x8001e068
      have nt6 : ¬ (taken .eq (e5.get 14) (e5.get 0) = true) := by
        rw [e5_14]; simp only [taken, Core.get_zero, beq_iff_eq]
        intro e; have := congrArg BitVec.toNat e; simp at this; omega
      let e6 := e5.goto 0x8001e056
      let e7 := e6.wr 13 (alu .add (e6.get 0) 0x1#32) 0x8001e058
      let e8 := e7.wr 17 (alu .add (e7.get 0) 0x2#32) 0x8001e05a
      let e9 := e8.wr 5 (alu .sub (e8.get 13) (e8.get 12)) 0x8001e05e
      let e10 := e9.wr 6 (alu .add (e9.get 0) 0xff#32) 0x8001e062
      let e11 := e10.goto 0x8001e068
      have p6 : DetStep B img ⟨e5, S0⟩ ⟨e6, S0⟩ := dstep f8001e054 rfl (by rw [exec_branch, if_neg nt6]; rfl)
      have p7 : DetStep B img ⟨e6, S0⟩ ⟨e7, S0⟩ := dstep f8001e056 rfl (by rw [exec_opimm]; rfl)
      have p8 : DetStep B img ⟨e7, S0⟩ ⟨e8, S0⟩ := dstep f8001e058 rfl (by rw [exec_opimm]; rfl)
      have p9 : DetStep B img ⟨e8, S0⟩ ⟨e9, S0⟩ := dstep f8001e05a rfl (by rw [exec_op]; rfl)
      have p10 : DetStep B img ⟨e9, S0⟩ ⟨e10, S0⟩ := dstep f8001e05e rfl (by rw [exec_opimm]; rfl)
      have p11 : DetStep B img ⟨e10, S0⟩ ⟨e11, S0⟩ := dstep f8001e062 rfl (by
        rw [exec_jal, Core.set_zero]; exact jump_lit _ 0x8001e062 _ 0x8001e068 rfl (by decide) (by decide))
      have k6 : e6.sameCsr c := (Core.sameCsr_goto _ _).trans k5
      have k7 : e7.sameCsr c := (Core.sameCsr_wr _ _ _ _).trans k6
      have k8 : e8.sameCsr c := (Core.sameCsr_wr _ _ _ _).trans k7
      have k9 : e9.sameCsr c := (Core.sameCsr_wr _ _ _ _).trans k8
      have k10 : e10.sameCsr c := (Core.sameCsr_wr _ _ _ _).trans k9
      have k11 : e11.sameCsr c := (Core.sameCsr_goto _ _).trans k10
      have g11 : ∀ r : Reg, r ≠ 5 → r ≠ 6 → r ≠ 13 → r ≠ 17 → e11.get r = e5.get r := fun r a b c' d' => by
        simp [e11, e10, e9, e8, e7, e6, Core.wr_get_ne, a, b, c', d']
      have g11' : ∀ r : Reg, r.val ∉ [5, 6, 13, 17] → e11.get r = e5.get r := fun r hr =>
        g11 r (fun e => hr (by subst e; decide)) (fun e => hr (by subst e; decide))
          (fun e => hr (by subst e; decide)) (fun e => hr (by subst e; decide))
      have g5' : ∀ r : Reg, r.val ∉ [2, 7, 13, 14, 16, 29] → e5.get r = c.get r := fun r hr =>
        g5 r (fun e => hr (by subst e; decide)) (fun e => hr (by subst e; decide))
          (fun e => hr (by subst e; decide)) (fun e => hr (by subst e; decide))
          (fun e => hr (by subst e; decide)) (fun e => hr (by subst e; decide))
      have e5r : ∀ r : Reg, r.val ∉ [2, 5, 6, 7, 13, 14, 16, 17, 29] → e11.get r = c.get r := fun r hr => by
        rw [g11' r (fun e => hr (by simp only [List.mem_cons, List.not_mem_nil, or_false] at e ⊢; omega)),
          g5' r (fun e => hr (by simp only [List.mem_cons, List.not_mem_nil, or_false] at e ⊢; omega))]
      have e5_2 : e5.get 2 = c.get 2 + 0xfffffff0#32 := by
        simp only [e5, e4, Core.wr_get_ne _ _ _ _ _ (show (2 : Reg) ≠ 7 by decide),
          Core.wr_get_ne _ _ _ _ _ (show (2 : Reg) ≠ 29 by decide)]
        rw [hg3 2 (by decide) (by decide)]
        simp only [e2, e1, Core.wr_get_ne _ _ _ _ _ (show (2 : Reg) ≠ 14 by decide), Core.goto_get]; exact pro_sp c
      have e5_16 : e5.get 16 = 4#32 := by
        simp only [e5, e4, Core.wr_get_ne _ _ _ _ _ (show (16 : Reg) ≠ 7 by decide),
          Core.wr_get_ne _ _ _ _ _ (show (16 : Reg) ≠ 29 by decide)]
        rw [hg3 16 (by decide) (by decide)]
        simp only [e2, e1, Core.wr_get_ne _ _ _ _ _ (show (16 : Reg) ≠ 14 by decide), Core.goto_get]; exact pro_a6 c
      have hi : LInv c R n 0 [] e11 S0 := by
        have e8_12 : e8.get 12 = c.get 12 := by
          simp only [e8, e7, e6, Core.wr_get_ne _ _ _ _ _ (show (12 : Reg) ≠ 17 by decide),
            Core.wr_get_ne _ _ _ _ _ (show (12 : Reg) ≠ 13 by decide), Core.goto_get]
          exact g5' 12 (by decide)
        have e8_13 : e8.get 13 = 1#32 := by simp [e8, e7, Core.wr_get_ne, Core.wr_get_self, alu]
        refine ⟨k11, e5r 10 (by decide), e5r 11 (by decide), e5r 12 (by decide), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
          e5r 1 (by decide), ?_, ?_, fun _ _ => rfl, ⟨Nat.le_refl _, Nat.zero_le _, hnl⟩⟩
        · rw [g11' 14 (by decide)]; exact e5_14
        · rw [g11' 29 (by decide)]; simp [e5, e4, Core.wr_get_ne, Core.wr_get_self, alu]
        · rw [g11' 7 (by decide)]; simp [e5, Core.wr_get_self, alu]
        · simp [e11, e10, e9, e8, Core.wr_get_ne, Core.wr_get_self, alu]
        · have : e11.get 5 = e8.get 13 - e8.get 12 := by
            simp [e11, e10, e9, Core.wr_get_ne, Core.wr_get_self, alu]
          rw [this, e8_13, e8_12]
        · simp [e11, e10, Core.wr_get_self, alu]
        · rw [g11' 16 (by decide)]; exact e5_16
        · rw [g11' 2 (by decide)]; exact e5_2
        · intro r hr hr'
          apply e5r r
          simp only [clobbered, List.mem_cons, List.not_mem_nil, or_false] at hr hr' ⊢
          omega
        · intro j hj; rw [dif_neg (by simp)]; exact bufByte_saved c R h j hj
      have run11 : QRun B img _ ⟨c, R⟩ ⟨e11, S0⟩ :=
        run5.trans (.step (q _ k5) p6 (.step (q _ k6) p7 (.step (q _ k7) p8 (.step (q _ k8) p9
          (.step (q _ k9) p10 (.single (q _ k10) p11))))))
      obtain ⟨k, e, S', hr, hx⟩ := loop c R h n (n + 1) 0 [] e11 S0 hi rfl (by omega) (by omega)
      exact ⟨_, e, S', run11.trans hr, hx⟩
  obtain ⟨k, e, S', hr, hx⟩ := fin
  unfold Final at hx
  have unf : (run orig n (n + 1) 0 []) = run (bufByte R (c.get 11)) (firstZero (bufByte R (c.get 11)) 0 (c.get 12).toNat)
      (firstZero (bufByte R (c.get 11)) 0 (c.get 12).toNat + 1) 0 [] := rfl
  cases hres : (run orig n (n + 1) 0 []).1 with
  | ok =>
    rw [hres] at hx
    obtain ⟨m, hm, hret, r0, r4, r8, hb'⟩ := fromExit c R h 0 n _ e S' hx
    refine ⟨_, m, hr.trans hm, hret, fun hp => absurd hp hz, fun _ => ?_⟩
    rw [unf] at hres
    refine ⟨?_, ?_, r8, hb'⟩
    · show _ = (if _ then _ else _); rw [r0, hres, if_pos rfl]; rfl
    · show _ = BitVec.ofNat 32 (if _ then _ else _); rw [r4, hres, if_pos rfl]
  | invalid =>
    rw [hres] at hx
    obtain ⟨m, hm, hret, r0, r4, r8, hb'⟩ := fromExit c R h 1 1 _ e S' hx
    refine ⟨_, m, hr.trans hm, hret, fun hp => absurd hp hz, fun _ => ?_⟩
    rw [unf] at hres
    refine ⟨?_, ?_, r8, hb'⟩
    · show _ = (if _ then _ else _); rw [r0, hres, if_neg (by decide)]; rfl
    · show _ = BitVec.ofNat 32 (if _ then _ else _); rw [r4, hres, if_neg (by decide)]

end E5R.Rmk.Cobs
