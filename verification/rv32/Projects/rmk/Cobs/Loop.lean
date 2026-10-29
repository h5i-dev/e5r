/-
  `cobs::dec::decode_in_place_report`, the decode loop (0x8001e064..0x8001e0ea) and
  its two exits to 0x8001e102, refined to `Spec.run` over the original bytes.

  Original e5r code, Apache-2.0.
-/
import Projects.rmk.Cobs.Copy
import Projects.rmk.Cobs.Spec

set_option maxRecDepth 100000

namespace E5R.Rmk.Cobs
open E5R E5R.Rmk E5R.Rmk.CobsFetch

/-- The decode loop's state at a machine `⟨d, S⟩`, for the call from `⟨c, R⟩`:
    source index `src`, output so far `acc` (dst = acc.length), first zero `n`. -/
structure LInv (c : Core) (R : Word → BitVec 8) (n src : Nat) (acc : List Nat)
    (d : Core) (S : Word → BitVec 8) : Prop where
  csr : d.sameCsr c
  a0 : d.get 10 = c.get 10
  a1 : d.get 11 = c.get 11
  a2 : d.get 12 = c.get 12
  a4 : d.get 14 = BitVec.ofNat 32 n
  t4 : d.get 29 = BitVec.ofNat 32 src
  t2 : d.get 7 = BitVec.ofNat 32 acc.length
  a7 : d.get 17 = 2#32
  t0 : d.get 5 = 1#32 - c.get 12
  t1 : d.get 6 = 0xff#32
  a6 : d.get 16 = 4#32
  sp : d.get 2 = c.get 2 + 0xfffffff0#32
  ra : d.get 1 = c.get 1
  keep : ∀ r : Reg, r.val ∉ clobbered → r.val ∉ [2, 8, 9, 18, 19] → d.get r = c.get r
  bytes : ∀ j, j < (c.get 12).toNat →
    bufByte S (c.get 11) j = if h : j < acc.length then acc[j] else bufByte R (c.get 11) j
  outside : ∀ x : Word, ¬ ((c.get 11).toNat ≤ x.toNat ∧ x.toNat < (c.get 11).toNat + (c.get 12).toNat) →
    S x = saved c R x
  ord : acc.length ≤ src ∧ src ≤ n ∧ n ≤ (c.get 12).toNat

/-- A machine at the shared exit 0x8001e102 after the loop: a6 = 8, the tag in a1,
    dst in t2, the word at a0+4 already stored, the buffer described by `acc`. -/
structure ExitPrep (c : Core) (R : Word → BitVec 8) (tag w4 : Nat) (acc : List Nat)
    (e : Core) (S : Word → BitVec 8) : Prop where
  pc : e.pc = 0x8001e102
  csr : e.sameCsr c
  sp : e.get 2 = c.get 2 + 0xfffffff0#32
  ra : e.get 1 = c.get 1
  a0 : e.get 10 = c.get 10
  a6 : e.get 16 = 8#32
  a1 : e.get 11 = BitVec.ofNat 32 tag
  t2 : e.get 7 = BitVec.ofNat 32 acc.length
  keep : ∀ r : Reg, r.val ∉ clobbered → r.val ∉ [2, 8, 9, 18, 19] → e.get r = c.get r
  slots : SlotsHold c S
  outside : ∀ x : Word, ¬ ((c.get 10).toNat ≤ x.toNat ∧ x.toNat < (c.get 10).toNat + 12) →
    ¬ ((c.get 11).toNat ≤ x.toNat ∧ x.toNat < (c.get 11).toNat + (c.get 12).toNat) →
    ¬ ((c.get 2).toNat - 16 ≤ x.toNat ∧ x.toNat < (c.get 2).toNat) → S x = R x
  w4 : ramRead S (c.get 10 + 4#32) .w = BitVec.ofNat 32 w4
  bytes : ∀ j, j < (c.get 12).toNat →
    bufByte S (c.get 11) j = if h : j < acc.length then acc[j] else bufByte R (c.get 11) j

/-- 0x8001e0f0..0x8001e0f6: sw t4,4(a0) ; li a6,8 ; j 0x8001e102. -/
theorem at0f0 (d : Core) (S : Word → BitVec 8) (hpc : d.pc = 0x8001e0f0) (hq : Quiet d)
    (hA : (d.get 10 + 0x4#32).toNat % 4 = 0) (hR : B.inRam (d.get 10 + 0x4#32) 4 = true) :
    QRun B img 3 ⟨d, S⟩ ⟨((d.goto 0x8001e0f4).wr 16 (alu .add 0 0x8#32) 0x8001e0f6).goto 0x8001e102,
      ramWrite S (d.get 10 + 0x4#32) (d.get 29) .w⟩ := by
  let S1 := ramWrite S (d.get 10 + 0x4#32) (d.get 29) .w
  let d1 := d.goto 0x8001e0f4
  let d2 := d1.wr 16 (alu .add 0 0x8#32) 0x8001e0f6
  have s1 : DetStep B img ⟨d, S⟩ ⟨d1, S1⟩ := dstep_store f8001e0f0 hpc (by rw [exec_store, hpc]; rfl) hA hR
  have s2 : DetStep B img ⟨d1, S1⟩ ⟨d2, S1⟩ := dstep f8001e0f4 rfl (by rw [exec_opimm]; rfl)
  have s3 : DetStep B img ⟨d2, S1⟩ ⟨d2.goto 0x8001e102, S1⟩ :=
    dstep f8001e0f6 rfl (by
      rw [exec_jal, Core.set_zero]; exact jump_ok _ _ (by show (0x8001e102 : Word).getLsbD 0 = false; decide))
  exact .step hq s1 (.step (Quiet.of_sameCsr (Core.sameCsr_goto _ _) hq) s2
    (.single (Quiet.of_sameCsr ((Core.sameCsr_wr _ _ _ _).trans (Core.sameCsr_goto _ _)) hq) s3))

/-- The result slot's second word: aligned, in model RAM. -/
theorem out4 (c : Core) (R : Word → BitVec 8) (h : CobsEnv ⟨c, R⟩) :
    (c.get 10 + 0x4#32).toNat % 4 = 0 ∧ B.inRam (c.get 10 + 0x4#32) 4 = true := by
  have ho := h.out; have hoa := h.outAl
  rw [B_ram] at ho ⊢; simp only at ho hoa
  exact ⟨by bv_omega, by bv_omega, by bv_omega⟩

/-- From the loop state to the exit, writing t4 at a0+4 (0x8001e0f0). -/
theorem exit_from (c : Core) (R : Word → BitVec 8) (h : CobsEnv ⟨c, R⟩) (acc : List Nat)
    (d : Core) (S : Word → BitVec 8) (hpc : d.pc = 0x8001e0f0)
    (hcs : d.sameCsr c) (h10 : d.get 10 = c.get 10) (hsp : d.get 2 = c.get 2 + 0xfffffff0#32)
    (hra : d.get 1 = c.get 1)
    (hbytes : ∀ j, j < (c.get 12).toNat →
      bufByte S (c.get 11) j = if h : j < acc.length then acc[j] else bufByte R (c.get 11) j)
    (houts : ∀ x : Word, ¬ ((c.get 11).toNat ≤ x.toNat ∧ x.toNat < (c.get 11).toNat + (c.get 12).toNat) →
      S x = saved c R x)
    (tag w4 : Nat) (h11 : d.get 11 = BitVec.ofNat 32 tag) (h29 : d.get 29 = BitVec.ofNat 32 w4)
    (hkeep : ∀ r : Reg, r.val ∉ clobbered → r.val ∉ [2, 8, 9, 18, 19] → d.get r = c.get r)
    (h7 : d.get 7 = BitVec.ofNat 32 acc.length) :
    ∃ e S', QRun B img 3 ⟨d, S⟩ ⟨e, S'⟩ ∧ ExitPrep c R tag w4 acc e S' := by
  obtain ⟨hA, hR⟩ := out4 c R h
  have hq : Quiet d := Quiet.of_sameCsr hcs h.quiet
  rw [← h10] at hA hR
  refine ⟨_, _, at0f0 d S hpc hq hA hR, ?_⟩
  have hf := h.frame; have ho := h.out; have hb := h.buf; have hof := h.outFrame; have hob := h.outBuf
  rw [B_ram] at hf ho hb
  simp only at hf ho hb hof hob
  have esp : (c.get 2 - 16).toNat = (c.get 2).toNat - 16 := by bv_omega
  have W : ∀ b : Word, b.toNat + 4 ≤ 2 ^ 32 →
      (b.toNat + 4 ≤ (c.get 10).toNat + 4 ∨ (c.get 10).toNat + 8 ≤ b.toNat) →
      ramRead (ramWrite S (d.get 10 + 0x4#32) (d.get 29) .w) b .w = ramRead S b .w := by
    intro b hb1 hb2; rw [h10]; rw [ramRead_w_out] <;> bv_omega
  have hsl := saved_hold c R h.frame
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (Core.sameCsr_goto _ _).trans ((Core.sameCsr_wr _ _ _ _).trans ((Core.sameCsr_goto _ _).trans hcs))
  · simp [Core.wr_get_ne, hsp]
  · simp [Core.wr_get_ne, hra]
  · simp [Core.wr_get_ne, h10]
  · simp [Core.wr_get_self, alu]
  · simp [Core.wr_get_ne, h11]
  · simp [Core.wr_get_ne, h7]
  · intro r hr hr'
    have r16 : r ≠ 16 := fun e => hr (by subst e; decide)
    simp only [Core.goto_get, Core.wr_get_ne _ _ _ _ _ r16]; exact hkeep r hr hr'
  · -- the saved registers: the slots lie outside the buffer and the result slot
    have hbf := h.bufFrame; simp only at hbf
    have sl : ∀ off : Word, (off = 0x0#32 ∨ off = 0x4#32 ∨ off = 0x8#32 ∨ off = 0xc#32) →
        ramRead (ramWrite S (d.get 10 + 0x4#32) (d.get 29) .w) (c.get 2 + 0xfffffff0#32 + off) .w =
          ramRead (saved c R) (c.get 2 + 0xfffffff0#32 + off) .w := by
      intro off hoff
      rw [W _ (by rcases hoff with rfl | rfl | rfl | rfl <;> bv_omega)
        (by rcases hoff with rfl | rfl | rfl | rfl <;> bv_omega)]
      apply ramRead_w_congr
      intro k hk
      apply houts
      rcases hoff with rfl | rfl | rfl | rfl <;> bv_omega
    obtain ⟨s8, s9, s18, s19⟩ := hsl
    exact ⟨(sl _ (by simp)).trans s8, (sl _ (by simp)).trans s9, (sl _ (by simp)).trans s18,
      (sl _ (by simp)).trans s19⟩
  · intro x xo xb xf
    rw [h10, ramWrite_w_out _ _ _ _ (by bv_omega) (by bv_omega), houts x xb, saved_out c R h.frame x xf]
  · rw [h10, ramRead_ramWrite_w, h29]
  · intro j hj
    unfold bufByte
    rw [h10, ramWrite_w_out _ _ _ _ (by bv_omega) (by bv_omega)]
    exact hbytes j hj

/-! ## Comparisons of small indices -/

theorem ult_small (a b : Nat) (ha : a < 2 ^ 32) (hb : b < 2 ^ 32) :
    (BitVec.ofNat 32 a).ult (BitVec.ofNat 32 b) = decide (a < b) := by
  simp [BitVec.ult, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]

theorem len_small (c : Core) (R : Word → BitVec 8) (h : CobsEnv ⟨c, R⟩) : (c.get 12).toNat ≤ 488 := h.len

/-- LInv with registers changed only where it does not look. -/
theorem LInv.goto {c R n src acc d S} (hi : LInv c R n src acc d S) (p : Word) :
    LInv c R n src acc (d.goto p) S :=
  ⟨(Core.sameCsr_goto _ _).trans hi.csr, hi.a0, hi.a1, hi.a2, hi.a4, hi.t4, hi.t2, hi.a7, hi.t0, hi.t1, hi.a6,
    hi.sp, hi.ra, hi.keep, hi.bytes, hi.outside, hi.ord⟩

theorem LInv.wr {c R n src acc d S} (hi : LInv c R n src acc d S) (rd : Reg) (v p : Word)
    (hrd : rd.val ∈ [8, 9, 13, 15, 18, 19, 28, 30, 31]) : LInv c R n src acc (d.wr rd v p) S := by
  have ne : ∀ k, k ∉ [8, 9, 13, 15, 18, 19, 28, 30, 31] → ∀ r : Reg, r.val = k → r ≠ rd :=
    fun k hk r hr e => hk (by rw [← hr, e]; exact hrd)
  have g := fun (r : Reg) (k : Nat) (hr : r.val = k) (hk : k ∉ [8, 9, 13, 15, 18, 19, 28, 30, 31]) =>
    Core.wr_get_ne d rd r v p (ne k hk r hr)
  refine ⟨(Core.sameCsr_wr _ _ _ _).trans hi.csr, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    hi.bytes, hi.outside, hi.ord⟩
  · rw [g 10 10 rfl (by decide)]; exact hi.a0
  · rw [g 11 11 rfl (by decide)]; exact hi.a1
  · rw [g 12 12 rfl (by decide)]; exact hi.a2
  · rw [g 14 14 rfl (by decide)]; exact hi.a4
  · rw [g 29 29 rfl (by decide)]; exact hi.t4
  · rw [g 7 7 rfl (by decide)]; exact hi.t2
  · rw [g 17 17 rfl (by decide)]; exact hi.a7
  · rw [g 5 5 rfl (by decide)]; exact hi.t0
  · rw [g 6 6 rfl (by decide)]; exact hi.t1
  · rw [g 16 16 rfl (by decide)]; exact hi.a6
  · rw [g 2 2 rfl (by decide)]; exact hi.sp
  · rw [g 1 1 rfl (by decide)]; exact hi.ra
  · intro r hr hr'
    rw [Core.wr_get_ne]; exact hi.keep r hr hr'
    intro e; subst e
    simp only [clobbered, List.mem_cons, List.not_mem_nil, or_false] at hr hr' hrd
    omega

/-- 0x8001e064 with src ≥ n: bgeu t4,a4 → 0x8001e0ee ; li a1,0 ; then the success exit. -/
theorem G_exit (c : Core) (R : Word → BitVec 8) (h : CobsEnv ⟨c, R⟩) (n src : Nat) (acc : List Nat)
    (d : Core) (S : Word → BitVec 8) (hi : LInv c R n src acc d S) (hpc : d.pc = 0x8001e064) (hs : n ≤ src) :
    ∃ k e S', QRun B img k ⟨d, S⟩ ⟨e, S'⟩ ∧ ExitPrep c R 0 n acc e S' := by
  have hl := h.len; have ord := hi.ord
  have hq : Quiet d := Quiet.of_sameCsr hi.csr h.quiet
  have tk : taken .geu (d.get 29) (d.get 14) = true := by
    simp only [taken, hi.t4, hi.a4, ult_small src n (by omega) (by omega)]; simp; omega
  let d1 := d.goto 0x8001e0ee
  let d2 := d1.wr 11 (alu .add (d1.get 0) 0x0#32) 0x8001e0f0
  have s1 : DetStep B img ⟨d, S⟩ ⟨d1, S⟩ := dstep f8001e064 hpc (by
    rw [exec_branch, if_pos tk, hpc]; exact jump_ok _ _ (by show (0x8001e0ee : Word).getLsbD 0 = false; decide))
  have s2 : DetStep B img ⟨d1, S⟩ ⟨d2, S⟩ := dstep f8001e0ee rfl (by rw [exec_opimm]; rfl)
  have k2 : d2.sameCsr c := (Core.sameCsr_wr _ _ _ _).trans ((Core.sameCsr_goto _ _).trans hi.csr)
  have g2 : ∀ r : Reg, r ≠ 11 → d2.get r = d.get r := fun r hr => by simp [d2, d1, Core.wr_get_ne, hr]
  obtain ⟨e, S', hr, hx⟩ := exit_from c R h acc d2 S rfl k2
    (by rw [g2 10 (by decide)]; exact hi.a0) (by rw [g2 2 (by decide)]; exact hi.sp)
    (by rw [g2 1 (by decide)]; exact hi.ra) hi.bytes hi.outside 0 n
    (by simp [d2, Core.wr_get_self, alu])
    (by rw [g2 29 (by decide), hi.t4]; congr 1; omega)
    (fun r hr hr' => by
      have : r ≠ 11 := fun e => hr (by subst e; decide)
      rw [g2 r this]; exact hi.keep r hr hr')
    (by rw [g2 7 (by decide)]; exact hi.t2)
  exact ⟨_, e, S', .step hq s1 (.step (Quiet.of_sameCsr ((Core.sameCsr_goto _ _).trans hi.csr) h.quiet) s2 hr), hx⟩

end E5R.Rmk.Cobs
