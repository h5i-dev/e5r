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

/-- A jump to `pc + off` from a core whose pc is the literal `pc`, landing at the literal `t`. -/
theorem jump_lit (c : Core) (pc off t : Word) (hpc : c.pc = pc) (ht : pc + off = t) (h : t.getLsbD 0 = false) :
    jump c (c.pc + off) = .done (c.goto t) := by
  rw [hpc, ht]; exact jump_ok _ _ h

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

/-- 0x8001e064 with src < n: falls through to the loop head 0x8001e068. -/
theorem G_cont (c : Core) (R : Word → BitVec 8) (h : CobsEnv ⟨c, R⟩) (n src : Nat) (acc : List Nat)
    (d : Core) (S : Word → BitVec 8) (hi : LInv c R n src acc d S) (hpc : d.pc = 0x8001e064) (hs : src < n) :
    QRun B img 1 ⟨d, S⟩ ⟨d.goto 0x8001e068, S⟩ := by
  have hl := h.len; have ord := hi.ord
  have nt : ¬ (taken .geu (d.get 29) (d.get 14) = true) := by
    simp only [taken, hi.t4, hi.a4, ult_small src n (by omega) (by omega)]; simp; omega
  exact .single (Quiet.of_sameCsr hi.csr h.quiet) (dstep f8001e064 hpc (by rw [exec_branch, if_neg nt, hpc]; rfl))

/-- 0x8001e116: li t4,1 ; li a1,1 ; j 0x8001e0f0 ; then the exit: invalid frame. -/
theorem invalid_exit (c : Core) (R : Word → BitVec 8) (h : CobsEnv ⟨c, R⟩) (n src : Nat) (acc : List Nat)
    (d : Core) (S : Word → BitVec 8) (hi : LInv c R n src acc d S) (hpc : d.pc = 0x8001e116) :
    ∃ k e S', QRun B img k ⟨d, S⟩ ⟨e, S'⟩ ∧ ExitPrep c R 1 1 acc e S' := by
  let d1 := d.wr 29 (alu .add (d.get 0) 0x1#32) 0x8001e118
  let d2 := d1.wr 11 (alu .add (d1.get 0) 0x1#32) 0x8001e11a
  let d3 := d2.goto 0x8001e0f0
  have s1 : DetStep B img ⟨d, S⟩ ⟨d1, S⟩ := dstep f8001e116 hpc (by rw [exec_opimm, hpc]; rfl)
  have s2 : DetStep B img ⟨d1, S⟩ ⟨d2, S⟩ := dstep f8001e118 rfl (by rw [exec_opimm]; rfl)
  have s3 : DetStep B img ⟨d2, S⟩ ⟨d3, S⟩ := dstep f8001e11a rfl (by
    rw [exec_jal, Core.set_zero]; exact jump_lit _ 0x8001e11a _ 0x8001e0f0 rfl (by decide) (by decide))
  have k1 : d1.sameCsr c := (Core.sameCsr_wr _ _ _ _).trans hi.csr
  have k2 : d2.sameCsr c := (Core.sameCsr_wr _ _ _ _).trans k1
  have k3 : d3.sameCsr c := (Core.sameCsr_goto _ _).trans k2
  have g3 : ∀ r : Reg, r ≠ 11 → r ≠ 29 → d3.get r = d.get r := fun r a b => by
    simp [d3, d2, d1, Core.wr_get_ne, a, b]
  obtain ⟨e, S', hr, hx⟩ := exit_from c R h acc d3 S rfl k3
    (by rw [g3 10 (by decide) (by decide)]; exact hi.a0) (by rw [g3 2 (by decide) (by decide)]; exact hi.sp)
    (by rw [g3 1 (by decide) (by decide)]; exact hi.ra) hi.bytes hi.outside 1 1
    (by simp [d3, d2, Core.wr_get_self, alu]) (by simp [d3, d2, d1, Core.wr_get_ne, Core.wr_get_self, alu])
    (fun r hr hr' => by
      have a : r ≠ 11 := fun e => hr (by subst e; decide)
      have b : r ≠ 29 := fun e => hr (by subst e; decide)
      rw [g3 r a b]; exact hi.keep r hr hr')
    (by rw [g3 7 (by decide) (by decide)]; exact hi.t2)
  have q := fun (x : Core) (hx : x.sameCsr c) => Quiet.of_sameCsr hx h.quiet
  exact ⟨_, e, S', .step (q _ hi.csr) s1 (.step (q _ k1) s2 (.step (q _ k2) s3 hr)), hx⟩

/-- The tail 0x8001e0d8 with src < n: append a zero (dst < src) and go to the loop head. -/
theorem tail_cont (c : Core) (R : Word → BitVec 8) (h : CobsEnv ⟨c, R⟩) (n src : Nat) (acc : List Nat)
    (d : Core) (S : Word → BitVec 8) (hi : LInv c R n src acc d S) (hpc : d.pc = 0x8001e0d8)
    (hs : src < n) (hd : acc.length < src) :
    ∃ k e S', QRun B img k ⟨d, S⟩ ⟨e, S'⟩ ∧ e.pc = 0x8001e068 ∧ LInv c R n src (acc ++ [0]) e S' := by
  have hl := h.len; have ord := hi.ord
  have hb := h.buf; rw [B_ram] at hb; simp only at hb
  have hb' : 0x80029bc8 ≤ (c.get 11).toNat ∧ (c.get 11).toNat + (c.get 12).toNat ≤ 0x81000000 := hb
  let d1 := d.goto 0x8001e0dc
  let d2 := d1.goto 0x8001e0e0
  let d3 := d2.wr 13 (alu .add (d2.get 11) (d2.get 7)) 0x8001e0e4
  let d4 := d3.goto 0x8001e0e8
  let S1 := ramWrite S (d3.get 13 + 0x0#32) (d3.get 0) .b
  let d5 := d4.wr 7 (alu .add (d4.get 7) 0x1#32) 0x8001e0ea
  let d6 := d5.goto 0x8001e068
  have nt1 : ¬ (taken .geu (d.get 29) (d.get 14) = true) := by
    simp only [taken, hi.t4, hi.a4, ult_small src n (by omega) (by omega)]; simp; omega
  have nt2 : ¬ (taken .geu (d1.get 7) (d1.get 12) = true) := by
    simp only [taken, d1, Core.goto_get, hi.t2, hi.a2]
    rw [← ofNat_toNat (c.get 12), ult_small _ _ (by omega) (by omega)]; simp; omega
  have v3 : d3.get 13 = c.get 11 + BitVec.ofNat 32 acc.length := by
    simp [d3, d2, d1, Core.wr_get_self, alu, hi.a1, hi.t2]
  have hS1 : S1 = ramPut S (c.get 11 + BitVec.ofNat 32 acc.length) 0#8 := by
    simp only [S1, ramWrite, v3, BitVec.add_zero, Core.get_zero]; rfl
  have s1 : DetStep B img ⟨d, S⟩ ⟨d1, S⟩ := dstep f8001e0d8 hpc (by rw [exec_branch, if_neg nt1, hpc]; rfl)
  have s2 : DetStep B img ⟨d1, S⟩ ⟨d2, S⟩ := dstep f8001e0dc rfl (by rw [exec_branch, if_neg nt2]; rfl)
  have s3 : DetStep B img ⟨d2, S⟩ ⟨d3, S⟩ := dstep f8001e0e0 rfl (by rw [exec_op]; rfl)
  have s4 : DetStep B img ⟨d3, S⟩ ⟨d4, S1⟩ :=
    dstep_store f8001e0e4 rfl (exec_store _ _ _ _ _ _) (Nat.mod_one _)
      (by show B.inRam _ 1 = true; rw [v3, BitVec.add_zero]; exact buf_inRam _ _ _ hb' (by omega))
  have s5 : DetStep B img ⟨d4, S1⟩ ⟨d5, S1⟩ := dstep f8001e0e8 rfl (by rw [exec_opimm]; rfl)
  have t6 : taken .ltu (d5.get 29) (d5.get 14) = true := by
    simp only [taken, d5, d4, d3, d2, d1, Core.wr_get_ne _ _ _ _ _ (show (29 : Reg) ≠ 7 by decide),
      Core.wr_get_ne _ _ _ _ _ (show (29 : Reg) ≠ 13 by decide),
      Core.wr_get_ne _ _ _ _ _ (show (14 : Reg) ≠ 7 by decide),
      Core.wr_get_ne _ _ _ _ _ (show (14 : Reg) ≠ 13 by decide), Core.goto_get, hi.t4, hi.a4,
      ult_small src n (by omega) (by omega)]
    simp; omega
  have s6 : DetStep B img ⟨d5, S1⟩ ⟨d6, S1⟩ := dstep f8001e0ea rfl (by
    rw [exec_branch, if_pos t6]; exact jump_lit _ 0x8001e0ea _ 0x8001e068 rfl (by decide) (by decide))
  have k1 : d1.sameCsr c := (Core.sameCsr_goto _ _).trans hi.csr
  have k2 : d2.sameCsr c := (Core.sameCsr_goto _ _).trans k1
  have k3 : d3.sameCsr c := (Core.sameCsr_wr _ _ _ _).trans k2
  have k4 : d4.sameCsr c := (Core.sameCsr_goto _ _).trans k3
  have k5 : d5.sameCsr c := (Core.sameCsr_wr _ _ _ _).trans k4
  have k6 : d6.sameCsr c := (Core.sameCsr_goto _ _).trans k5
  have q := fun (x : Core) (hx : x.sameCsr c) => Quiet.of_sameCsr hx h.quiet
  have g6 : ∀ r : Reg, r ≠ 7 → r ≠ 13 → d6.get r = d.get r := fun r a b => by
    simp [d6, d5, d4, d3, d2, d1, Core.wr_get_ne, a, b]
  refine ⟨_, d6, S1, .step (q _ hi.csr) s1 (.step (q _ k1) s2 (.step (q _ k2) s3 (.step (q _ k3) s4
    (.step (q _ k4) s5 (.single (q _ k5) s6))))), rfl, ⟨k6, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_⟩⟩
  · rw [g6 10 (by decide) (by decide)]; exact hi.a0
  · rw [g6 11 (by decide) (by decide)]; exact hi.a1
  · rw [g6 12 (by decide) (by decide)]; exact hi.a2
  · rw [g6 14 (by decide) (by decide)]; exact hi.a4
  · rw [g6 29 (by decide) (by decide)]; exact hi.t4
  · simp only [d6, d5, Core.goto_get, Core.wr_get_self _ (7 : Reg) _ _ (by decide), alu, List.length_append,
      List.length_singleton]
    rw [show d4.get 7 = d.get 7 by simp [d4, d3, d2, d1, Core.wr_get_ne], hi.t2]
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  · rw [g6 17 (by decide) (by decide)]; exact hi.a7
  · rw [g6 5 (by decide) (by decide)]; exact hi.t0
  · rw [g6 6 (by decide) (by decide)]; exact hi.t1
  · rw [g6 16 (by decide) (by decide)]; exact hi.a6
  · rw [g6 2 (by decide) (by decide)]; exact hi.sp
  · rw [g6 1 (by decide) (by decide)]; exact hi.ra
  · intro r hr hr'
    have a : r ≠ 7 := fun e => hr (by subst e; decide)
    have b : r ≠ 13 := fun e => hr (by subst e; decide)
    rw [g6 r a b]; exact hi.keep r hr hr'
  · intro j hj
    rw [hS1]
    by_cases e : j = acc.length
    · subst e; rw [put_same]; simp
    · rw [put_other S _ _ _ j _ hb' (by omega) hj e, hi.bytes j hj]
      by_cases hj' : j < acc.length
      · rw [dif_pos hj', dif_pos (by simp; omega), List.getElem_append_left hj']
      · rw [dif_neg hj', dif_neg (by simp; omega)]
  · intro x hx; rw [hS1, put_outside S _ _ _ _ x hb' (by omega) hx]; exact hi.outside x hx
  · simp only [List.length_append, List.length_singleton]; omega

/-- The tail 0x8001e0d8 with src ≥ n: bgeu → 0x8001e064, then the success exit. -/
theorem tail_exit (c : Core) (R : Word → BitVec 8) (h : CobsEnv ⟨c, R⟩) (n src : Nat) (acc : List Nat)
    (d : Core) (S : Word → BitVec 8) (hi : LInv c R n src acc d S) (hpc : d.pc = 0x8001e0d8) (hs : n ≤ src) :
    ∃ k e S', QRun B img k ⟨d, S⟩ ⟨e, S'⟩ ∧ ExitPrep c R 0 n acc e S' := by
  have hl := h.len; have ord := hi.ord
  have tk : taken .geu (d.get 29) (d.get 14) = true := by
    simp only [taken, hi.t4, hi.a4, ult_small src n (by omega) (by omega)]; simp; omega
  have s : DetStep B img ⟨d, S⟩ ⟨d.goto 0x8001e064, S⟩ := dstep f8001e0d8 hpc (by
    rw [exec_branch, if_pos tk, hpc]; exact jump_ok _ _ (by show (0x8001e064 : Word).getLsbD 0 = false; decide))
  obtain ⟨k, e, S', hr, hx⟩ := G_exit c R h n src acc _ S (hi.goto _) rfl hs
  exact ⟨_, e, S', .step (Quiet.of_sameCsr hi.csr h.quiet) s hr, hx⟩

/-- Re-establish the invariant after the loop changed src (t4), dst (t2), scratch registers
    and buffer bytes. -/
theorem LInv.mk' {c R n src acc d S} (hi : LInv c R n src acc d S) (d' : Core) (S' : Word → BitVec 8)
    (src' : Nat) (acc' : List Nat) (hcs : d'.sameCsr c)
    (hreg : ∀ r : Reg, r.val ∉ [7, 8, 9, 13, 15, 18, 19, 28, 29, 30, 31] → d'.get r = d.get r)
    (h29 : d'.get 29 = BitVec.ofNat 32 src') (h7 : d'.get 7 = BitVec.ofNat 32 acc'.length)
    (hbytes : ∀ j, j < (c.get 12).toNat →
      bufByte S' (c.get 11) j = if h : j < acc'.length then acc'[j] else bufByte R (c.get 11) j)
    (hout : ∀ x : Word, ¬ ((c.get 11).toNat ≤ x.toNat ∧ x.toNat < (c.get 11).toNat + (c.get 12).toNat) →
      S' x = S x)
    (hord : acc'.length ≤ src' ∧ src' ≤ n) : LInv c R n src' acc' d' S' := by
  refine ⟨hcs, ?_, ?_, ?_, ?_, h29, h7, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hbytes, fun x hx => (hout x hx).trans (hi.outside x hx),
    ⟨hord.1, hord.2, hi.ord.2.2⟩⟩
  · rw [hreg 10 (by decide)]; exact hi.a0
  · rw [hreg 11 (by decide)]; exact hi.a1
  · rw [hreg 12 (by decide)]; exact hi.a2
  · rw [hreg 14 (by decide)]; exact hi.a4
  · rw [hreg 17 (by decide)]; exact hi.a7
  · rw [hreg 5 (by decide)]; exact hi.t0
  · rw [hreg 6 (by decide)]; exact hi.t1
  · rw [hreg 16 (by decide)]; exact hi.a6
  · rw [hreg 2 (by decide)]; exact hi.sp
  · rw [hreg 1 (by decide)]; exact hi.ra
  · intro r hr hr'
    rw [hreg r (by
      intro hm; simp only [clobbered, List.mem_cons, List.not_mem_nil, or_false] at hr hr' hm; omega)]
    exact hi.keep r hr hr'

/-- The original buffer byte, as the loop reads it at index `src ≥ dst`. -/
theorem read_orig {c R n src acc d S} (hi : LInv c R n src acc d S) (hs : src < n) :
    bufByte S (c.get 11) src = bufByte R (c.get 11) src := by
  rw [hi.bytes src (by have := hi.ord; omega), dif_neg (by have := hi.ord; omega)]

/-- 0x8001e068..0x8001e078: the bounds check (never taken), the code byte, and the
    invalid-frame test. -/
theorem head (c : Core) (R : Word → BitVec 8) (h : CobsEnv ⟨c, R⟩) (n src : Nat) (acc : List Nat)
    (d : Core) (S : Word → BitVec 8) (hi : LInv c R n src acc d S) (hpc : d.pc = 0x8001e068) (hs : src < n) :
    (n < src + bufByte R (c.get 11) src → ∃ k e S', QRun B img k ⟨d, S⟩ ⟨e, S'⟩ ∧ ExitPrep c R 1 1 acc e S') ∧
    (src + bufByte R (c.get 11) src ≤ n → ∃ d', QRun B img 5 ⟨d, S⟩ ⟨d', S⟩ ∧ d'.pc = 0x8001e07c ∧
      LInv c R n src acc d' S ∧ d'.get 28 = BitVec.ofNat 32 (bufByte R (c.get 11) src) ∧
      d'.get 19 = c.get 11 + BitVec.ofNat 32 src ∧
      d'.get 15 = BitVec.ofNat 32 (src + bufByte R (c.get 11) src)) := by
  have hl := h.len; have ord := hi.ord
  have hb := h.buf; rw [B_ram] at hb; simp only at hb
  have hb' : 0x80029bc8 ≤ (c.get 11).toNat ∧ (c.get 11).toNat + (c.get 12).toNat ≤ 0x81000000 := hb
  have hcode : bufByte R (c.get 11) src < 256 := (R _).isLt
  let code := bufByte R (c.get 11) src
  have q := fun (x : Core) (hx : x.sameCsr c) => Quiet.of_sameCsr hx h.quiet
  let d1 := d.goto 0x8001e06c
  let d2 := d1.wr 19 (alu .add (d1.get 11) (d1.get 29)) 0x8001e070
  let d3 := d2.wr 28 (extend .b false (ramRead S (d2.get 19 + 0x0#32) .b)) 0x8001e074
  let d4 := d3.wr 15 (alu .add (d3.get 29) (d3.get 28)) 0x8001e078
  have nt : ¬ (taken .geu (d.get 29) (d.get 12) = true) := by
    simp only [taken, hi.t4, hi.a2]; rw [← ofNat_toNat (c.get 12), ult_small _ _ (by omega) (by omega)]; simp; omega
  have v2 : d2.get 19 = c.get 11 + BitVec.ofNat 32 src := by simp [d2, d1, Core.wr_get_self, alu, hi.a1, hi.t4]
  have v3 : d3.get 28 = BitVec.ofNat 32 code := by
    simp only [d3, Core.wr_get_self _ (28 : Reg) _ _ (by decide), v2, BitVec.add_zero, lbu_val]
    show BitVec.ofNat 32 (bufByte S (c.get 11) src) = _
    rw [read_orig hi hs]
  have v4 : d4.get 15 = BitVec.ofNat 32 (src + code) := by
    have e29 : d3.get 29 = BitVec.ofNat 32 src := by simp [d3, d2, d1, Core.wr_get_ne, hi.t4]
    have : d4.get 15 = d3.get 29 + d3.get 28 := by simp [d4, Core.wr_get_self, alu]
    rw [this, e29, v3]
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have s1 : DetStep B img ⟨d, S⟩ ⟨d1, S⟩ := dstep f8001e068 hpc (by rw [exec_branch, if_neg nt, hpc]; rfl)
  have s2 : DetStep B img ⟨d1, S⟩ ⟨d2, S⟩ := dstep f8001e06c rfl (by rw [exec_op]; rfl)
  have s3 : DetStep B img ⟨d2, S⟩ ⟨d3, S⟩ :=
    dstep_load f8001e070 rfl (exec_load _ _ _ _ _ _ _) (Nat.mod_one _)
      (by show B.inRam _ 1 = true; rw [v2, BitVec.add_zero]; exact buf_inRam _ _ _ hb' (by omega)) rfl
  have s4 : DetStep B img ⟨d3, S⟩ ⟨d4, S⟩ := dstep f8001e074 rfl (by rw [exec_op]; rfl)
  have i4 : LInv c R n src acc d4 S :=
    ((((hi.goto _).wr 19 _ _ (by decide)).wr 28 _ _ (by decide)).wr 15 _ _ (by decide))
  have h14 : d4.get 14 = BitVec.ofNat 32 n := i4.a4
  have run4 : QRun B img 4 ⟨d, S⟩ ⟨d4, S⟩ :=
    .step (q _ hi.csr) s1 (.step (q _ (hi.goto _).csr) s2 (.step (q _ ((hi.goto _).wr 19 _ _ (by decide)).csr) s3
      (.single (q _ (((hi.goto _).wr 19 _ _ (by decide)).wr 28 _ _ (by decide)).csr) s4)))
  constructor
  · intro hbad
    have tk : taken .ltu (d4.get 14) (d4.get 15) = true := by
      rw [h14, v4]; simp only [taken, ult_small n (src + code) (by omega) (by omega)]; simp; omega
    have s5 : DetStep B img ⟨d4, S⟩ ⟨d4.goto 0x8001e116, S⟩ := dstep f8001e078 rfl (by
      rw [exec_branch, if_pos tk]; exact jump_lit _ 0x8001e078 _ 0x8001e116 rfl (by decide) (by decide))
    obtain ⟨k, e, S', hr, hx⟩ := invalid_exit c R h n src acc _ S (i4.goto _) rfl
    exact ⟨_, e, S', run4.trans (.step (q _ i4.csr) s5 hr), hx⟩
  · intro hok
    have nt5 : ¬ (taken .ltu (d4.get 14) (d4.get 15) = true) := by
      rw [h14, v4]; simp only [taken, ult_small n (src + code) (by omega) (by omega)]; simp; omega
    have s5 : DetStep B img ⟨d4, S⟩ ⟨d4.goto 0x8001e07c, S⟩ := dstep f8001e078 rfl (by
      rw [exec_branch, if_neg nt5]; rfl)
    refine ⟨d4.goto 0x8001e07c, run4.trans (.single (q _ i4.csr) s5), rfl, i4.goto _, ?_, ?_, ?_⟩
    · simp only [Core.goto_get, d4, Core.wr_get_ne _ _ _ _ _ (show (28 : Reg) ≠ 15 by decide)]; exact v3
    · simp only [Core.goto_get, d4, d3, Core.wr_get_ne _ _ _ _ _ (show (19 : Reg) ≠ 15 by decide),
        Core.wr_get_ne _ _ _ _ _ (show (19 : Reg) ≠ 28 by decide)]; exact v2
    · simp only [Core.goto_get]; exact v4

theorem block_small {orig : Nat → Nat} {n src : Nat} (h1 : src + orig src ≤ n) (h2 : orig src < 2) :
    block orig n src = some ((if src + 1 < n then [0] else []), src + 1) := by
  unfold block; simp only; rw [if_neg (by omega), if_pos h2]

theorem block_big {orig : Nat → Nat} {n src : Nat} (h1 : src + orig src ≤ n) (h2 : 2 ≤ orig src) :
    block orig n src = some ((List.range (orig src - 1)).map (fun i => orig (src + 1 + i)) ++
      (if orig src ≠ 0xff ∧ src + orig src < n then [0] else []), src + orig src) := by
  unfold block; simp only; rw [if_neg (by omega), if_neg (by omega)]

theorem block_none {orig : Nat → Nat} {n src : Nat} (h1 : n < src + orig src) : block orig n src = none := by
  unfold block; simp only; rw [if_pos h1]

/-- What one iteration from the loop head achieves, against `block`. -/
def IterOK (c : Core) (R : Word → BitVec 8) (n src : Nat) (acc : List Nat) (d : Core) (S : Word → BitVec 8) :
    Prop :=
  match block (bufByte R (c.get 11)) n src with
  | none => ∃ k e S', QRun B img k ⟨d, S⟩ ⟨e, S'⟩ ∧ ExitPrep c R 1 1 acc e S'
  | some (out, src') =>
    (n ≤ src' → ∃ k e S', QRun B img k ⟨d, S⟩ ⟨e, S'⟩ ∧ ExitPrep c R 0 n (acc ++ out) e S') ∧
    (src' < n → ∃ k e S', QRun B img k ⟨d, S⟩ ⟨e, S'⟩ ∧ e.pc = 0x8001e068 ∧ LInv c R n src' (acc ++ out) e S')

/-- code < 2 (0x8001e07c → 0x8001e0d2 → 0x8001e0d8): src += 1, then the tail. -/
theorem small (c : Core) (R : Word → BitVec 8) (h : CobsEnv ⟨c, R⟩) (n src : Nat) (acc : List Nat)
    (d : Core) (S : Word → BitVec 8) (hi : LInv c R n src acc d S) (hpc : d.pc = 0x8001e07c) (hs : src < n)
    (h28 : d.get 28 = BitVec.ofNat 32 (bufByte R (c.get 11) src)) (hc : bufByte R (c.get 11) src < 2) :
    (n ≤ src + 1 → ∃ k e S', QRun B img k ⟨d, S⟩ ⟨e, S'⟩ ∧ ExitPrep c R 0 n acc e S') ∧
    (src + 1 < n → ∃ k e S', QRun B img k ⟨d, S⟩ ⟨e, S'⟩ ∧ e.pc = 0x8001e068 ∧ LInv c R n (src + 1) (acc ++ [0]) e S') := by
  have hl := h.len; have ord := hi.ord
  have q := fun (x : Core) (hx : x.sameCsr c) => Quiet.of_sameCsr hx h.quiet
  have tk : taken .ltu (d.get 28) (d.get 17) = true := by
    rw [h28, hi.a7]; simp only [taken]
    rw [show (2#32 : Word) = BitVec.ofNat 32 2 from rfl,
      ult_small (bufByte R (c.get 11) src) 2 (by omega) (by omega)]; simp; omega
  let d1 := d.goto 0x8001e0d2
  let d2 := d1.wr 29 (alu .add (d1.get 29) 0x1#32) 0x8001e0d4
  have nt : ¬ (taken .eq (d2.get 28) (d2.get 6) = true) := by
    have : d2.get 28 = d.get 28 := by simp [d2, d1, Core.wr_get_ne]
    have e6 : d2.get 6 = d.get 6 := by simp [d2, d1, Core.wr_get_ne]
    rw [this, e6, h28, hi.t1]; simp only [taken, beq_iff_eq]
    intro e; have := congrArg BitVec.toNat e; simp at this; omega
  let d3 := d2.goto 0x8001e0d8
  have s1 : DetStep B img ⟨d, S⟩ ⟨d1, S⟩ := dstep f8001e07c hpc (by
    rw [exec_branch, if_pos tk]; exact jump_lit _ 0x8001e07c _ 0x8001e0d2 hpc (by decide) (by decide))
  have s2 : DetStep B img ⟨d1, S⟩ ⟨d2, S⟩ := dstep f8001e0d2 rfl (by rw [exec_opimm]; rfl)
  have s3 : DetStep B img ⟨d2, S⟩ ⟨d3, S⟩ := dstep f8001e0d4 rfl (by rw [exec_branch, if_neg nt]; rfl)
  have k3 : d3.sameCsr c :=
    (Core.sameCsr_goto _ _).trans ((Core.sameCsr_wr _ _ _ _).trans ((Core.sameCsr_goto _ _).trans hi.csr))
  have i3 : LInv c R n (src + 1) acc d3 S := hi.mk' d3 S (src + 1) acc k3
    (fun r hr => by
      have : r ≠ 29 := fun e => hr (by subst e; decide)
      simp [d3, d2, d1, Core.wr_get_ne, this])
    (by
      simp only [d3, d2, Core.goto_get, Core.wr_get_self _ (29 : Reg) _ _ (by decide), alu, d1, hi.t4]
      apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega)
    (by simp [d3, d2, d1, Core.wr_get_ne, hi.t2]) hi.bytes (fun _ _ => rfl) ⟨by omega, by omega⟩
  have run3 : QRun B img 3 ⟨d, S⟩ ⟨d3, S⟩ :=
    .step (q _ hi.csr) s1 (.step (q _ ((Core.sameCsr_goto _ _).trans hi.csr)) s2
      (.single (q _ ((Core.sameCsr_wr _ _ _ _).trans ((Core.sameCsr_goto _ _).trans hi.csr))) s3))
  constructor
  · intro hn
    obtain ⟨k, e, S', hr, hx⟩ := tail_exit c R h n (src + 1) acc d3 S i3 rfl hn
    exact ⟨_, e, S', run3.trans hr, hx⟩
  · intro hn
    obtain ⟨k, e, S', hr, hpc', hx⟩ := tail_cont c R h n (src + 1) acc d3 S i3 rfl hn (by omega)
    exact ⟨_, e, S', run3.trans hr, hpc', hx⟩

/-- 0x8001e082..0x8001e090: t6 := (len - dst) masked by (len < len - dst ? 0 : ~0), i.e. len - dst. -/
theorem t6_val (len dst : Nat) (h : dst ≤ len) (hl : len < 2 ^ 32) :
    (alu .and (alu .add (alu .sltu (BitVec.ofNat 32 len) (alu .sub (BitVec.ofNat 32 len) (BitVec.ofNat 32 dst)))
      0xffffffff#32) (alu .sub (BitVec.ofNat 32 len) (BitVec.ofNat 32 dst))) = BitVec.ofNat 32 (len - dst) := by
  have e : BitVec.ofNat 32 len - BitVec.ofNat 32 dst = BitVec.ofNat 32 (len - dst) := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  have nlt : ¬ ((BitVec.ofNat 32 len).ult (BitVec.ofNat 32 (len - dst)) = true) := by
    rw [ult_small _ _ hl (by omega)]; simp
  simp only [alu, e, if_neg nlt]
  rw [show (0 : Word) + 0xffffffff#32 = BitVec.allOnes 32 from by decide, BitVec.allOnes_and]

theorem zext_val (x : Nat) : (BitVec.ofNat 32 x) &&& 0xff#32 = BitVec.ofNat 32 (x % 256) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_and, BitVec.toNat_ofNat]
  rw [show (255 : Nat) % 2 ^ 32 = 2 ^ 8 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  omega

/-- code ≥ 2 (0x8001e07c → setup → copy → 0x8001e0c6..0x8001e0cc): `code - 1` bytes moved, then
    the tail (code ≠ 0xff) or 0x8001e064 (code = 0xff). -/
theorem big (c : Core) (R : Word → BitVec 8) (h : CobsEnv ⟨c, R⟩) (n src : Nat) (acc : List Nat)
    (d : Core) (S : Word → BitVec 8) (hi : LInv c R n src acc d S) (hpc : d.pc = 0x8001e07c) (hs : src < n)
    (h28 : d.get 28 = BitVec.ofNat 32 (bufByte R (c.get 11) src))
    (h19 : d.get 19 = c.get 11 + BitVec.ofNat 32 src)
    (h15 : d.get 15 = BitVec.ofNat 32 (src + bufByte R (c.get 11) src))
    (hc : 2 ≤ bufByte R (c.get 11) src) (hok : src + bufByte R (c.get 11) src ≤ n) :
    let code := bufByte R (c.get 11) src
    let data := (List.range (code - 1)).map (fun i => bufByte R (c.get 11) (src + 1 + i))
    (n ≤ src + code → ∃ k e S', QRun B img k ⟨d, S⟩ ⟨e, S'⟩ ∧ ExitPrep c R 0 n (acc ++ data) e S') ∧
    (src + code < n → ∃ k e S', QRun B img k ⟨d, S⟩ ⟨e, S'⟩ ∧ e.pc = 0x8001e068 ∧
      LInv c R n (src + code) (acc ++ data ++ (if code ≠ 0xff then [0] else [])) e S') := by
  intro code data
  have hl := h.len; have ord := hi.ord
  have hb := h.buf; rw [B_ram] at hb; simp only at hb
  have hb' : 0x80029bc8 ≤ (c.get 11).toNat ∧ (c.get 11).toNat + (c.get 12).toNat ≤ 0x81000000 := hb
  have hcode : code < 256 := (R _).isLt
  have q := fun (x : Core) (hx : x.sameCsr c) => Quiet.of_sameCsr hx h.quiet
  have hlen : c.get 12 = BitVec.ofNat 32 (c.get 12).toNat := (ofNat_toNat _).symm
  -- 0x8001e07c: code ≥ 2, fall through to the copy setup
  have nt : ¬ (taken .ltu (d.get 28) (d.get 17) = true) := by
    rw [h28, hi.a7]; simp only [taken]
    rw [show (2#32 : Word) = BitVec.ofNat 32 2 from rfl, ult_small code 2 (by omega) (by omega)]; simp; omega
  let b0 := d.goto 0x8001e080
  let b1 := b0.wr 13 (alu .add (b0.get 0) 0x0#32) 0x8001e082
  let b2 := b1.wr 31 (alu .sub (b1.get 12) (b1.get 7)) 0x8001e086
  let b3 := b2.wr 30 (alu .add (b2.get 5) (b2.get 29)) 0x8001e08a
  let b4 := b3.wr 8 (alu .sltu (b3.get 12) (b3.get 31)) 0x8001e08e
  let b5 := b4.wr 8 (alu .add (b4.get 8) 0xffffffff#32) 0x8001e090
  let b6 := b5.wr 31 (alu .and (b5.get 8) (b5.get 31)) 0x8001e094
  let b7 := b6.wr 18 (alu .add (b6.get 11) (b6.get 7)) 0x8001e098
  let b8 := b7.wr 8 (alu .and (b7.get 15) 0xff#32) 0x8001e09c
  have s0 : DetStep B img ⟨d, S⟩ ⟨b0, S⟩ := dstep f8001e07c hpc (by rw [exec_branch, if_neg nt, hpc]; rfl)
  have s1 : DetStep B img ⟨b0, S⟩ ⟨b1, S⟩ := dstep f8001e080 rfl (by rw [exec_opimm]; rfl)
  have s2 : DetStep B img ⟨b1, S⟩ ⟨b2, S⟩ := dstep f8001e082 rfl (by rw [exec_op]; rfl)
  have s3 : DetStep B img ⟨b2, S⟩ ⟨b3, S⟩ := dstep f8001e086 rfl (by rw [exec_op]; rfl)
  have s4 : DetStep B img ⟨b3, S⟩ ⟨b4, S⟩ := dstep f8001e08a rfl (by rw [exec_op]; rfl)
  have s5 : DetStep B img ⟨b4, S⟩ ⟨b5, S⟩ := dstep f8001e08e rfl (by rw [exec_opimm]; rfl)
  have s6 : DetStep B img ⟨b5, S⟩ ⟨b6, S⟩ := dstep f8001e090 rfl (by rw [exec_op]; rfl)
  have s7 : DetStep B img ⟨b6, S⟩ ⟨b7, S⟩ := dstep f8001e094 rfl (by rw [exec_op]; rfl)
  have s8 : DetStep B img ⟨b7, S⟩ ⟨b8, S⟩ := dstep f8001e098 rfl (by rw [exec_opimm]; rfl)
  have k8 : b8.sameCsr c := by
    simp only [b8, b7, b6, b5, b4, b3, b2, b1, b0]
    exact (Core.sameCsr_wr _ _ _ _).trans ((Core.sameCsr_wr _ _ _ _).trans ((Core.sameCsr_wr _ _ _ _).trans
      ((Core.sameCsr_wr _ _ _ _).trans ((Core.sameCsr_wr _ _ _ _).trans ((Core.sameCsr_wr _ _ _ _).trans
      ((Core.sameCsr_wr _ _ _ _).trans ((Core.sameCsr_wr _ _ _ _).trans ((Core.sameCsr_goto _ _).trans hi.csr))))))))
  have runb : QRun B img 9 ⟨d, S⟩ ⟨b8, S⟩ := by
    have k : ∀ x : Core, x.sameCsr c → Quiet x := q
    exact .step (k _ hi.csr) s0 (.step (k _ ((Core.sameCsr_goto _ _).trans hi.csr)) s1
      (.step (k _ ((Core.sameCsr_wr _ _ _ _).trans ((Core.sameCsr_goto _ _).trans hi.csr))) s2
      (.step (k _ ((Core.sameCsr_wr _ _ _ _).trans ((Core.sameCsr_wr _ _ _ _).trans ((Core.sameCsr_goto _ _).trans
        hi.csr)))) s3
      (.step (k _ ((Core.sameCsr_wr _ _ _ _).trans ((Core.sameCsr_wr _ _ _ _).trans ((Core.sameCsr_wr _ _ _ _).trans
        ((Core.sameCsr_goto _ _).trans hi.csr))))) s4
      (.step (k _ ((Core.sameCsr_wr _ _ _ _).trans ((Core.sameCsr_wr _ _ _ _).trans ((Core.sameCsr_wr _ _ _ _).trans
        ((Core.sameCsr_wr _ _ _ _).trans ((Core.sameCsr_goto _ _).trans hi.csr)))))) s5
      (.step (k _ ((Core.sameCsr_wr _ _ _ _).trans ((Core.sameCsr_wr _ _ _ _).trans ((Core.sameCsr_wr _ _ _ _).trans
        ((Core.sameCsr_wr _ _ _ _).trans ((Core.sameCsr_wr _ _ _ _).trans ((Core.sameCsr_goto _ _).trans hi.csr))))))) s6
      (.step (k _ ((Core.sameCsr_wr _ _ _ _).trans ((Core.sameCsr_wr _ _ _ _).trans ((Core.sameCsr_wr _ _ _ _).trans
        ((Core.sameCsr_wr _ _ _ _).trans ((Core.sameCsr_wr _ _ _ _).trans ((Core.sameCsr_wr _ _ _ _).trans
        ((Core.sameCsr_goto _ _).trans hi.csr)))))))) s7
      (.single (k _ ((Core.sameCsr_wr _ _ _ _).trans ((Core.sameCsr_wr _ _ _ _).trans ((Core.sameCsr_wr _ _ _ _).trans
        ((Core.sameCsr_wr _ _ _ _).trans ((Core.sameCsr_wr _ _ _ _).trans ((Core.sameCsr_wr _ _ _ _).trans
        ((Core.sameCsr_wr _ _ _ _).trans ((Core.sameCsr_goto _ _).trans hi.csr))))))))) s8))))))))
  -- the copy loop's registers
  have gb : ∀ r : Reg, r.val ∉ [8, 13, 18, 30, 31] → b8.get r = d.get r := by
    intro r hr
    have a : r ≠ 8 := fun e => hr (by subst e; decide)
    have b : r ≠ 13 := fun e => hr (by subst e; decide)
    have c' : r ≠ 18 := fun e => hr (by subst e; decide)
    have d' : r ≠ 30 := fun e => hr (by subst e; decide)
    have e' : r ≠ 31 := fun e => hr (by subst e; decide)
    simp [b8, b7, b6, b5, b4, b3, b2, b1, b0, Core.wr_get_ne, a, b, c', d', e']
  have dl : acc.length ≤ (c.get 12).toNat := by omega
  have cr : CopyRegs b8 (c.get 11) (c.get 12).toNat src acc.length code 0 := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [b8, b7, b6, b5, b4, b3, Core.wr_get_ne, Core.wr_get_self, alu, b2, b1, b0, hi.t0, hi.t4]
    · have e1 : b6.get 31 = alu .and (alu .add (alu .sltu (c.get 12) (alu .sub (c.get 12) (BitVec.ofNat 32 acc.length)))
          0xffffffff#32) (alu .sub (c.get 12) (BitVec.ofNat 32 acc.length)) := by
        simp [b6, b5, b4, b3, b2, b1, b0, Core.wr_get_ne, Core.wr_get_self, hi.a2, hi.t2]
      have e2 : b8.get 31 = b6.get 31 := by simp [b8, b7, Core.wr_get_ne]
      have := t6_val (c.get 12).toNat acc.length dl (by omega)
      simp only [ofNat_toNat] at this
      rw [e2, e1]; exact this
    · rw [gb 19 (by decide)]; exact h19
    · simp [b8, b7, Core.wr_get_ne, Core.wr_get_self, alu, b6, b5, b4, b3, b2, b1, b0, hi.a1, hi.t2]
    · rw [gb 29 (by decide)]; exact hi.t4
    · simp only [b8, Core.wr_get_self _ (8 : Reg) _ _ (by decide), alu]
      rw [show b7.get 15 = d.get 15 by simp [b7, b6, b5, b4, b3, b2, b1, b0, Core.wr_get_ne], h15, zext_val]
    · simp [b8, b7, b6, b5, b4, b3, b2, Core.wr_get_ne, Core.wr_get_self, alu, b1]
  obtain ⟨n1, f, S', hrc, hpcf, hcsf, h13f, hgf, hin, hout, hx⟩ :=
    copy (c.get 11) (c.get 12).toNat src acc.length code hb' hl ⟨hc, by omega⟩ (by omega) ord.1
      (code - 2) 0 b8 S (by omega) rfl (q _ k8) cr
  -- 0x8001e0c6..0x8001e0ca: src += code, dst += code - 1
  let f1 := f.wr 29 (alu .add (f.get 29) (f.get 13)) 0x8001e0c8
  let f2 := f1.wr 29 (alu .add (f1.get 29) 0x1#32) 0x8001e0ca
  let f3 := f2.wr 7 (alu .add (f2.get 7) (f2.get 13)) 0x8001e0cc
  have t1 : DetStep B img ⟨f, S'⟩ ⟨f1, S'⟩ := dstep f8001e0c6 hpcf (by rw [exec_op, hpcf]; rfl)
  have t2 : DetStep B img ⟨f1, S'⟩ ⟨f2, S'⟩ := dstep f8001e0c8 rfl (by rw [exec_opimm]; rfl)
  have t3 : DetStep B img ⟨f2, S'⟩ ⟨f3, S'⟩ := dstep f8001e0ca rfl (by rw [exec_op]; rfl)
  have kf : f.sameCsr c := hcsf.trans k8
  have k3 : f3.sameCsr c := (Core.sameCsr_wr _ _ _ _).trans ((Core.sameCsr_wr _ _ _ _).trans
    ((Core.sameCsr_wr _ _ _ _).trans kf))
  have run3 : QRun B img _ ⟨d, S⟩ ⟨f3, S'⟩ :=
    runb.trans (hrc.trans (.step (q _ kf) t1 (.step (q _ ((Core.sameCsr_wr _ _ _ _).trans kf)) t2
      (.single (q _ ((Core.sameCsr_wr _ _ _ _).trans ((Core.sameCsr_wr _ _ _ _).trans kf))) t3))))
  have gf : ∀ r : Reg, r.val ∉ [8, 9, 13, 15, 18, 30, 31] → f.get r = d.get r := by
    intro r hr
    rw [hgf r (fun e => hr (by subst e; decide)) (fun e => hr (by subst e; decide)) (fun e => hr (by subst e; decide))]
    exact gb r (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; omega)
  have hdlen : data.length = code - 1 := by simp [data]
  have i3 : LInv c R n (src + code) (acc ++ data) f3 S' := hi.mk' f3 S' (src + code) (acc ++ data) k3
    (fun r hr => by
      have a : r ≠ 7 := fun e => hr (by subst e; decide)
      have b : r ≠ 29 := fun e => hr (by subst e; decide)
      simp only [f3, f2, f1, Core.wr_get_ne _ _ _ _ _ a, Core.wr_get_ne _ _ _ _ _ b]
      exact gf r (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; omega))
    (by
      simp only [f3, f2, f1, Core.wr_get_ne _ _ _ _ _ (show (29 : Reg) ≠ 7 by decide),
        Core.wr_get_self _ (29 : Reg) _ _ (by decide), alu, h13f]
      rw [gf 29 (by decide), hi.t4]
      apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega)
    (by
      simp only [f3, Core.wr_get_self _ (7 : Reg) _ _ (by decide), alu, f2, f1,
        Core.wr_get_ne _ _ _ _ _ (show (7 : Reg) ≠ 29 by decide),
        Core.wr_get_ne _ _ _ _ _ (show (13 : Reg) ≠ 29 by decide), h13f, List.length_append, hdlen]
      rw [gf 7 (by decide), hi.t2]
      apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega)
    (by
      intro j hj
      by_cases j1 : j < acc.length
      · rw [hout j (Or.inl (by omega)) hj, hi.bytes j hj, dif_pos j1, dif_pos (by simp; omega),
          List.getElem_append_left j1]
      · by_cases j2 : j < acc.length + (code - 1)
        · rw [hin j (by omega) (by omega), hi.bytes _ (by omega), dif_neg (by omega), dif_pos (by simp [hdlen]; omega),
            List.getElem_append_right (by omega)]
          simp only [data, List.getElem_map, List.getElem_range]
        · rw [hout j (Or.inr (by omega)) hj, hi.bytes j hj, dif_neg j1, dif_neg (by simp [hdlen]; omega)])
    hx ⟨by simp [hdlen]; omega, hok⟩
  have h28' : f3.get 28 = BitVec.ofNat 32 code := by
    simp only [f3, f2, f1, Core.wr_get_ne _ _ _ _ _ (show (28 : Reg) ≠ 7 by decide),
      Core.wr_get_ne _ _ _ _ _ (show (28 : Reg) ≠ 29 by decide)]
    rw [gf 28 (by decide)]; exact h28
  have h6' : f3.get 6 = 0xff#32 := i3.t1
  by_cases hff : code = 0xff
  · -- 0x8001e0cc: bne not taken; 0x8001e0d0: j 0x8001e064
    have nt : ¬ (taken .ne (f3.get 28) (f3.get 6) = true) := by
      rw [h28', h6', hff]; simp [taken]
    have u1 : DetStep B img ⟨f3, S'⟩ ⟨f3.goto 0x8001e0d0, S'⟩ := dstep f8001e0cc rfl (by rw [exec_branch, if_neg nt]; rfl)
    have u2 : DetStep B img ⟨f3.goto 0x8001e0d0, S'⟩ ⟨(f3.goto 0x8001e0d0).goto 0x8001e064, S'⟩ :=
      dstep f8001e0d0 rfl (by
        rw [exec_jal, Core.set_zero]; exact jump_lit _ 0x8001e0d0 _ 0x8001e064 rfl (by decide) (by decide))
    have i5 := (i3.goto 0x8001e0d0).goto 0x8001e064
    have run5 := run3.trans (.step (q _ k3) u1 (.single (q _ (i3.goto 0x8001e0d0).csr) u2))
    simp only [if_neg (show ¬ (code ≠ 0xff) from fun e => e hff), List.append_nil]
    constructor
    · intro hn
      obtain ⟨k, e, S'', hr, hx⟩ := G_exit c R h n (src + code) (acc ++ data) _ S' i5 rfl hn
      exact ⟨_, e, S'', run5.trans hr, hx⟩
    · intro hn
      exact ⟨_, _, S', run5.trans (G_cont c R h n (src + code) (acc ++ data) _ S' i5 rfl hn), rfl, i5.goto _⟩
  · -- 0x8001e0cc: bne taken → the tail 0x8001e0d8
    have tk : taken .ne (f3.get 28) (f3.get 6) = true := by
      rw [h28', h6']; simp only [taken, bne_iff_ne, ne_eq]
      intro e; have := congrArg BitVec.toNat e; simp at this; omega
    have u1 : DetStep B img ⟨f3, S'⟩ ⟨f3.goto 0x8001e0d8, S'⟩ := dstep f8001e0cc rfl (by
      rw [exec_branch, if_pos tk]; exact jump_lit _ 0x8001e0cc _ 0x8001e0d8 rfl (by decide) (by decide))
    have i4 := i3.goto 0x8001e0d8
    have run4 := run3.trans (.single (q _ k3) u1)
    simp only [if_pos hff]
    constructor
    · intro hn
      obtain ⟨k, e, S'', hr, hx⟩ := tail_exit c R h n (src + code) (acc ++ data) _ S' i4 rfl hn
      exact ⟨_, e, S'', run4.trans hr, hx⟩
    · intro hn
      obtain ⟨k, e, S'', hr, hpc', hx⟩ := tail_cont c R h n (src + code) (acc ++ data) _ S' i4 rfl hn
        (by simp [hdlen]; omega)
      exact ⟨_, e, S'', run4.trans hr, hpc', hx⟩

end E5R.Rmk.Cobs
