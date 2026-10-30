/-
  The session's None path, from `recv_step`'s None point (0x80003f7c, after `tail`) through the UART
  receive poll, on the pinned RMK image: EVERY behaviour, for every value the UART returns.

  Original e5r code, Apache-2.0.

  PROVED here: `none_step`: from `NoneAt` every behaviour of `Step` (`Lands`: no fault, no
  interrupt on the way) reaches either
  * the session loop head 0x80003e1a with `SessPre` again (bytes were read: filled += n ≤ 488), or
  * one of two EXPLICIT BOUNDARIES where the code hands control towards the read future and the
    executor, which are not proved: 0x80003ff2 (discarding, or nothing pending) and 0x80004428
    (the buffer is full, or the UART had no byte ready).

  EXPLICIT ASSUMPTIONS in `NoneAt` (not proved here): the Uart16550 struct that s3 points to holds
  the UART base 0x10000000 (at +0x1c) and register stride 1 (at +0x20), outside the future's state
  words s6+0x2f3..s6+0x30c; the task flag pointer at sp+0x24 points into RAM outside the deframer;
  the stack has 0x28 bytes above sp. Everything else is from `recv_step` (Deframer/Session.lean).
-/
import Projects.rmk.Deframer.Rx
import Projects.rmk.Deframer.NoneSegs
import Projects.rmk.Deframer.Session

set_option maxRecDepth 100000

namespace E5R.Rmk.Deframer.NoneP
open E5R E5R.Rmk E5R.Rmk.Deframer.Tail E5R.Rmk.Deframer.Session E5R.Rmk.Deframer.Rx

structure NoneAt (m : Machine) : Prop where
  pc : m.core.pc = 0x80003f7c
  quiet : Quiet m.core
  s6 : m.core.get 22 = s6v
  s7 : m.core.get 23 = s7v
  spAl : (m.core.get 2).toNat % 4 = 0
  sp : 0x8002a798 + 0x70 ≤ (m.core.get 2).toNat ∧ (m.core.get 2).toNat + 0x28 ≤ 0x81000000
  inv : Inv m.ram dfr bufLen
  cons0 : consumed m.ram dfr = 0
  s2 : m.core.get 18 = bufA + BitVec.ofNat 32 (filled m.ram dfr)
  s4 : (m.core.get 20).toNat = bufLen - filled m.ram dfr
  disc : discarding m.ram dfr ≤ 1
  s9 : (m.core.get 25).toNat = discarding m.ram dfr
  s58 : (m.core.get 21).toNat ≤ (m.core.get 24).toNat ∧ (m.core.get 24).toNat - (m.core.get 21).toNat = filled m.ram dfr
  -- explicit assumptions: the Uart16550 struct and the task flag pointer
  uBase : ramRead m.ram (m.core.get 19 + 0x0000001c#32) .w = 0x10000000
  uBaseIn : (m.core.get 19 + 0x0000001c#32).toNat % 4 = 0 ∧ B.inRam (m.core.get 19 + 0x0000001c#32) 4 = true
  uStride : (m.ram (m.core.get 19 + 0x00000020#32)).toNat = 1
  uStrideIn : B.inRam (m.core.get 19 + 0x00000020#32) 1 = true
  uSep : ∀ k < 4, ((m.core.get 19 + 0x0000001c#32 + BitVec.ofNat 32 k).toNat < 0x8002a7b0 ∨
      0x8002a7ca ≤ (m.core.get 19 + 0x0000001c#32 + BitVec.ofNat 32 k).toNat) ∧
    ((m.core.get 19 + 0x00000020#32).toNat < 0x8002a7b0 ∨ 0x8002a7ca ≤ (m.core.get 19 + 0x00000020#32).toNat)
  flagIn : B.inRam (ramRead m.ram (m.core.get 2 + 0x00000024#32) .w) 1 = true
  flagSep : (ramRead m.ram (m.core.get 2 + 0x00000024#32) .w).toNat < dfr.toNat ∨
    dfr.toNat + 12 ≤ (ramRead m.ram (m.core.get 2 + 0x00000024#32) .w).toNat

/-- Where the None path may stop: the loop head again, or the read future's two boundaries. -/
def NoneQ (m : Machine) : Prop := SessPre m ∨ m.core.pc = 0x80003ff2 ∨ m.core.pc = 0x80004428

/-- The future-state stores touch only s6+0x2f3 .. s6+0x30c. -/
theorem nGo1_other (e : Core) (M : Word → BitVec 8) (h22 : e.get 22 = s6v) (x : Word)
    (hx : x.toNat < 0x8002a7b0 ∨ 0x8002a7ca ≤ x.toNat) : nGo1Ram e M x = M x := by
  simp only [nGo1Ram, h22]
  rw [wr_byte_other _ _ _ _ (by decide) (by rw [show (s6v + 0x00000303#32).toNat = 0x8002a7c0 from rfl]; omega),
    wr_byte_other _ _ _ _ (by decide) (by rw [show (s6v + 0x000002f7#32).toNat = 0x8002a7b4 from rfl]; omega),
    wr_byte_other _ _ _ _ (by decide) (by rw [show (s6v + 0x000002f3#32).toNat = 0x8002a7b0 from rfl]; omega),
    ramWrite, ramPut_ne _ (fun e => by subst e; rw [show (s6v + 0x0000030c#32).toNat = 0x8002a7c9 from rfl] at hx; omega),
    wr_byte_other _ _ _ _ (by decide) (by rw [show (s6v + 0x00000307#32).toNat = 0x8002a7c4 from rfl]; omega),
    wr_byte_other _ _ _ _ (by decide) (by rw [show (s6v + 0x000002ff#32).toNat = 0x8002a7bc from rfl]; omega),
    wr_byte_other _ _ _ _ (by decide) (by rw [show (s6v + 0x000002fb#32).toNat = 0x8002a7b8 from rfl]; omega)]

theorem none_step (m : Machine) (h : NoneAt m) : Lands B img NoneQ m := by
  obtain ⟨c, M⟩ := m
  have h22 : c.get 22 = s6v := h.s6
  have h23 : c.get 23 = s7v := h.s7
  have hsp : 0x8002a798 + 0x70 ≤ (c.get 2).toNat ∧ (c.get 2).toNat + 0x28 ≤ 0x81000000 := h.sp
  have hI : consumed M dfr ≤ filled M dfr ∧ filled M dfr ≤ bufLen := h.inv
  have hc0 : consumed M dfr = 0 := h.cons0
  have hs4 : (c.get 20).toNat = bufLen - filled M dfr := h.s4
  have hs9 : (c.get 25).toNat = discarding M dfr := h.s9
  have hs58 : (c.get 21).toNat ≤ (c.get 24).toNat ∧ (c.get 24).toNat - (c.get 21).toNat = filled M dfr := h.s58
  have hbl : bufLen = 488 := rfl
  have s6in : ∀ k : Nat, k < 0x1d → B.inRam (s6v + BitVec.ofNat 32 (0x2f3 + k)) 1 = true := by
    intro k hk; rw [B_ram, show (s6v + BitVec.ofNat 32 (0x2f3 + k)).toNat = 0x8002a7b0 + k by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat]; rw [show s6v.toNat = 0x8002a4bd from rfl]; omega]; omega
  -- discarding: the read future for discarded bytes (boundary)
  by_cases hd : c.get 25 ≠ 0
  · exact lands_of_qrun (nDisc c M h.pc h.quiet (by simp only [taken, bne_iff_ne, ne_eq]; exact hd)) (.inr (.inl rfl))
  have hd0 : c.get 25 = 0 := by simpa using hd
  have t25 : taken .ne (c.get 25) 0 = false := by rw [hd0]; rfl
  -- nothing pending (boundary)
  by_cases hp : (c.get 21).toNat ≥ (c.get 24).toNat
  · exact lands_of_qrun (nNoP c M h.pc h.quiet t25 (by
      simp only [taken, BitVec.ult, Bool.not_eq_true', decide_eq_false_iff_not]; omega)) (.inr (.inl rfl))
  have t2124 : taken .geu (c.get 21) (c.get 24) = false := by
    simp only [taken, BitVec.ult, Bool.not_eq_false', decide_eq_true_eq]; omega
  have hf0 : 0 < filled M dfr := by omega
  -- the store side conditions of the future state
  have stw : ∀ k : Nat, k = 0x2f3 ∨ k = 0x2f7 ∨ k = 0x2fb ∨ k = 0x2ff ∨ k = 0x303 ∨ k = 0x307 →
      (c.get 22 + BitVec.ofNat 32 k).toNat % 4 = 0 ∧ B.inRam (c.get 22 + BitVec.ofNat 32 k) 4 = true := by
    intro k hk; rw [h22]; rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  -- the buffer is full (boundary)
  by_cases hfull : c.get 20 = 0
  · exact lands_of_qrun (nFull c M h.pc h.quiet t25 t2124 (stw 0x2fb (by decide)).1 (stw 0x2fb (by decide)).2
      (stw 0x2ff (by decide)).1 (stw 0x2ff (by decide)).2 (stw 0x307 (by decide)).1 (stw 0x307 (by decide)).2
      (Nat.mod_one _) (by rw [h22]; decide) (stw 0x2f3 (by decide)).1 (stw 0x2f3 (by decide)).2
      (stw 0x2f7 (by decide)).1 (stw 0x2f7 (by decide)).2 (stw 0x303 (by decide)).1 (stw 0x303 (by decide)).2
      (by rw [hfull]; rfl)) (.inr (.inr rfl))
  have hcap : 1 ≤ (c.get 20).toNat := by
    have : (c.get 20).toNat ≠ 0 := fun e => hfull (BitVec.eq_of_toNat_eq e)
    omega
  -- the future state, then the Uart16550 register addresses
  have r1 := nGo1 c M h.pc h.quiet t25 t2124 (stw 0x2fb (by decide)).1 (stw 0x2fb (by decide)).2
    (stw 0x2ff (by decide)).1 (stw 0x2ff (by decide)).2 (stw 0x307 (by decide)).1 (stw 0x307 (by decide)).2
    (Nat.mod_one _) (by rw [h22]; decide) (stw 0x2f3 (by decide)).1 (stw 0x2f3 (by decide)).2
    (stw 0x2f7 (by decide)).1 (stw 0x2f7 (by decide)).2 (stw 0x303 (by decide)).1 (stw 0x303 (by decide)).2
    (by simp only [taken, bne_iff_ne, ne_eq]; exact hfull)
  let G1 := nGo1Core c M
  let M1 := nGo1Ram c M
  have g1 : ∀ r : Reg, G1.get r = c.get r := fun r => by simp [G1, nGo1Core]
  have qG1 : Quiet G1 := Quiet.of_sameCsr (by
    unfold G1 nGo1Core
    repeat (first | exact Core.sameCsr_wr _ _ _ _ | exact Core.sameCsr_goto _ _ | refine (Core.sameCsr_wr _ _ _ _).trans ?_ | refine (Core.sameCsr_goto _ _).trans ?_)) h.quiet
  have M1o := nGo1_other c M h22
  have uS := h.uSep
  have stride : M1 (c.get 19 + 0x00000020#32) = M (c.get 19 + 0x00000020#32) := M1o _ (uS 0 (by decide)).2
  have base : ramRead M1 (c.get 19 + 0x0000001c#32) .w = 0x10000000 := by
    rw [← h.uBase]; exact ramRead_w_congr _ fun k hk => M1o _ (uS k hk).1
  have sv : extend .b false (ramRead M1 (c.get 19 + 0x00000020#32) .b) = 1 := by
    rw [Next.lbu_val, stride]; apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_ofNat]; rw [h.uStride]; rfl
  have r2 := nGo2 G1 M1 rfl qG1 (Nat.mod_one _) (by rw [g1]; exact h.uStrideIn)
    (by rw [g1, sv]; decide) (by rw [g1]; exact h.uBaseIn.1) (by rw [g1]; exact h.uBaseIn.2)
  let G2 := nGo2Core G1 M1
  have qG2 : Quiet G2 := Quiet.of_sameCsr (by
    unfold G2 nGo2Core
    repeat (first | exact Core.sameCsr_wr _ _ _ _ | exact Core.sameCsr_goto _ _ | refine (Core.sameCsr_wr _ _ _ _).trans ?_ | refine (Core.sameCsr_goto _ _).trans ?_)) qG1
  have gG2 : ∀ r : Reg, r ≠ 9 → r ≠ 10 → r ≠ 11 → r ≠ 19 → r ≠ 21 → r ≠ 24 → G2.get r = c.get r :=
    fun r a b c' d' e' f' => by simp [G2, nGo2Core, Core.wr_get_ne, a, b, c', d', e', f', g1]
  have G2_19 : G2.get 19 = 0x10000000 := by
    simp [G2, nGo2Core, Core.wr_get_ne, Core.wr_get_self, g1]; exact base
  have G2_21 : G2.get 21 = 0x10000005 := by
    simp [G2, nGo2Core, Core.wr_get_ne, Core.wr_get_self, g1, sv, base]; decide
  have G2_9 : G2.get 9 = BitVec.ofNat 32 0 := by simp [G2, nGo2Core, Core.wr_get_ne, Core.wr_get_self]; rfl
  have G2_pc : G2.pc = 0x80004374 := rfl
  have fl : (filled M dfr) + (c.get 20).toNat = 488 := by omega
  have exd : (bufA + BitVec.ofNat 32 (filled M dfr)).toNat = 0x8002a590 + filled M dfr := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, show bufA.toNat = 0x8002a590 from rfl]; omega
  have env : RxEnv G2 := by
    refine ⟨G2_19, G2_21, ?_, ?_, ?_⟩
    · rw [gG2 20 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hcap
    · rw [gG2 20 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
        gG2 18 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h.s2, B_ram, exd]; omega
    · rw [gG2 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), B_ram]
      constructor <;> bv_omega
  refine lands_of_qrun_lands (r1.trans r2) (lands_seq (Q := RxOut G2 M1) ?_
    (rx_loop G2 M1 env _ 0 G2 M1 rfl ⟨G2_pc, qG2, fun r _ => rfl, G2_9, by
      rw [gG2 20 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; omega,
      fun x _ _ => rfl⟩))
  -- after the poll: nothing read (boundary), or filled += n and back to the loop head
  rintro ⟨x, Mx⟩ ⟨xpc, xq, xr, x9, xram⟩
  have xs : ∀ r : Reg, r.val ∉ rxW → r ≠ 9 → r ≠ 10 → r ≠ 11 → r ≠ 19 → r ≠ 21 → r ≠ 24 → x.get r = c.get r :=
    fun r hr a b c' d' e' f' => (xr r hr).trans (gG2 r a b c' d' e' f')
  have x2 : x.get 2 = c.get 2 := xs 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have x22 : x.get 22 = s6v := (xs 22 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h22
  have x23 : x.get 23 = s7v := (xs 23 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h23
  have cap20 : (G2.get 20).toNat = 488 - filled M dfr := by
    rw [gG2 20 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; omega
  have g18 : G2.get 18 = bufA + BitVec.ofNat 32 (filled M dfr) :=
    (gG2 18 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h.s2
  have g2 : G2.get 2 = c.get 2 := gG2 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  -- RAM after the poll, outside the buffer's free part and the stack byte, is the entry RAM
  have MxM : ∀ y : Word, (y.toNat < 0x8002a590 + filled M dfr ∨ 0x8002a590 + 488 ≤ y.toNat) →
      y ≠ c.get 2 + 0xffffffe0#32 + 0x0000000f#32 → (y.toNat < 0x8002a7b0 ∨ 0x8002a7ca ≤ y.toNat) → Mx y = M y := by
    intro y h1 h2 h3
    exact (xram y (by rw [g18, exd, cap20]; omega) (by rw [g2]; exact h2)).trans (M1o y h3)
  by_cases hz : x.get 9 = 0
  · exact lands_of_qrun (nZero x Mx xpc xq (by rw [hz]; rfl)) (.inr (.inr rfl))
  have hspb : 0x8002a808 ≤ (c.get 2).toNat := by omega
  have hsa : (c.get 2).toNat % 4 = 0 := h.spAl
  have fIn : B.inRam (ramRead M (c.get 2 + 0x00000024#32) .w) 1 = true := h.flagIn
  have fS : (ramRead M (c.get 2 + 0x00000024#32) .w).toNat < dfr.toNat ∨
      dfr.toNat + 12 ≤ (ramRead M (c.get 2 + 0x00000024#32) .w).toNat := h.flagSep
  have hdsc : (M (dfr + 8)).toNat ≤ 1 := h.disc
  have e24 : (c.get 2 + 0x00000024#32).toNat = (c.get 2).toNat + 0x24 := by bv_omega
  have esb : (c.get 2 + 0xffffffe0#32 + 0x0000000f#32).toNat = (c.get 2).toNat - 0x11 := by bv_omega
  have Fx : ramRead Mx (c.get 2 + 0x00000024#32) .w = ramRead M (c.get 2 + 0x00000024#32) .w :=
    rd_congr _ (by omega) fun y h1 h2 => MxM y (by omega) (fun e => by rw [e, esb] at h1; omega) (by omega)
  have hdf : ∀ y : Word, y.toNat < 0x8002a798 → 0x8002a78c ≤ y.toNat →
      Mx y = M y := fun y h1 h2 => MxM y (by omega) (fun e => by rw [e, esb] at h1; omega) (by omega)
  have r3 := nCommit x Mx xpc xq (by simp only [taken, beq_eq_false_iff_ne]; exact hz)
    (by rw [x2, e24]; omega) (by rw [x2, B_ram, e24]; omega)
    (Nat.mod_one _) (by rw [x2, Fx]; exact fIn)
    (by rw [x22]; decide) (by rw [x22]; decide) (by rw [x22]; decide) (by rw [x22]; decide)
  refine lands_of_qrun r3 (.inl ?_)
  let F := ramRead Mx (x.get 2 + 0x00000024#32) .w
  have hF : F.toNat < dfr.toNat ∨ dfr.toNat + 12 ≤ F.toNat := by
    show (ramRead Mx (x.get 2 + 0x00000024#32) .w).toNat < dfr.toNat ∨
      dfr.toNat + 12 ≤ (ramRead Mx (x.get 2 + 0x00000024#32) .w).toNat
    rw [x2, Fx]; exact fS
  rw [show dfr.toNat = 0x8002a78c from rfl] at hF
  let Mb := ramWrite Mx F (alu .add 0 0x00000001#32) .b
  have Mbo : ∀ y : Word, 0x8002a78c ≤ y.toNat → y.toNat < 0x8002a798 → Mb y = Mx y := by
    intro y h1 h2; exact ramPut_ne _ (fun e => by subst e; omega)
  have eq_cr : ramRead (nCommitRam x Mx) dfr .w = ramRead M dfr .w := by
    show ramRead (ramWrite Mb (x.get 22 + 0x000002d3#32) _ .w) dfr .w = _
    rw [x22, rd_wr_far _ _ _ _ _ (by decide) (by decide) (by decide)]
    exact rd_congr _ (by decide) fun y h1 h2 => by
      rw [show dfr.toNat = 0x8002a78c from rfl] at h1 h2
      rw [Mbo y h1 (by omega), hdf y (by omega) h1]
  have eq_fl : ramRead Mb (dfr + 4) .w = ramRead M (dfr + 4) .w :=
    rd_congr _ (by decide) fun y h1 h2 => by
      rw [show (dfr + 4).toNat = 0x8002a790 from rfl] at h1 h2
      rw [Mbo y (by omega) (by omega), hdf y (by omega) (by omega)]
  have eq_d : nCommitRam x Mx (dfr + 8) = M (dfr + 8) := by
    show ramWrite Mb (x.get 22 + 0x000002d3#32) _ .w (dfr + 8) = _
    rw [x22, wr_byte_other _ _ _ _ (by decide) (by decide), Mbo _ (by decide) (by decide), hdf _ (by decide) (by decide)]
  have x9' : (x.get 9).toNat ≤ 488 - filled M dfr := by rw [← cap20]; exact x9
  have fM : (ramRead M (dfr + 4) .w).toNat = filled M dfr := rfl
  have eq_f : filled (nCommitRam x Mx) dfr = filled M dfr + (x.get 9).toNat := by
    show (ramRead (ramWrite Mb (x.get 22 + 0x000002d3#32)
      (alu .add (ramRead Mb (x.get 22 + 0x000002d3#32) .w) (x.get 9)) .w) (dfr + 4) .w).toNat = _
    rw [x22, show s6v + 0x000002d3#32 = dfr + 4 from rfl, ramRead_ramWrite_w, alu_add, eq_fl, BitVec.toNat_add, fM]
    omega
  refine ⟨rfl, Quiet.of_sameCsr (by
      unfold nCommitCore
      repeat (first | exact Core.sameCsr_wr _ _ _ _ | exact Core.sameCsr_goto _ _ | refine (Core.sameCsr_wr _ _ _ _).trans ?_ | refine (Core.sameCsr_goto _ _).trans ?_)) xq,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show (nCommitCore x Mx).get 22 = s6v; simp [nCommitCore, Core.wr_get_ne, x22]
  · show (nCommitCore x Mx).get 23 = s7v; simp [nCommitCore, Core.wr_get_ne, x23]
  · show ((nCommitCore x Mx).get 2).toNat % 4 = 0; simp [nCommitCore, Core.wr_get_ne, x2]; exact hsa
  · show 0x8002a798 + 0x70 ≤ ((nCommitCore x Mx).get 2).toNat ∧ ((nCommitCore x Mx).get 2).toNat ≤ 0x81000000
    simp [nCommitCore, Core.wr_get_ne, x2]; omega
  · show consumed (nCommitRam x Mx) dfr ≤ filled (nCommitRam x Mx) dfr ∧ filled (nCommitRam x Mx) dfr ≤ bufLen
    have : consumed (nCommitRam x Mx) dfr = consumed M dfr := congrArg BitVec.toNat eq_cr
    rw [this, eq_f]; omega
  · show (nCommitRam x Mx (dfr + 8)).toNat ≤ 1; rw [eq_d]; exact hdsc

end E5R.Rmk.Deframer.NoneP
