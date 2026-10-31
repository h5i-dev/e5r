/-
  A function contract on the emitted Embassy firmware: `duty`, the mean of an
  eight-byte window plus 7, clamped at 100.

    fn duty(window: &[u8; 8]) -> u32 {
        let sum: u32 = window.iter().map(|&s| u32::from(s)).sum();
        (sum / 8 + 7).min(100)
    }

  The proof is about the instructions rustc emitted at `duty`'s address in
  the checked flash image, from every state that satisfies the RISC-V
  calling convention for this signature: `a0` points at eight readable bytes
  of RAM and `ra` holds the return address. The loop is proved by an
  invariant over the iteration count, not by unrolling, and the result is
  related to the source-level expression above (`spec`), not only to what
  the compiler made of it.

  Interrupts are not part of this contract: it describes the function's own
  instruction sequence. Whole-firmware proofs account for interrupts that
  arrive in the middle of it.
-/
import Theories.Logic
import Theories.Board.Hifive1Revb
import Projects.hifive1.Image

set_option maxRecDepth 100000

namespace E5R.Hifive1.Duty
open E5R

abbrev B := Hifive1Revb.board
abbrev img := Firmware.segments

def entry : Word := 0x200102a0
def loopPc : Word := 0x200102a6
def exitPc : Word := 0x200102b2

/-! ## The instructions at `duty` (kernel-checked against the image) -/

theorem i0 : fetchDecode img 0x200102a0 = some (.opimm .add 11 0 0, 2) := by decide +kernel
theorem i1 : fetchDecode img 0x200102a2 = some (.opimm .add 12 10 8, 4) := by decide +kernel
theorem i2 : fetchDecode img 0x200102a6 = some (.load .b false 13 10 0, 4) := by decide +kernel
theorem i3 : fetchDecode img 0x200102aa = some (.opimm .add 10 10 1, 2) := by decide +kernel
theorem i4 : fetchDecode img 0x200102ac = some (.op .add 11 11 13, 2) := by decide +kernel
theorem i5 : fetchDecode img 0x200102ae = some (.branch .ne 10 12 (-8), 4) := by decide +kernel
theorem i6 : fetchDecode img 0x200102b2 = some (.opimm .srl 10 11 3, 4) := by decide +kernel
theorem i7 : fetchDecode img 0x200102b6 = some (.opimm .add 11 0 0x5d, 4) := by decide +kernel
theorem i8 : fetchDecode img 0x200102ba = some (.branch .ltu 10 11 8, 4) := by decide +kernel
theorem i9 : fetchDecode img 0x200102be = some (.opimm .add 10 0 0x5d, 4) := by decide +kernel
theorem i10 : fetchDecode img 0x200102c2 = some (.opimm .add 10 10 7, 2) := by decide +kernel
theorem i11 : fetchDecode img 0x200102c4 = some (.jalr 0 1 0, 2) := by decide +kernel

/-! ## Specification -/

/-- The sum of the first `k` bytes at `p`. -/
def sumBytes (ram : Word → BitVec 8) (p : Word) : Nat → Nat
  | 0 => 0
  | k+1 => sumBytes ram p k + (ram (p + BitVec.ofNat 32 k)).toNat

theorem sumBytes_le (ram : Word → BitVec 8) (p : Word) : ∀ k, sumBytes ram p k ≤ 255 * k
  | 0 => by simp [sumBytes]
  | k+1 => by
    have := sumBytes_le ram p k
    have := (ram (p + BitVec.ofNat 32 k)).isLt
    simp only [sumBytes]; omega

/-- The source-level result, in unbounded arithmetic (the `u32` sum of eight
    bytes cannot overflow, which `sumBytes_le` makes explicit). -/
def spec (ram : Word → BitVec 8) (p : Word) : Nat := min (sumBytes ram p 8 / 8 + 7) 100

/-- What a caller may assume: the RISC-V calling convention for
    `fn(&[u8; 8]) -> u32`, with the array in RAM. -/
structure Pre (c : Core) (p : Word) : Prop where
  pc : c.pc = entry
  arg : c.get 10 = p
  lo : B.ramBase ≤ p.toNat
  hi : p.toNat + 8 ≤ B.ramBase + B.ramSize

/-- What `duty` guarantees on return: the result in `a0`, control at the
    return address, RAM untouched, only caller-saved `a1`-`a3` clobbered,
    and every CSR and the reservation unchanged. -/
structure Post (c₀ : Core) (ram : Word → BitVec 8) (p : Word) (m : Machine) : Prop where
  ret : m.core.pc = c₀.get 1 &&& ~~~1
  result : (m.core.get 10).toNat = spec ram p
  bound : (m.core.get 10).toNat ≤ 100
  ram : m.ram = ram
  frame : ∀ r : Reg, r ≠ 10 → r ≠ 11 → r ≠ 12 → r ≠ 13 → m.core.get r = c₀.get r
  csr : m.core.sameCsr c₀

/-! ## The loop -/

/-- At the loop head after `k` iterations. -/
structure Inv (c₀ : Core) (ram : Word → BitVec 8) (p : Word) (k : Nat) (c : Core) : Prop where
  pc : c.pc = loopPc
  ptr : c.get 10 = p + BitVec.ofNat 32 k
  sum : c.get 11 = BitVec.ofNat 32 (sumBytes ram p k)
  stop : c.get 12 = p + 8
  frame : ∀ r : Reg, r ≠ 10 → r ≠ 11 → r ≠ 12 → r ≠ 13 → c.get r = c₀.get r
  csr : c.sameCsr c₀

/-- After the loop: the sum of all eight bytes in `a1`. -/
structure Done (c₀ : Core) (ram : Word → BitVec 8) (p : Word) (c : Core) : Prop where
  pc : c.pc = exitPc
  sum : c.get 11 = BitVec.ofNat 32 (sumBytes ram p 8)
  frame : ∀ r : Reg, r ≠ 10 → r ≠ 11 → r ≠ 12 → r ≠ 13 → c.get r = c₀.get r
  csr : c.sameCsr c₀

theorem board_ram : B.ramBase = 0x80000000 ∧ B.ramSize = 0x4000 := ⟨rfl, rfl⟩

/-- One iteration: load, advance, accumulate, branch. -/
theorem body {c₀ ram p k c} (pre : B.ramBase ≤ p.toNat ∧ p.toNat + 8 ≤ B.ramBase + B.ramSize)
    (hk : k < 8) (h : Inv c₀ ram p k c) :
    ∃ c', DetSteps B img 4 ⟨c, ram⟩ ⟨c', ram⟩ ∧
      (if k + 1 < 8 then Inv c₀ ram p (k+1) c' else Done c₀ ram p c') := by
  obtain ⟨hpc, hptr, hsum, hstop, hframe, hcsr⟩ := h
  rw [board_ram.1, board_ram.2] at pre
  have hk' : (p + BitVec.ofNat 32 k).toNat = p.toNat + k := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have hbyte : (extend .b false (ramRead ram (p + BitVec.ofNat 32 k) .b)).toNat =
      (ram (p + BitVec.ofNat 32 k)).toNat := by
    have := (ram (p + BitVec.ofNat 32 k)).isLt
    simp only [extend, ramRead, BitVec.toNat_and, BitVec.toNat_ofNat]
    rw [show (0xff : Word).toNat = 2^8 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]; omega
  generalize hbv : extend .b false (ramRead ram (p + BitVec.ofNat 32 k) .b) = byte at hbyte
  -- The machines along the iteration.
  have s1 : DetStep B img ⟨c, ram⟩ ⟨c.wr 13 byte (loopPc + 4), ram⟩ := by
    refine detStep_of (B := B) (by rw [hpc]; decide) (by rw [hpc]; exact i2) fun o => ?_
    have ha : c.get 10 + 0 = p + BitVec.ofNat 32 k := by rw [hptr]; simp
    rw [exec_load, ha, interp_load_ram o (by simp only [Width.bytes, Nat.mod_one]) ?_]
    · simp [hbv, hpc]
    · rw [Board.inRam_iff, hk', board_ram.1, board_ram.2]
      simp only [Width.bytes]; constructor <;> omega
  generalize hc1 : c.wr 13 byte (loopPc + 4) = c1 at s1
  have g1 : ∀ r : Reg, r ≠ 13 → c1.get r = c.get r := fun r h => by
    rw [← hc1, Core.wr_get_ne _ _ _ _ _ h]
  have g13 : c1.get 13 = byte := by rw [← hc1, Core.wr_get_self _ _ _ _ (by decide)]
  have p1 : c1.pc = 0x200102aa := by rw [← hc1]; rfl
  have s2 : DetStep B img ⟨c1, ram⟩ ⟨c1.wr 10 (c1.get 10 + 1) (0x200102aa + 2), ram⟩ := by
    refine detStep_of (B := B) (by rw [p1]; decide) (by rw [p1]; exact i3) fun o => ?_
    rw [exec_opimm, p1]; rfl
  generalize hc2 : c1.wr 10 (c1.get 10 + 1) (0x200102aa + 2) = c2 at s2
  have p2 : c2.pc = 0x200102ac := by rw [← hc2]; rfl
  have s3 : DetStep B img ⟨c2, ram⟩ ⟨c2.wr 11 (c2.get 11 + c2.get 13) (0x200102ac + 2), ram⟩ := by
    refine detStep_of (B := B) (by rw [p2]; decide) (by rw [p2]; exact i4) fun o => ?_
    rw [exec_op, p2]; rfl
  generalize hc3 : c2.wr 11 (c2.get 11 + c2.get 13) (0x200102ac + 2) = c3 at s3
  have p3 : c3.pc = 0x200102ae := by rw [← hc3]; rfl
  -- What the registers hold after the three straight-line steps.
  have r10 : c3.get 10 = p + BitVec.ofNat 32 (k+1) := by
    rw [← hc3, Core.wr_get_ne _ _ _ _ _ (by decide), ← hc2, Core.wr_get_self _ _ _ _ (by decide),
      g1 10 (by decide), hptr]
    apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add]; omega
  have r11 : c3.get 11 = BitVec.ofNat 32 (sumBytes ram p (k+1)) := by
    have hs := sumBytes_le ram p k
    rw [← hc3, Core.wr_get_self _ _ _ _ (by decide), ← hc2, Core.wr_get_ne _ _ _ _ _ (by decide),
      Core.wr_get_ne _ _ _ _ _ (by decide), g1 11 (by decide), g13, hsum]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat, sumBytes]
    rw [hbyte]; have := (ram (p + BitVec.ofNat 32 k)).isLt; omega
  have r12 : c3.get 12 = p + 8 := by
    rw [← hc3, Core.wr_get_ne _ _ _ _ _ (by decide), ← hc2, Core.wr_get_ne _ _ _ _ _ (by decide),
      g1 12 (by decide), hstop]
  have rf : ∀ r : Reg, r ≠ 10 → r ≠ 11 → r ≠ 12 → r ≠ 13 → c3.get r = c₀.get r := by
    intro r a b d e
    rw [← hc3, Core.wr_get_ne _ _ _ _ _ b, ← hc2, Core.wr_get_ne _ _ _ _ _ a, g1 r e,
      hframe r a b d e]
  have rc : c3.sameCsr c₀ := by
    rw [← hc3, ← hc2, ← hc1]
    exact ((Core.sameCsr_wr _ _ _ _).trans ((Core.sameCsr_wr _ _ _ _).trans
      (Core.sameCsr_wr _ _ _ _))).trans hcsr
  have hne : (p + BitVec.ofNat 32 (k+1) != p + 8) = decide (k + 1 < 8) := by
    by_cases hlt : k + 1 < 8
    · simp only [hlt, decide_true, bne_iff_ne, ne_eq]
      intro he; have := congrArg BitVec.toNat he
      simp [BitVec.toNat_add] at this; omega
    · have : k + 1 = 8 := by omega
      simp [this, hlt]
  by_cases hlt : k + 1 < 8
  · refine ⟨c3.goto loopPc, .step s1 (.step s2 (.step s3 (.single ?_))), ?_⟩
    · refine detStep_of (B := B) (by rw [p3]; decide) (by rw [p3]; exact i5) fun o => ?_
      rw [exec_branch]
      simp only [taken, r10, r12, hne, hlt, decide_true, ite_true, p3]
      rw [jump_ok _ _ (by decide)]; rfl
    · rw [if_pos hlt]
      exact ⟨rfl, by simp [r10], by simp [r11], by simp [r12],
        fun r a b d e => by simp [rf r a b d e], (Core.sameCsr_goto _ _).trans rc⟩
  · refine ⟨c3.goto exitPc, .step s1 (.step s2 (.step s3 (.single ?_))), ?_⟩
    · refine detStep_of (B := B) (by rw [p3]; decide) (by rw [p3]; exact i5) fun o => ?_
      rw [exec_branch]
      simp only [taken, r10, r12, hne, hlt, decide_false, Bool.false_eq_true, ite_false, p3]
      rfl
    · have : k + 1 = 8 := by omega
      rw [if_neg hlt]
      exact ⟨rfl, by simp [r11, this], fun r a b d e => by simp [rf r a b d e],
        (Core.sameCsr_goto _ _).trans rc⟩

/-- The loop, by induction on the iterations left. -/
theorem loop {c₀ ram p} (pre : B.ramBase ≤ p.toNat ∧ p.toNat + 8 ≤ B.ramBase + B.ramSize) :
    ∀ j k c, k + j = 8 → 0 < j → Inv c₀ ram p k c →
      ∃ c', DetSteps B img (4 * j) ⟨c, ram⟩ ⟨c', ram⟩ ∧ Done c₀ ram p c'
  | 0, _, _, _, hj, _ => absurd hj (by decide)
  | j+1, k, c, hkj, _, h => by
    obtain ⟨c', hs, hc'⟩ := body pre (by omega) h
    by_cases hlt : k + 1 < 8
    · rw [if_pos hlt] at hc'
      obtain ⟨c'', hs', hd⟩ := loop pre j (k+1) c' (by omega) (by omega) hc'
      exact ⟨c'', by have := hs.trans hs'; rwa [show 4 + 4 * j = 4 * (j+1) by omega] at this, hd⟩
    · rw [if_neg hlt] at hc'
      have : j = 0 := by omega
      subst this
      exact ⟨c', hs, hc'⟩

/-! ## The whole function -/

theorem duty_contract (c₀ : Core) (ram : Word → BitVec 8) (p : Word) (h : Pre c₀ p) :
    ∃ n m, DetSteps B img n ⟨c₀, ram⟩ m ∧ Post c₀ ram p m := by
  obtain ⟨hpc, harg, hlo, hhi⟩ := h
  -- Prologue: a1 := 0; a2 := a0 + 8.
  have s1 : DetStep B img ⟨c₀, ram⟩ ⟨c₀.wr 11 0 (entry + 2), ram⟩ := by
    refine detStep_of (B := B) (by rw [hpc]; decide) (by rw [hpc]; exact i0) fun o => ?_
    rw [exec_opimm, hpc]; simp [alu]
  generalize hc1 : c₀.wr 11 0 (entry + 2) = c1 at s1
  have p1 : c1.pc = 0x200102a2 := by rw [← hc1]; rfl
  have s2 : DetStep B img ⟨c1, ram⟩ ⟨c1.wr 12 (c1.get 10 + 8) (0x200102a2 + 4), ram⟩ := by
    refine detStep_of (B := B) (by rw [p1]; decide) (by rw [p1]; exact i1) fun o => ?_
    rw [exec_opimm, p1]; rfl
  generalize hc2 : c1.wr 12 (c1.get 10 + 8) (0x200102a2 + 4) = c2 at s2
  have inv0 : Inv c₀ ram p 0 c2 := by
    have g10 : c1.get 10 = p := by rw [← hc1, Core.wr_get_ne _ _ _ _ _ (by decide), harg]
    refine ⟨by rw [← hc2]; rfl, ?_, ?_, ?_, ?_, ?_⟩
    · rw [← hc2, Core.wr_get_ne _ _ _ _ _ (by decide), g10]; simp
    · rw [← hc2, Core.wr_get_ne _ _ _ _ _ (by decide), ← hc1, Core.wr_get_self _ _ _ _ (by decide)]
      simp [sumBytes]
    · rw [← hc2, Core.wr_get_self _ _ _ _ (by decide), g10]
    · intro r a b d e
      rw [← hc2, Core.wr_get_ne _ _ _ _ _ d, ← hc1, Core.wr_get_ne _ _ _ _ _ b]
    · rw [← hc2, ← hc1]; exact (Core.sameCsr_wr _ _ _ _).trans (Core.sameCsr_wr _ _ _ _)
  obtain ⟨c3, hloop, ⟨hpc3, hsum, hframe, hcsr⟩⟩ := loop ⟨hlo, hhi⟩ 8 0 c2 rfl (by decide) inv0
  -- Epilogue: a0 := a1 >> 3; a1 := 93; if !(a0 < 93) then a0 := 93; a0 += 7; ret.
  have hS := sumBytes_le ram p 8
  generalize hSdef : sumBytes ram p 8 = S at hS hsum
  have s4 : DetStep B img ⟨c3, ram⟩ ⟨c3.wr 10 (alu .srl (c3.get 11) 3) (exitPc + 4), ram⟩ :=
    detStep_of (B := B) (by rw [hpc3]; decide) (by rw [hpc3]; exact i6)
      fun o => by rw [exec_opimm, hpc3]; rfl
  generalize hc4 : c3.wr 10 (alu .srl (c3.get 11) 3) (exitPc + 4) = c4 at s4
  have p4 : c4.pc = 0x200102b6 := by rw [← hc4]; rfl
  have v4 : (c4.get 10).toNat = S / 8 := by
    rw [← hc4, Core.wr_get_self _ _ _ _ (by decide), hsum]
    simp [alu]; omega
  have s5 : DetStep B img ⟨c4, ram⟩ ⟨c4.wr 11 (alu .add (c4.get 0) 0x5d) (0x200102b6 + 4), ram⟩ :=
    detStep_of (B := B) (by rw [p4]; decide) (by rw [p4]; exact i7)
      fun o => by rw [exec_opimm, p4]; rfl
  generalize hc5 : c4.wr 11 (alu .add (c4.get 0) 0x5d) (0x200102b6 + 4) = c5 at s5
  have p5 : c5.pc = 0x200102ba := by rw [← hc5]; rfl
  have v5 : c5.get 11 = 0x5d := by rw [← hc5, Core.wr_get_self _ _ _ _ (by decide)]; simp [alu]
  have v5a : (c5.get 10).toNat = S / 8 := by rw [← hc5, Core.wr_get_ne _ _ _ _ _ (by decide), v4]
  -- The clamp: whichever way the branch goes, a0 = min(S/8, 93) before +7.
  have clamp : ∃ c6 : Core, ∃ n, DetSteps B img n ⟨c5, ram⟩ ⟨c6, ram⟩ ∧ c6.pc = 0x200102c2 ∧
      (c6.get 10).toNat = min (S / 8) 93 ∧
      (∀ r : Reg, r ≠ 10 → c6.get r = c5.get r) ∧ c6.sameCsr c5 := by
    by_cases hlt : S / 8 < 93
    · refine ⟨c5.goto 0x200102c2, 1, .single ?_, rfl, ?_, fun r _ => rfl, Core.sameCsr_goto _ _⟩
      · refine detStep_of (B := B) (by rw [p5]; decide) (by rw [p5]; exact i8) fun o => ?_
        rw [exec_branch]
        have : taken .ltu (c5.get 10) (c5.get 11) = true := by
          simp only [taken, v5, BitVec.ult]; rw [v5a]; simp; omega
        rw [if_pos this, p5, jump_ok _ _ (by decide)]; rfl
      · simp only [Core.goto_get]; rw [v5a]; omega
    · refine ⟨(c5.goto 0x200102be).wr 10 (alu .add ((c5.goto 0x200102be).get 0) 0x5d)
          (0x200102be + 4), 2, .step (m₁ := ⟨c5.goto 0x200102be, ram⟩) ?_ (.single ?_), rfl, ?_, ?_, ?_⟩
      · refine detStep_of (B := B) (by rw [p5]; decide) (by rw [p5]; exact i8) fun o => ?_
        rw [exec_branch]
        have : taken .ltu (c5.get 10) (c5.get 11) = false := by
          simp only [taken, v5, BitVec.ult]; rw [v5a]; simp; omega
        rw [if_neg (by simp [this]), p5]; rfl
      · refine detStep_of (B := B) (by simp only [Core.goto_pc]; decide) i9 fun o => ?_
        rw [exec_opimm]; rfl
      · rw [Core.wr_get_self _ _ _ _ (by decide)]; simp [alu]; omega
      · intro r hr; rw [Core.wr_get_ne _ _ _ _ _ hr]; rfl
      · exact (Core.sameCsr_wr _ _ _ _).trans (Core.sameCsr_goto _ _)
  obtain ⟨c6, n6, s6, pc6, v6, f6, csr6⟩ := clamp
  have s7 : DetStep B img ⟨c6, ram⟩ ⟨c6.wr 10 (alu .add (c6.get 10) 7) (0x200102c2 + 2), ram⟩ :=
    detStep_of (B := B) (by rw [pc6]; decide) (by rw [pc6]; exact i10)
      fun o => by rw [exec_opimm, pc6]; rfl
  generalize hc7 : c6.wr 10 (alu .add (c6.get 10) 7) (0x200102c2 + 2) = c7 at s7
  have p7 : c7.pc = 0x200102c4 := by rw [← hc7]; rfl
  have s8 : DetStep B img ⟨c7, ram⟩ ⟨c7.goto ((c7.get 1 + 0) &&& ~~~1), ram⟩ := by
    refine detStep_of (B := B) (by rw [p7]; decide) (by rw [p7]; exact i11) fun o => ?_
    rw [exec_jalr, Core.set_zero, jump_ok _ _ (clear_bit0 _)]; rfl
  have v7 : (c7.get 10).toNat = min (S / 8) 93 + 7 := by
    rw [← hc7, Core.wr_get_self _ _ _ _ (by decide)]; simp [alu]; omega
  -- Registers other than a0-a3 come through every stage unchanged.
  have keep : ∀ r : Reg, r ≠ 10 → r ≠ 11 → r ≠ 12 → r ≠ 13 → c7.get r = c₀.get r := by
    intro r a b d e
    rw [← hc7, Core.wr_get_ne _ _ _ _ _ a, f6 r a, ← hc5, Core.wr_get_ne _ _ _ _ _ b,
      ← hc4, Core.wr_get_ne _ _ _ _ _ a, hframe r a b d e]
  refine ⟨_, _, ((((DetSteps.single s1).trans (.single s2)).trans hloop).trans
    ((DetSteps.single s4).trans ((DetSteps.single s5).trans (s6.trans
      ((DetSteps.single s7).trans (.single s8)))))), ?_⟩
  refine ⟨?_, ?_, ?_, rfl, fun r a b d e => by simp [keep r a b d e], ?_⟩
  · simp only [Core.goto_pc]
    rw [keep 1 (by decide) (by decide) (by decide) (by decide)]; simp
  · simp only [Core.goto_get]; rw [v7, ← hSdef]; unfold spec; omega
  · simp only [Core.goto_get]; rw [v7]; omega
  · refine (Core.sameCsr_goto _ _).trans ?_
    rw [← hc7]; refine (Core.sameCsr_wr _ _ _ _).trans (csr6.trans ?_)
    rw [← hc5, ← hc4]
    exact ((Core.sameCsr_wr _ _ _ _).trans (Core.sameCsr_wr _ _ _ _)).trans hcsr

#print axioms duty_contract

/-! ## Nonvacuity

The precondition is satisfiable and the run is real: from a concrete state
with a window of eight 10s, the function returns 17. -/

def demo : Core :=
  { pc := entry, x := fun r => if r.val = 10 then 0x80000000 else 0, mie_ := false, mpie := false,
    mpp := 3, mieReg := 0, mtvec := 0, mepc := 0, mcause := 0, mscratch := 0, resv := false }

theorem nonvacuous : ∃ n m, DetSteps B img n ⟨demo, fun _ => 10⟩ m ∧ (m.core.get 10).toNat = 17 := by
  obtain ⟨n, m, h, post⟩ := duty_contract demo (fun _ => 10) 0x80000000 ⟨rfl, rfl, by decide, by decide⟩
  exact ⟨n, m, h, by rw [post.result]; decide⟩

end E5R.Hifive1.Duty
