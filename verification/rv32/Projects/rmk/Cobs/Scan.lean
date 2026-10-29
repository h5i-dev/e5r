/-
  `cobs::dec::decode_in_place_report`, first loop (0x8001e03c..0x8001e04e): the
  frame length, i.e. the index of the first zero byte of the buffer, or its
  length if it has none.

    0x8001e03c li a4,0
    0x8001e03e add a3,a1,a4 ; lbu a3,0(a3) ; beqz a3,0x8001e050
    0x8001e048 addi a4,a4,1 ; bne a2,a4,0x8001e03e
    0x8001e04e mv a4,a2                                 (falls to 0x8001e050)

  Original e5r code, Apache-2.0. Every load is a byte of `[a1, a1 + a2)`.
-/
import Projects.rmk.Cobs.Basic

set_option maxRecDepth 100000

namespace E5R.Rmk.Cobs
open E5R E5R.Rmk E5R.Rmk.CobsFetch

/-- Byte `j` of the buffer at `buf` in RAM `S`. -/
def bufByte (S : Word → BitVec 8) (buf : Word) (j : Nat) : Nat := (S (buf + BitVec.ofNat 32 j)).toNat

/-- The first `j ≥ i`, `j < len`, with a zero byte; `len` if there is none. -/
def firstZero (byte : Nat → Nat) (i len : Nat) : Nat :=
  if i < len then (if byte i = 0 then i else firstZero byte (i + 1) len) else len
termination_by len - i

theorem firstZero_eq (byte : Nat → Nat) (i len : Nat) :
    firstZero byte i len = if i < len then (if byte i = 0 then i else firstZero byte (i + 1) len) else len := by
  rw [firstZero]

/-- What the first zero is: between `i` and `len`, every byte before it non-zero,
    and a zero byte there unless it is `len`. -/
theorem firstZero_spec (byte : Nat → Nat) (len : Nat) : ∀ k i, i + k = len →
    i ≤ firstZero byte i len ∧ firstZero byte i len ≤ len ∧
    (∀ j, i ≤ j → j < firstZero byte i len → byte j ≠ 0) ∧
    (firstZero byte i len < len → byte (firstZero byte i len) = 0)
  | 0, i, h => by
    rw [firstZero_eq, if_neg (by omega)]
    exact ⟨by omega, Nat.le_refl _, fun j h1 h2 => absurd h2 (by omega), fun h => absurd h (by omega)⟩
  | k+1, i, h => by
    rw [firstZero_eq, if_pos (by omega)]
    by_cases hb : byte i = 0
    · rw [if_pos hb]; exact ⟨Nat.le_refl _, by omega, fun j h1 h2 => absurd h2 (by omega), fun _ => hb⟩
    · rw [if_neg hb]
      obtain ⟨a, b, c, d⟩ := firstZero_spec byte len k (i + 1) (by omega)
      refine ⟨by omega, b, fun j h1 h2 => ?_, d⟩
      rcases Nat.eq_or_lt_of_le h1 with e | e
      · subst e; exact hb
      · exact c j e h2

/-- A zero-extended byte load. -/
theorem lbu_val (S : Word → BitVec 8) (a : Word) :
    extend .b false (ramRead S a .b) = BitVec.ofNat 32 (S a).toNat := by
  have := (S a).isLt
  apply BitVec.eq_of_toNat_eq
  simp only [extend, ramRead, BitVec.toNat_and, BitVec.toNat_ofNat]
  rw [show (0xff : Word).toNat = 255 from rfl]
  rw [Nat.mod_eq_of_lt (by omega : (S a).toNat < 2 ^ 32)]
  rw [show (255 : Nat) = 2 ^ 8 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt this]

theorem byte_eq0 (b : BitVec 8) : (BitVec.ofNat 32 b.toNat = 0) ↔ b.toNat = 0 := by
  have := b.isLt
  constructor
  · intro h; have := congrArg BitVec.toNat h; simp at this; omega
  · intro h; rw [h]; rfl

theorem ofNat_toNat (x : Word) : BitVec.ofNat 32 x.toNat = x := by simp

/-- One byte of the scan: load buf[i], and either stop at 0x8001e050 (zero) or
    increment a4 and reach the back edge 0x8001e04a. -/
theorem scan_head (buf : Word) (len : Nat) (hbuf : 0x80029bc8 ≤ buf.toNat ∧ buf.toNat + len ≤ 0x81000000)
    (d : Core) (S : Word → BitVec 8) (hpc : d.pc = 0x8001e03e) (hq : Quiet d) (h11 : d.get 11 = buf)
    (hi : (d.get 14).toNat < len) :
    (bufByte S buf (d.get 14).toNat = 0 → ∃ e, QRun B img 3 ⟨d, S⟩ ⟨e, S⟩ ∧ e.pc = 0x8001e050 ∧
      e.sameCsr d ∧ ∀ r : Reg, r ≠ 13 → e.get r = d.get r) ∧
    (bufByte S buf (d.get 14).toNat ≠ 0 → ∃ e, QRun B img 4 ⟨d, S⟩ ⟨e, S⟩ ∧ e.pc = 0x8001e04a ∧
      e.get 14 = d.get 14 + 1 ∧ e.sameCsr d ∧ ∀ r : Reg, r ≠ 13 → r ≠ 14 → e.get r = d.get r) := by
  let d1 := d.wr 13 (alu .add (d.get 11) (d.get 14)) 0x8001e042
  let d2 := d1.wr 13 (extend .b false (ramRead S (d1.get 13 + 0x0#32) .b)) 0x8001e046
  have v13 : d1.get 13 = buf + BitVec.ofNat 32 (d.get 14).toNat := by
    simp [d1, Core.wr_get_self, alu, h11]
  have v2 : d2.get 13 = BitVec.ofNat 32 (bufByte S buf (d.get 14).toNat) := by
    simp only [d2, Core.wr_get_self _ (13 : Reg) _ _ (by decide), v13, BitVec.add_zero, lbu_val, bufByte]
  have k1 : d1.sameCsr d := Core.sameCsr_wr _ _ _ _
  have k2 : d2.sameCsr d := (Core.sameCsr_wr _ _ _ _).trans k1
  have q : ∀ e : Core, e.sameCsr d → Quiet e := fun e h => Quiet.of_sameCsr h hq
  have s1 : DetStep B img ⟨d, S⟩ ⟨d1, S⟩ := dstep f8001e03e hpc (by rw [exec_op, hpc]; rfl)
  have s2 : DetStep B img ⟨d1, S⟩ ⟨d2, S⟩ :=
    dstep_load f8001e042 rfl (exec_load _ _ _ _ _ _ _) (Nat.mod_one _)
      (by show B.inRam _ 1 = true; rw [v13, BitVec.add_zero, B_ram]; constructor <;> bv_omega) rfl
  have g2 : ∀ r : Reg, r ≠ 13 → d2.get r = d.get r := fun r h => by simp [d2, d1, Core.wr_get_ne, h]
  constructor
  · intro hz
    have s3 : DetStep B img ⟨d2, S⟩ ⟨d2.goto 0x8001e050, S⟩ :=
      dstep f8001e046 rfl (by
        rw [exec_branch, if_pos (by simp [taken, v2, hz])]
        exact jump_ok _ _ (by show (0x8001e050 : Word).getLsbD 0 = false; decide))
    exact ⟨_, .step hq s1 (.step (q _ k1) s2 (.single (q _ k2) s3)), rfl, (Core.sameCsr_goto _ _).trans k2,
      fun r h => by simp only [Core.goto_get]; exact g2 r h⟩
  · intro hz
    have hz' : ¬ (BitVec.ofNat 32 (bufByte S buf (d.get 14).toNat) = 0) := by
      unfold bufByte at hz ⊢; rw [byte_eq0]; exact hz
    let d3 := d2.goto 0x8001e048
    let d4 := d3.wr 14 (alu .add (d3.get 14) 0x1#32) 0x8001e04a
    have s3 : DetStep B img ⟨d2, S⟩ ⟨d3, S⟩ :=
      dstep f8001e046 rfl (by rw [exec_branch, if_neg (by simp only [taken, v2, beq_iff_eq]; exact hz')]; rfl)
    have s4 : DetStep B img ⟨d3, S⟩ ⟨d4, S⟩ := dstep f8001e048 rfl (by rw [exec_opimm]; rfl)
    have k3 : d3.sameCsr d := (Core.sameCsr_goto _ _).trans k2
    refine ⟨d4, .step hq s1 (.step (q _ k1) s2 (.step (q _ k2) s3 (.single (q _ k3) s4))), rfl,
      ?_, (Core.sameCsr_wr _ _ _ _).trans k3, fun r h13 h14 => ?_⟩
    · simp [d4, d3, Core.wr_get_self, alu, g2 14 (by decide)]
    · simp only [d4, d3, Core.wr_get_ne _ _ _ _ _ h14, Core.goto_get]; exact g2 r h13

/-- **The scan loop** from 0x8001e03e with a4 = i < len: it reaches 0x8001e050 with
    a4 = the first zero index from `i`, RAM unchanged, only a3 and a4 written. -/
theorem scan (buf : Word) (len : Nat) (hbuf : B.inRam buf len = true) :
    ∀ (k : Nat) (d : Core) (S : Word → BitVec 8), d.pc = 0x8001e03e → Quiet d →
      d.get 11 = buf → (d.get 12).toNat = len → (d.get 14).toNat + k + 1 = len →
      ∃ n e, QRun B img n ⟨d, S⟩ ⟨e, S⟩ ∧ e.pc = 0x8001e050 ∧
        (e.get 14).toNat = firstZero (bufByte S buf) (d.get 14).toNat len ∧ e.sameCsr d ∧
        ∀ r : Reg, r ≠ 13 → r ≠ 14 → e.get r = d.get r := by
  rw [B_ram] at hbuf
  intro k
  induction k with
  | zero =>
    intro d S hpc hq h11 h12 hk
    obtain ⟨hz, hnz⟩ := scan_head buf len hbuf d S hpc hq h11 (by omega)
    by_cases hb : bufByte S buf (d.get 14).toNat = 0
    · obtain ⟨e, hr, hpc', hcs, hg⟩ := hz hb
      refine ⟨_, e, hr, hpc', ?_, hcs, fun r h13 _ => hg r h13⟩
      rw [hg 14 (by decide), firstZero_eq, if_pos (by omega), if_pos hb]
    · obtain ⟨e, hr, hpc', h14, hcs, hg⟩ := hnz hb
      -- a4 + 1 = len: bne not taken, then mv a4, a2.
      have heq : e.get 12 = e.get 14 := by
        rw [hg 12 (by decide) (by decide), h14]
        apply BitVec.eq_of_toNat_eq; rw [h12]; simp; omega
      have hne : ¬ (taken .ne (e.get 12) (e.get 14) = true) := by simp [taken, heq]
      let e1 := e.goto 0x8001e04e
      let e2 := e1.wr 14 (alu .add (e1.get 0) (e1.get 12)) 0x8001e050
      have s1 : DetStep B img ⟨e, S⟩ ⟨e1, S⟩ := dstep f8001e04a hpc' (by rw [exec_branch, if_neg hne, hpc']; rfl)
      have s2 : DetStep B img ⟨e1, S⟩ ⟨e2, S⟩ := dstep f8001e04e rfl (by rw [exec_op]; rfl)
      have q := Quiet.of_sameCsr hcs hq
      refine ⟨_, e2, hr.trans (.step q s1 (.single (Quiet.of_sameCsr (Core.sameCsr_goto _ _) q) s2)), rfl,
        ?_, (Core.sameCsr_wr _ _ _ _).trans ((Core.sameCsr_goto _ _).trans hcs), fun r h13 h14 => ?_⟩
      · have : (e2.get 14).toNat = len := by
          simp [e2, e1, Core.wr_get_self, alu, hg 12 (by decide) (by decide), h12]
        rw [this, firstZero_eq, if_pos (by omega), if_neg hb, firstZero_eq, if_neg (by omega)]
      · simp only [e2, e1, Core.wr_get_ne _ _ _ _ _ h14, Core.goto_get]; exact hg r h13 h14
  | succ k ih =>
    intro d S hpc hq h11 h12 hk
    obtain ⟨hz, hnz⟩ := scan_head buf len hbuf d S hpc hq h11 (by omega)
    by_cases hb : bufByte S buf (d.get 14).toNat = 0
    · obtain ⟨e, hr, hpc', hcs, hg⟩ := hz hb
      refine ⟨_, e, hr, hpc', ?_, hcs, fun r h13 _ => hg r h13⟩
      rw [hg 14 (by decide), firstZero_eq, if_pos (by omega), if_pos hb]
    · obtain ⟨e, hr, hpc', h14, hcs, hg⟩ := hnz hb
      have hi1 : (e.get 14).toNat = (d.get 14).toNat + 1 := by rw [h14]; bv_omega
      have ht : taken .ne (e.get 12) (e.get 14) = true := by
        simp only [taken, hg 12 (by decide) (by decide), bne_iff_ne, ne_eq]
        intro he; have := congrArg BitVec.toNat he; omega
      let e1 := e.goto 0x8001e03e
      have s1 : DetStep B img ⟨e, S⟩ ⟨e1, S⟩ := dstep f8001e04a hpc' (by
        rw [exec_branch, if_pos ht, hpc']
        exact jump_ok _ _ (by show (0x8001e03e : Word).getLsbD 0 = false; decide))
      have q := Quiet.of_sameCsr hcs hq
      have k1 : e1.sameCsr d := (Core.sameCsr_goto _ _).trans hcs
      obtain ⟨n, f, hr2, hpc2, h14f, hcs2, hg2⟩ := ih e1 S rfl (Quiet.of_sameCsr k1 hq)
        (by simp only [e1, Core.goto_get]; rw [hg 11 (by decide) (by decide), h11])
        (by simp only [e1, Core.goto_get]; rw [hg 12 (by decide) (by decide), h12])
        (by simp only [e1, Core.goto_get]; omega)
      refine ⟨_, f, hr.trans (.step q s1 hr2), hpc2, ?_, hcs2.trans k1, fun r h13 h14 => ?_⟩
      · rw [h14f]; simp only [e1, Core.goto_get]
        rw [hi1, firstZero_eq ((bufByte S buf)) (d.get 14).toNat, if_pos (by omega), if_neg hb]
      · rw [hg2 r h13 h14]; simp only [e1, Core.goto_get]; exact hg r h13 h14

end E5R.Rmk.Cobs
