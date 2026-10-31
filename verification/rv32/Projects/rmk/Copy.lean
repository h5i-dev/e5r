/-
  The byte copies memmove's loops perform, and what they mean.

  Original e5r code, Apache-2.0.

  `fwd ram s d k` and `bwd ram p q k` are exactly what the emitted byte
  loops do to RAM (read a byte, write it, step the pointers); they are
  defined by the loop structure, not by the intended result. `fwd_spec`
  and `bwd_spec` then prove the memmove result pointwise, overlapping
  ranges included, when the direction fits the overlap.
-/
import Theories.Logic

set_option maxRecDepth 100000

namespace E5R.Rmk
open E5R

def fwd : (Word → BitVec 8) → Word → Word → Nat → (Word → BitVec 8)
  | ram, _, _, 0 => ram
  | ram, s, d, k+1 => fwd (ramPut ram d (ram s)) (s + 1) (d + 1) k

def bwd : (Word → BitVec 8) → Word → Word → Nat → (Word → BitVec 8)
  | ram, _, _, 0 => ram
  | ram, p, q, k+1 => bwd (ramPut ram (q + 0xffffffff#32) (ram p)) (p + 0xffffffff#32) (q + 0xffffffff#32) k

/-- Writing a byte just loaded (zero-extended) stores that byte. -/
theorem copyByte (ram : Word → BitVec 8) (a d : Word) :
    ramWrite ram d (extend .b false (ramRead ram a .b)) .b = ramPut ram d (ram a) := by
  simp only [ramWrite]
  congr 1
  apply BitVec.eq_of_toNat_eq
  have := (ram a).isLt
  simp only [byteOf, extend, ramRead, BitVec.toNat_and, BitVec.toNat_ofNat, Nat.pow_zero, Nat.div_one]
  rw [show BitVec.toNat (255 : Word) = 2 ^ 8 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  omega

/-- Forward copy of `n` bytes: correct when the destination is not inside
    the source just above it (d ≤ s, or the ranges are disjoint). -/
theorem fwd_spec : ∀ (n : Nat) (ram : Word → BitVec 8) (s d x : Word),
    d.toNat + n < 2 ^ 32 → s.toNat + n < 2 ^ 32 → (d.toNat ≤ s.toNat ∨ s.toNat + n ≤ d.toNat) →
    fwd ram s d n x = if d.toNat ≤ x.toNat ∧ x.toNat < d.toNat + n then ram (s + (x - d)) else ram x
  | 0, ram, s, d, x, _, _, _ => by simp [fwd]; omega
  | n+1, ram, s, d, x, hd, hs, hdir => by
    simp only [fwd]
    rw [fwd_spec n _ (s + 1) (d + 1) x (by bv_omega) (by bv_omega) (by bv_omega)]
    simp only [ramPut]
    have e1 : (d + 1).toNat = d.toNat + 1 := by bv_omega
    rw [e1]
    repeat' split
    all_goals first | (exfalso; bv_omega) | exact congrArg ram (by bv_omega)

/-- Backward copy of `k` bytes, reading down from `p` and writing down from
    `q - 1`: correct when the source lies below the destination (`p < q`). -/
theorem bwd_spec : ∀ (k : Nat) (ram : Word → BitVec 8) (p q x : Word),
    k ≤ p.toNat → p.toNat < q.toNat →
    bwd ram p q k x = if q.toNat - k ≤ x.toNat ∧ x.toNat < q.toNat then ram (p - (q - 1 - x)) else ram x
  | 0, ram, p, q, x, _, _ => by simp [bwd]; omega
  | k+1, ram, p, q, x, hp, hpq => by
    simp only [bwd]
    rw [bwd_spec k _ (p + 0xffffffff#32) (q + 0xffffffff#32) x (by bv_omega) (by bv_omega)]
    simp only [ramPut]
    have eq1 : (q + 0xffffffff#32).toNat = q.toNat - 1 := by bv_omega
    rw [eq1]
    repeat' split
    all_goals first | (exfalso; bv_omega) | exact congrArg ram (by bv_omega)

/-! ## Composition and word copies (the n ≥ 16 paths) -/

/-- A forward copy splits into two consecutive ones. -/
theorem fwd_add : ∀ (a b : Nat) (ram : Word → BitVec 8) (s d : Word),
    fwd ram s d (a + b) = fwd (fwd ram s d a) (s + BitVec.ofNat 32 a) (d + BitVec.ofNat 32 a) b
  | 0, b, ram, s, d => by simp [fwd]
  | a+1, b, ram, s, d => by
    rw [show a + 1 + b = (a + b) + 1 by omega]
    simp only [fwd]
    rw [fwd_add a b]
    congr 1 <;> bv_omega

/-- The word loop: `sw (lw src) dst`, then both pointers + 4, `j` times. -/
def words : (Word → BitVec 8) → Word → Word → Nat → (Word → BitVec 8)
  | ram, _, _, 0 => ram
  | ram, s, d, j+1 => words (ramWrite ram d (ramRead ram s .w) .w) (s + 4) (d + 4) j

theorem byte_read (ram : Word → BitVec 8) (s : Word) :
    byteOf (ramRead ram s .w) 0 = ram s ∧ byteOf (ramRead ram s .w) 1 = ram (s + 1) ∧
    byteOf (ramRead ram s .w) 2 = ram (s + 2) ∧ byteOf (ramRead ram s .w) 3 = ram (s + 3) := by
  have h0 := (ram s).isLt; have h1 := (ram (s + 1)).isLt
  have h2 := (ram (s + 2)).isLt; have h3 := (ram (s + 3)).isLt
  refine ⟨?_, ?_, ?_, ?_⟩ <;> apply BitVec.eq_of_toNat_eq <;>
    simp only [byteOf, ramRead, BitVec.toNat_ofNat] <;> omega

/-- One word copy, pointwise: it reads the whole word before writing, so
    it is the memmove of 4 bytes whatever the overlap. -/
theorem word_spec (ram : Word → BitVec 8) (s d x : Word) (hd : d.toNat + 4 < 2 ^ 32) :
    ramWrite ram d (ramRead ram s .w) .w x =
      if d.toNat ≤ x.toNat ∧ x.toNat < d.toNat + 4 then ram (s + (x - d)) else ram x := by
  obtain ⟨b0, b1, b2, b3⟩ := byte_read ram s
  simp only [ramWrite, ramPut, b0, b1, b2, b3]
  repeat' split
  all_goals first | (exfalso; bv_omega) | exact congrArg ram (by bv_omega) | rfl

/-- The word loop is a forward copy of `4 j` bytes when the direction fits. -/
theorem words_eq_fwd : ∀ (j : Nat) (ram : Word → BitVec 8) (s d : Word),
    d.toNat + 4 * j < 2 ^ 32 → s.toNat + 4 * j < 2 ^ 32 →
    (d.toNat ≤ s.toNat ∨ s.toNat + 4 ≤ d.toNat) →
    words ram s d j = fwd ram s d (4 * j)
  | 0, ram, s, d, _, _, _ => rfl
  | j+1, ram, s, d, hd, hs, hdir => by
    simp only [words]
    rw [words_eq_fwd j _ (s + 4) (d + 4) (by bv_omega) (by bv_omega) (by bv_omega),
      show 4 * (j + 1) = 4 + 4 * j by omega, fwd_add 4 (4 * j)]
    have hw : ramWrite ram d (ramRead ram s .w) .w = fwd ram s d 4 := by
      funext x
      rw [word_spec _ _ _ _ (by omega), fwd_spec _ _ _ _ _ (by omega) (by omega) hdir]
    rw [hw]; rfl

/-! ## Backward composition and word copies -/

/-- A backward copy splits into two consecutive ones (top part first). -/
theorem bwd_add : ∀ (a b : Nat) (ram : Word → BitVec 8) (p q : Word),
    bwd ram p q (a + b) = bwd (bwd ram p q a) (p - BitVec.ofNat 32 a) (q - BitVec.ofNat 32 a) b
  | 0, b, ram, p, q => by simp [bwd]
  | a+1, b, ram, p, q => by
    rw [show a + 1 + b = (a + b) + 1 by omega]
    simp only [bwd]
    rw [bwd_add a b, show p + 0xffffffff#32 - BitVec.ofNat 32 a = p - BitVec.ofNat 32 (a + 1) by bv_omega,
      show q + 0xffffffff#32 - BitVec.ofNat 32 a = q - BitVec.ofNat 32 (a + 1) by bv_omega]

/-- The backward word loop: `sw (lw p) (q - 4)`, then both pointers - 4, `j` times. -/
def wordsB : (Word → BitVec 8) → Word → Word → Nat → (Word → BitVec 8)
  | ram, _, _, 0 => ram
  | ram, p, q, j+1 => wordsB (ramWrite ram (q + 0xfffffffc#32) (ramRead ram p .w) .w) (p + 0xfffffffc#32)
      (q + 0xfffffffc#32) j

/-- The backward word loop is a backward byte copy of `4 j` bytes, reading
    down from `p + 3`, when the source lies below the destination. -/
theorem wordsB_eq_bwd : ∀ (j : Nat) (ram : Word → BitVec 8) (p q : Word),
    4 * j ≤ q.toNat → 4 * j ≤ p.toNat + 3 → p.toNat + 4 < 2 ^ 32 → p.toNat + 4 ≤ q.toNat →
    wordsB ram p q j = bwd ram (p + 3) q (4 * j)
  | 0, ram, p, q, _, _, _, _ => rfl
  | j+1, ram, p, q, h1, h2, h3, h4 => by
    simp only [wordsB]
    rw [show 4 * (j + 1) = 4 + 4 * j by omega, bwd_add 4 (4 * j)]
    by_cases hj : j = 0
    · subst hj
      simp only [wordsB, bwd]
      funext x
      rw [word_spec _ _ _ _ (by bv_omega)]
      have := bwd_spec 4 ram (p + 3) q x (by bv_omega) (by bv_omega)
      simp only [bwd] at this
      rw [this]
      split <;> split <;> first | (exfalso; bv_omega) | (refine congrArg ram ?_; bv_omega) | rfl
    · rw [wordsB_eq_bwd j _ _ _ (by bv_omega) (by bv_omega) (by bv_omega) (by bv_omega)]
      have hw : ramWrite ram (q + 0xfffffffc#32) (ramRead ram p .w) .w = bwd ram (p + 3) q 4 := by
        funext x
        rw [word_spec _ _ _ _ (by bv_omega), bwd_spec 4 ram (p + 3) q x (by bv_omega) (by bv_omega)]
        split <;> split <;> first | (exfalso; bv_omega) | (refine congrArg ram ?_; bv_omega) | rfl
      rw [hw, show p + 0xfffffffc#32 + 3 = p + 3 - BitVec.ofNat 32 4 by bv_omega,
        show q + 0xfffffffc#32 = q - BitVec.ofNat 32 4 by bv_omega]

end E5R.Rmk
