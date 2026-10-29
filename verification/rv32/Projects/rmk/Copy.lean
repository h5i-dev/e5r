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

end E5R.Rmk
