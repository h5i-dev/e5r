import E5R.Spec

/-
Word arithmetic lemmas for proofs about compiled code. They are stated so
that a proof rewrites with them instead of calling `simp` on `toNat` of an
expression with a 64-bit literal in it, which can make `simp` (and then the
kernel) evaluate Nat arithmetic on that literal one successor at a time.
-/
namespace E5R

theorem allOnes_toNat : (18446744073709551615#64).toNat = 18446744073709551615 := rfl

/-- `addi rd, rs, -1` on a counter. -/
theorem ofNat_add_allOnes (m : Nat) (hm : 1 ≤ m) (h : m < 2 ^ 64) :
    BitVec.ofNat 64 m + 18446744073709551615#64 = BitVec.ofNat 64 (m - 1) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, allOnes_toNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt h, Nat.mod_eq_of_lt (a := m - 1) (by omega)]
  omega

/-- Adding a small literal to a word built from a natural number. -/
theorem ofNat_add_lit (m n : Nat) :
    BitVec.ofNat 64 m + BitVec.ofNat 64 n = BitVec.ofNat 64 (m + n) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  omega

/-- A pointer advanced by `n` from `a + m`. -/
theorem add_ofNat_add (a : Word) (m n : Nat) :
    a + BitVec.ofNat 64 m + BitVec.ofNat 64 n = a + BitVec.ofNat 64 (m + n) := by
  rw [BitVec.add_assoc, ofNat_add_lit]

theorem toNat_ofNat_of_lt {m : Nat} (h : m < 2 ^ 64) : (BitVec.ofNat 64 m).toNat = m := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

/-- `(a + m) - a`, for a region check. -/
theorem add_ofNat_sub_toNat (a : Word) {m : Nat} (h : m < 2 ^ 64) :
    (a + BitVec.ofNat 64 m - a).toNat = m := by
  have : a + BitVec.ofNat 64 m - a = BitVec.ofNat 64 m := by bv_omega
  rw [this, toNat_ofNat_of_lt h]

/-- `a + m` is `n`-aligned when `a` and `m` are (`n` divides 2^64). -/
theorem aligned_add_ofNat {a : Word} {m n : Nat} (ha : aligned a n) (hm : m % n = 0)
    (hn : 2 ^ 64 % n = 0) : aligned (a + BitVec.ofNat 64 m) n := by
  unfold aligned at *
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_mod_of_dvd _ (Nat.dvd_of_mod_eq_zero hn)]
  rw [Nat.add_mod, ha, Nat.zero_add, Nat.mod_mod_of_dvd _ (Nat.dvd_of_mod_eq_zero hn), hm,
    Nat.zero_mod]

/-- A word is zero exactly when the natural number it was built from is. -/
theorem ofNat_eq_zero_iff {m : Nat} (h : m < 2 ^ 64) : BitVec.ofNat 64 m = (0 : Word) ↔ m = 0 := by
  constructor
  · intro e; have := congrArg BitVec.toNat e; rw [toNat_ofNat_of_lt h] at this; exact this
  · intro e; subst e; rfl

end E5R
