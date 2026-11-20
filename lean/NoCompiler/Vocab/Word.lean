import NoCompiler.Auto

/-
Spec vocabulary: fixed-width arithmetic facts.

The step tactics and `nocompiler_auto` put words in the normal form
`BitVec.ofNat 64 e` (NoCompiler/Arith.lean, the `nocompiler_nat` lemmas of
NoCompiler/Auto.lean). What is here is what specifications and their
verification conditions need on top: bytes as numbers, the sign bit of a
small result, and alignment of a frame below an aligned stack pointer.
-/
namespace NoCompiler.Vocab

/-! ## Bytes -/

theorem byte_toNat_lt (b : Byte) : b.toNat < 256 := b.isLt

theorem byte_eq_zero_of_toNat {b : Byte} (h : b.toNat = 0) : b = 0 := BitVec.eq_of_toNat_eq h

theorem byte_toNat_ne_zero {b : Byte} (h : b ≠ 0) : b.toNat ≠ 0 :=
  fun e => h (byte_eq_zero_of_toNat e)

theorem byte_ne_zero_of_toNat {b : Byte} (h : ¬ b.toNat = 0) : b ≠ 0 :=
  fun e => h (by rw [e]; rfl)

/-- A byte compared with zero by `==` (the form of a `findIdx` test). -/
theorem byte_beq_zero_iff (b : Byte) : (b == 0) = true ↔ b.toNat = 0 := by
  constructor
  · intro h; rw [beq_iff_eq] at h; rw [h]; rfl
  · intro h; rw [beq_iff_eq]; exact byte_eq_zero_of_toNat h

theorem byte_beq_zero_false (b : Byte) : (b == 0) = false ↔ ¬ b.toNat = 0 := by
  rw [← Bool.not_eq_true, byte_beq_zero_iff]

/-! ## The sign bit -/

/-- `srli x, 63` of a non-negative result. -/
theorem ofNat_ushiftRight_63 {x : Nat} (h : x < 2 ^ 63) : (BitVec.ofNat 64 x) >>> 63 = 0 := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, toNat_ofNat_of_lt (by omega), Nat.shiftRight_eq_div_pow]
  simp; omega

/-- `srli x, 63` of a negative result `-e`, `1 ≤ e ≤ 2^63`. -/
theorem neg_ofNat_ushiftRight_63 {e : Nat} (h1 : 1 ≤ e) (h2 : e ≤ 2 ^ 63) :
    (-(BitVec.ofNat 64 e)) >>> 63 = 1 := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_neg, toNat_ofNat_of_lt (by omega)]
  simp only [Nat.shiftRight_eq_div_pow]
  rw [Nat.mod_eq_of_lt (by omega)]
  simp; omega

/-! ## Alignment -/

/-- A frame base `sp - k` below an aligned `sp`. -/
theorem aligned_sub_ofNat {a : Word} {m n : Nat} (ha : aligned a n) (hm : m % n = 0)
    (hn : 2 ^ 64 % n = 0) (hlt : m < 2 ^ 64) : aligned (a - BitVec.ofNat 64 m) n := by
  unfold aligned at *
  have hd : n ∣ 2 ^ 64 := Nat.dvd_of_mod_eq_zero hn
  rw [BitVec.toNat_sub, Nat.mod_mod_of_dvd _ hd, toNat_ofNat_of_lt hlt]
  have hm' : n ∣ m := Nat.dvd_of_mod_eq_zero hm
  have ha' : n ∣ a.toNat := Nat.dvd_of_mod_eq_zero ha
  exact Nat.mod_eq_zero_of_dvd (Nat.dvd_add (Nat.dvd_sub hd hm') ha')

/-- Alignment to `n` gives alignment to any divisor of `n`. -/
theorem aligned_of_dvd {a : Word} {n k : Nat} (h : aligned a n) (hk : k ∣ n) : aligned a k := by
  unfold aligned at *
  exact Nat.mod_eq_zero_of_dvd (Nat.dvd_trans hk (Nat.dvd_of_mod_eq_zero h))

end NoCompiler.Vocab
