import NoCompiler.Arith

/-
Memory lemmas for proofs about compiled code: a load after a store, stores
outside a region, and arrays of words.
-/
namespace NoCompiler

theorem mod_pow_succ_256 (v n : Nat) :
    v % 256 + 256 * (v / 256 % 256 ^ n) = v % 256 ^ (n + 1) := by
  rw [Nat.pow_succ', Nat.mod_mul]

/-- Reading back the `n` bytes just stored. -/
theorem readLE_writeLE_same (m : Word → Byte) (a : Word) (v : Nat) {n : Nat} (hn : n ≤ 8) :
    readLE (writeLE m a v n) a n = v % 256 ^ n := by
  induction n generalizing a v with
  | zero => simp [readLE, Nat.mod_one]
  | succ n ih =>
    simp only [readLE, writeLE, ite_true]
    have hc : readLE (fun x => if x = a then BitVec.ofNat 8 v else writeLE m (a + 1) (v / 256) n x)
        (a + 1) n = readLE (writeLE m (a + 1) (v / 256) n) (a + 1) n := by
      apply readLE_congr
      intro k hk
      have : a + 1 + BitVec.ofNat 64 k ≠ a := by
        intro e
        have := congrArg BitVec.toNat (show a + 1 + BitVec.ofNat 64 k - a = 0 by rw [e]; simp)
        have e2 : a + 1 + BitVec.ofNat 64 k - a = BitVec.ofNat 64 (1 + k) := by
          apply BitVec.eq_of_toNat_eq; simp; omega
        rw [e2, toNat_ofNat_of_lt (by omega)] at this
        simp at this
      simp only [ite_eq_right_iff]
      intro e; exact absurd e this
    rw [hc, ih _ _ (by omega), BitVec.toNat_ofNat]
    exact mod_pow_succ_256 v n

theorem read64_writeLE_same (m : Word → Byte) (a : Word) (v : Word) :
    read64 (writeLE m a v.toNat 8) a = v := by
  unfold read64
  rw [readLE_writeLE_same m a v.toNat (by omega)]
  apply BitVec.eq_of_toNat_eq
  have h64 : (256 : Nat) ^ 8 = 2 ^ 64 := rfl
  rw [BitVec.toNat_ofNat, h64, Nat.mod_mod, Nat.mod_eq_of_lt v.isLt]

/-- A store to one region leaves memory outside it alone. -/
theorem writeLE_of_not_mem {r : Region} {m : Word → Byte} {b : Word} {v n : Nat} {x : Word}
    (hc : r.covers b n) (hx : ¬ r.mem x) : writeLE m b v n x = m x :=
  writeLE_other m b v n x (Nat.le_of_not_lt fun h => hx (Region.covers_mem hc h))

/-- Two 8-byte slots at offsets `i` and `j` from the same base do not overlap. -/
theorem read64_writeLE_other (m : Word → Byte) (base : Word) (v : Nat) {i j : Nat}
    (hi : i < 2 ^ 32) (hj : j < 2 ^ 32) (hij : i + 8 ≤ j ∨ j + 8 ≤ i) :
    read64 (writeLE m (base + BitVec.ofNat 64 j) v 8) (base + BitVec.ofNat 64 i) =
      read64 m (base + BitVec.ofNat 64 i) := by
  unfold read64
  apply congrArg (BitVec.ofNat 64)
  apply readLE_congr
  intro k hk
  apply writeLE_other
  have e : base + BitVec.ofNat 64 i + BitVec.ofNat 64 k - (base + BitVec.ofNat 64 j) =
      BitVec.ofNat 64 (i + k) - BitVec.ofNat 64 j := by bv_omega
  rw [e, BitVec.toNat_sub, toNat_ofNat_of_lt (by omega), toNat_ofNat_of_lt (by omega)]
  omega

theorem readBytes_congr {m m' : Word → Byte} {a : Word} {n : Nat}
    (h : ∀ k, k < n → m (a + BitVec.ofNat 64 k) = m' (a + BitVec.ofNat 64 k)) :
    readBytes m a n = readBytes m' a n := by
  induction n generalizing a with
  | zero => rfl
  | succ n ih =>
    simp only [readBytes]
    have h0 := h 0 (by omega)
    simp only [BitVec.add_zero] at h0
    rw [h0, ih]
    intro k hk
    have e : a + 1 + BitVec.ofNat 64 k = a + BitVec.ofNat 64 (k + 1) := by
      apply BitVec.eq_of_toNat_eq; simp; omega
    rw [e]; exact h (k + 1) (by omega)

/-- Memory holds `xs` as consecutive little-endian words from `a`. -/
def arr64 (m : Word → Byte) (a : Word) (xs : List Word) : Prop :=
  ∀ i (h : i < xs.length), read64 m (a + BitVec.ofNat 64 (8 * i)) = xs[i]

/-- The region `arr64` reads. -/
def arrRegion (a : Word) (xs : List Word) : Region := ⟨a, 8 * xs.length⟩

/-- An array survives any change to memory outside it. -/
theorem arr64_congr {m m' : Word → Byte} {a : Word} {xs : List Word}
    (hlen : 8 * xs.length < 2 ^ 64) (h : arr64 m a xs)
    (hm : ∀ x, (arrRegion a xs).mem x → m' x = m x) : arr64 m' a xs := by
  intro i hi
  rw [← h i hi]
  unfold read64
  apply congrArg (BitVec.ofNat 64)
  apply readLE_congr
  intro k hk
  apply hm
  show (_ - a).toNat < 8 * xs.length
  have e : a + BitVec.ofNat 64 (8 * i) + BitVec.ofNat 64 k - a = BitVec.ofNat 64 (8 * i + k) := by
    bv_omega
  rw [e, toNat_ofNat_of_lt (by omega)]
  omega

end NoCompiler
