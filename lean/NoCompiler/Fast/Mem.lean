import NoCompiler.Machine

/-
Word-level memory for proofs (docs/design/prior-art-others.md, "Implementation
plan", step 1).

The trusted memory is a function `Word → Byte`, read and written a byte at a
time (`readLE`, `writeLE`, NoCompiler/Machine.lean). A proof that steps
through stores and loads with those definitions ends up with byte-level
terms in its goals. Here memory is a base function plus a list of word-level
writes, newest first, and a read at word level (`FMem.read`) looks through
the writes: the written value when it reads exactly what a write wrote, the
older memory when the two ranges are disjoint (decided on `toNat`, as
LNSym's `simp_mem` does), and the byte-level read otherwise. `FMem.read_eq`
proves it equal to the trusted `readLE` of the memory the writes describe,
once; nothing here is trusted.
-/
namespace NoCompiler.Fast

/-! ## Two facts about the trusted byte-level memory -/

/-- A read only looks at the bytes it reads. -/
theorem readLE_congr {m m' : Word → Byte} {a : Word} :
    ∀ {k : Nat}, (∀ i, i < k → m' (a + BitVec.ofNat 64 i) = m (a + BitVec.ofNat 64 i)) →
      readLE m' a k = readLE m a k
  | 0, _ => rfl
  | k + 1, h => by
    simp only [readLE]
    have h0 := h 0 (by omega)
    simp only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] at h0
    rw [h0, readLE_congr (m := m) (m' := m') (a := a + 1) (fun i hi => by
      have := h (i + 1) (by omega)
      rwa [show a + 1 + BitVec.ofNat 64 i = a + BitVec.ofNat 64 (i + 1) by bv_omega])]

/-- A write only changes the bytes it writes. -/
theorem writeLE_apply_of_ne {m : Word → Byte} {b x : Word} {v : Nat} :
    ∀ {n : Nat}, (∀ j, j < n → x ≠ b + BitVec.ofNat 64 j) → writeLE m b v n x = m x
  | 0, _ => rfl
  | n + 1, h => by
    simp only [writeLE]
    have h0 := h 0 (by omega)
    simp only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] at h0
    rw [if_neg h0]
    exact writeLE_apply_of_ne (b := b + 1) (fun j hj => by
      have := h (j + 1) (by omega)
      rwa [show b + 1 + BitVec.ofNat 64 j = b + BitVec.ofNat 64 (j + 1) by bv_omega])

/-- A write, pointwise: byte `x` is written exactly when it is `j < n` bytes past `a`,
    and then it is byte `j` of the value (the lowest such `j` is `(x - a).toNat`). -/
theorem writeLE_apply {m : Word → Byte} (x : Word) :
    ∀ {n : Nat} {a : Word} {v : Nat}, writeLE m a v n x =
      if (x - a).toNat < n then BitVec.ofNat 8 (v / 256 ^ (x - a).toNat) else m x
  | 0, _, _ => by simp [writeLE]
  | n + 1, a, v => by
    simp only [writeLE]
    by_cases hx : x = a
    · subst hx; simp
    · rw [if_neg hx, writeLE_apply x]
      have e : (x - a).toNat = (x - (a + 1)).toNat + 1 := by
        have : x - a ≠ 0 := fun h => hx (by bv_omega)
        bv_omega
      rw [e, Nat.pow_succ, Nat.mul_comm, ← Nat.div_div_eq_div_mul]
      simp only [Nat.add_lt_add_iff_right]

/-- A write over a write of the same range. -/
theorem writeLE_overwrite (m : Word → Byte) (a : Word) (v₁ v₂ n : Nat) :
    writeLE (writeLE m a v₁ n) a v₂ n = writeLE m a v₂ n := by
  funext x; rw [writeLE_apply, writeLE_apply, writeLE_apply]; split <;> simp_all

/-- The ranges `[a, a+k)` and `[b, b+n)` do not overlap (modulo 2^64). -/
def Disjoint (a : Word) (k : Nat) (b : Word) (n : Nat) : Prop :=
  n ≤ (a - b).toNat ∧ k ≤ (b - a).toNat

instance (a : Word) (k : Nat) (b : Word) (n : Nat) : Decidable (Disjoint a k b n) := by
  unfold Disjoint; infer_instance

theorem Disjoint.ne {a b : Word} {k n : Nat} (h : Disjoint a k b n) {i j : Nat} (hi : i < k) (hj : j < n) :
    a + BitVec.ofNat 64 i ≠ b + BitVec.ofNat 64 j := by
  obtain ⟨h1, h2⟩ := h
  intro he
  have hk : k ≤ 2 ^ 64 := Nat.le_trans h2 (Nat.le_of_lt (BitVec.isLt _))
  have hn : n ≤ 2 ^ 64 := Nat.le_trans h1 (Nat.le_of_lt (BitVec.isLt _))
  have hi' : i < 2 ^ 64 := by omega
  have hj' : j < 2 ^ 64 := by omega
  bv_omega

/-- Writes to disjoint ranges commute. -/
theorem writeLE_comm {m : Word → Byte} {a b : Word} {v w n k : Nat} (h : Disjoint a n b k) :
    writeLE (writeLE m b w k) a v n = writeLE (writeLE m a v n) b w k := by
  funext x
  simp only [writeLE_apply x]
  unfold Disjoint at h
  by_cases ha : (x - a).toNat < n <;> by_cases hb : (x - b).toNat < k <;> simp only [ha, hb, ite_true, ite_false]
  exfalso; bv_omega

/-- A read of a range disjoint from a write sees the memory before the write. -/
theorem readLE_writeLE_of_disjoint {m : Word → Byte} {a b : Word} {v k n : Nat}
    (h : Disjoint a k b n) : readLE (writeLE m b v n) a k = readLE m a k :=
  readLE_congr fun i hi => writeLE_apply_of_ne fun j hj => h.ne hi hj

/-- Reading back what was just written, at the same address and width. -/
theorem readLE_writeLE_same {m : Word → Byte} :
    ∀ {n : Nat} {a : Word} {v : Nat}, n < 2 ^ 64 → readLE (writeLE m a v n) a n = v % 256 ^ n
  | 0, _, _, _ => by simp [readLE, Nat.mod_one]
  | n + 1, a, v, hn => by
    simp only [readLE, writeLE, ite_true]
    have hrest : readLE (fun x => if x = a then BitVec.ofNat 8 v else writeLE m (a + 1) (v / 256) n x)
        (a + 1) n = readLE (writeLE m (a + 1) (v / 256) n) (a + 1) n :=
      readLE_congr fun i hi => by
        have : a + 1 + BitVec.ofNat 64 i ≠ a := by
          have : i + 1 < 2 ^ 64 := by omega
          bv_omega
        show (if a + 1 + BitVec.ofNat 64 i = a then _ else _) = _
        rw [if_neg this]
    rw [hrest, readLE_writeLE_same (by omega), Nat.pow_succ, Nat.mul_comm (256 ^ n) 256, Nat.mod_mul]
    simp

/-! ## Word-level memory -/

/-- A write of the low `width` bytes of `val` at `addr`. -/
structure Write where
  addr : Word
  width : Nat
  val : Nat
  deriving Repr

/-- A base memory and the writes since, newest first. -/
structure FMem where
  base : Word → Byte
  writes : List Write

namespace FMem

/-- The trusted memory the writes describe. -/
def toMem : List Write → (Word → Byte) → (Word → Byte)
  | [], m => m
  | w :: ws, m => writeLE (toMem ws m) w.addr w.val w.width

def mem (M : FMem) : Word → Byte := toMem M.writes M.base

/-- A read of `k` bytes at `a`, through the writes. -/
def readW : List Write → (Word → Byte) → Word → Nat → Nat
  | [], m, a, k => readLE m a k
  | w :: ws, m, a, k =>
    if a = w.addr ∧ k = w.width ∧ k < 2 ^ 64 then w.val % 256 ^ k
    else if Disjoint a k w.addr w.width then readW ws m a k
    else readLE (toMem (w :: ws) m) a k

def read (M : FMem) (a : Word) (k : Nat) : Nat := readW M.writes M.base a k

/-- A write, at the front. -/
def write (M : FMem) (a : Word) (v k : Nat) : FMem := ⟨M.base, ⟨a, k, v⟩ :: M.writes⟩

theorem readW_eq : ∀ (ws : List Write) (m : Word → Byte) (a : Word) (k : Nat),
    readW ws m a k = readLE (toMem ws m) a k
  | [], _, _, _ => rfl
  | w :: ws, m, a, k => by
    simp only [readW]
    split
    · rename_i h
      obtain ⟨rfl, rfl, hk⟩ := h
      exact (readLE_writeLE_same hk).symm
    · split
      · rename_i _ hd
        rw [readW_eq ws m a k]
        exact (readLE_writeLE_of_disjoint hd).symm
      · rfl

/-- The word-level read is the trusted read of the memory. -/
theorem read_eq (M : FMem) (a : Word) (k : Nat) : M.read a k = readLE M.mem a k :=
  readW_eq M.writes M.base a k

@[simp] theorem mem_write (M : FMem) (a : Word) (v k : Nat) :
    (M.write a v k).mem = writeLE M.mem a v k := rfl

end FMem
end NoCompiler.Fast
