import Std.Tactic.BVDecide
/-
Byte-addressed global memory.

Addresses are 64-bit (`.address_size 64`), memory is a total map from address
to byte, and multi-byte accesses are little-endian. An access is legal only if
it is naturally aligned and lies inside one allocation of the launch; anything
else is a fault (PTX leaves it undefined, so the model refuses it).

`covers a n x` says byte `x` is one of the `n` bytes starting at `a`. It is
phrased with wrapping subtraction so it is meaningful for every `a`; inside an
allocation (no wrap) it is the ordinary interval `[a, a + n)`.
-/
namespace Ptx

abbrev Val := BitVec 64
abbrev Addr := BitVec 64
abbrev Mem := Addr → BitVec 8

/-- Access sizes of the subset: 4 and 8 bytes. -/
inductive Size where
  | b4 | b8
  deriving Repr, DecidableEq, Inhabited

def Size.bytes : Size → Nat
  | .b4 => 4
  | .b8 => 8

@[simp] theorem Size.bytes_b4 : Size.b4.bytes = 4 := rfl
@[simp] theorem Size.bytes_b8 : Size.b8.bytes = 8 := rfl

/-- Byte `x` is one of the `n` bytes starting at `a`. -/
def covers (a : Addr) (n : Nat) (x : Addr) : Prop := (x - a).toNat < n

instance (a : Addr) (n : Nat) (x : Addr) : Decidable (covers a n x) := by
  unfold covers; infer_instance

def rd32 (m : Mem) (a : Addr) : BitVec 32 := m (a + 3) ++ m (a + 2) ++ m (a + 1) ++ m a

def rd64 (m : Mem) (a : Addr) : BitVec 64 := rd32 m (a + 4) ++ rd32 m a

/-- A load: the bytes at `a`, zero-extended to 64 bits. -/
def rd (m : Mem) (a : Addr) : Size → Val
  | .b4 => (rd32 m a).setWidth 64
  | .b8 => rd64 m a

/-- A store of the low `sz` bytes of `v` at `a`. Defined pointwise, so its
frame is visible without unfolding anything. -/
def wr (m : Mem) (a : Addr) (sz : Size) (v : Val) : Mem := fun x =>
  if (x - a).toNat < sz.bytes then (v >>> (8 * (x - a).toNat)).setWidth 8 else m x

/-- One allocation: `size` bytes at `base`. -/
structure Region where
  base : Addr
  size : Nat
  deriving Repr, DecidableEq, Inhabited

/-- The `n` bytes at `a` lie inside the region (as natural numbers, so a range
that wraps around the address space is never inside). -/
def Region.holds (r : Region) (a : Addr) (n : Nat) : Bool :=
  decide (r.base.toNat ≤ a.toNat ∧ a.toNat + n ≤ r.base.toNat + r.size)

/-- Aligned and inside one allocation. -/
def accessOk (al : List Region) (a : Addr) (sz : Size) : Bool :=
  a.toNat % sz.bytes == 0 && al.any (·.holds a sz.bytes)

/-! ## Locality and frame -/

theorem add_sub_left (a k : Addr) : a + k - a = k := by bv_omega

theorem wr_outside {m : Mem} {a : Addr} {sz : Size} {v : Val} {x : Addr}
    (h : ¬ covers a sz.bytes x) : wr m a sz v x = m x := by
  unfold covers at h; simp only [wr]; exact ite_eq_right_iff.mpr (fun h' => absurd h' h)

theorem wr_inside {m : Mem} {a : Addr} {sz : Size} {v : Val} {x : Addr}
    (h : covers a sz.bytes x) : wr m a sz v x = (v >>> (8 * (x - a).toNat)).setWidth 8 := by
  unfold covers at h; simp only [wr]; exact ite_eq_left h

/-- A load depends only on the bytes it covers. -/
theorem rd_congr {m₁ m₂ : Mem} {a : Addr} {sz : Size}
    (h : ∀ x, covers a sz.bytes x → m₁ x = m₂ x) : rd m₁ a sz = rd m₂ a sz := by
  unfold covers at h
  cases sz with
  | b4 =>
    simp only [Size.bytes_b4] at h
    simp only [rd, rd32]
    rw [h a (by bv_omega), h (a + 1) (by bv_omega), h (a + 2) (by bv_omega),
      h (a + 3) (by bv_omega)]
  | b8 =>
    simp only [Size.bytes_b8] at h
    simp only [rd, rd64, rd32]
    rw [h a (by bv_omega), h (a + 1) (by bv_omega), h (a + 2) (by bv_omega),
      h (a + 3) (by bv_omega), h (a + 4) (by bv_omega), h (a + 4 + 1) (by bv_omega),
      h (a + 4 + 2) (by bv_omega), h (a + 4 + 3) (by bv_omega)]

/-- A store overwrites exactly the bytes it covers, with the value stored. -/
theorem rd_wr_same (m : Mem) (a : Addr) (sz : Size) (v : Val) :
    rd (wr m a sz v) a sz = match sz with
      | .b4 => (v.setWidth 32).setWidth 64
      | .b8 => v := by
  cases sz with
  | b4 =>
    simp only [rd, rd32, wr, BitVec.sub_self, add_sub_left, Size.bytes_b4]
    simp
    bv_decide
  | b8 =>
    simp only [rd, rd64, rd32, wr, BitVec.sub_self, BitVec.add_assoc, add_sub_left,
      Size.bytes_b8]
    simp
    bv_decide

/-- A load from bytes a store did not touch sees the old memory. -/
theorem rd_wr_disjoint {m : Mem} {a b : Addr} {sz sz' : Size} {v : Val}
    (h : ∀ x, covers b sz'.bytes x → ¬ covers a sz.bytes x) :
    rd (wr m a sz v) b sz' = rd m b sz' :=
  rd_congr fun x hx => wr_outside (h x hx)

end Ptx
