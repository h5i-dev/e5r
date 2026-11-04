/-
Arrays in global memory and the arithmetic facts kernels need about them.

`elem base i` is the address of 32-bit element `i` of an array at `base`.
For an array that does not wrap the address space (`base + 4N ≤ 2^64`) every
fact about which bytes an element covers reduces to linear arithmetic on
`toNat`, which `omega` decides; that is the only route the per-kernel proofs
use for disjointness.
-/
import Ptx.Logic.Hoare

namespace Ptx

def elem (base : Addr) (i : Nat) : Addr := base + BitVec.ofNat 64 (4 * i)

/-- An array of `N` 32-bit elements at `base`, inside the address space. -/
def Fits (base : Addr) (N : Nat) : Prop := base.toNat + 4 * N ≤ 2 ^ 64

/-- Memory holds `A i` at element `i` for every `i < N`. -/
def Holds32 (m : Mem) (base : Addr) (N : Nat) (A : Nat → BitVec 32) : Prop :=
  ∀ i < N, rd32 m (elem base i) = A i

theorem covers_iff {a : Addr} {n : Nat} {x : Addr} (h : a.toNat + n ≤ 2 ^ 64) :
    covers a n x ↔ a.toNat ≤ x.toNat ∧ x.toNat < a.toNat + n := by
  unfold covers
  rw [BitVec.toNat_sub]
  have := x.isLt; have := a.isLt
  constructor
  · intro hc
    by_cases hle : a.toNat ≤ x.toNat
    · refine ⟨hle, ?_⟩
      rw [show 2 ^ 64 - a.toNat + x.toNat = (x.toNat - a.toNat) + 2 ^ 64 by omega,
        Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)] at hc
      omega
    · rw [Nat.mod_eq_of_lt (by omega)] at hc; omega
  · rintro ⟨h1, h2⟩
    rw [show 2 ^ 64 - a.toNat + x.toNat = (x.toNat - a.toNat) + 2 ^ 64 by omega,
      Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    omega

theorem toNat_elem {base : Addr} {N i : Nat} (hf : Fits base N) (hi : i < N) :
    (elem base i).toNat = base.toNat + 4 * i := by
  unfold elem Fits at *
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 4 * i) (by omega),
    Nat.mod_eq_of_lt (by omega)]

theorem covers_elem {base : Addr} {N i : Nat} {x : Addr} (hf : Fits base N) (hi : i < N) :
    covers (elem base i) 4 x ↔ base.toNat + 4 * i ≤ x.toNat ∧ x.toNat < base.toNat + 4 * i + 4 := by
  rw [covers_iff (by rw [toNat_elem hf hi]; unfold Fits at hf; omega), toNat_elem hf hi]

/-- Distinct elements of one array share no byte. -/
theorem elem_disjoint {base : Addr} {N i j : Nat} {x : Addr} (hf : Fits base N) (hi : i < N)
    (hj : j < N) (hij : i ≠ j) (hx : covers (elem base i) 4 x) : ¬ covers (elem base j) 4 x := by
  rw [covers_elem hf hi] at hx; rw [covers_elem hf hj]; omega

/-- Elements of two non-overlapping arrays share no byte. -/
theorem elem_disjoint₂ {a b : Addr} {N M i j : Nat} {x : Addr} (ha : Fits a N) (hb : Fits b M)
    (hsep : a.toNat + 4 * N ≤ b.toNat ∨ b.toNat + 4 * M ≤ a.toNat) (hi : i < N) (hj : j < M)
    (hx : covers (elem a i) 4 x) : ¬ covers (elem b j) 4 x := by
  rw [covers_elem ha hi] at hx; rw [covers_elem hb hj]; omega

/-- An aligned array element inside a region given as one allocation. -/
theorem holds_elem {base : Addr} {N i : Nat} (hf : Fits base N) (hi : i < N) :
    (Region.mk base (4 * N)).holds (elem base i) 4 = true := by
  simp only [Region.holds, decide_eq_true_eq, toNat_elem hf hi]; omega

theorem aligned_elem {base : Addr} {N i : Nat} (hf : Fits base N) (hi : i < N)
    (hal : base.toNat % 4 = 0) : (elem base i).toNat % 4 = 0 := by
  rw [toNat_elem hf hi]; omega

/-- The 64-bit byte offset `mul.wide.s32 %rd, %r, 4` computes from a
non-negative 32-bit index. -/
theorem mulWide4 {g : BitVec 32} (h : g.toNat < 2 ^ 31) :
    BitVec.signExtend 64 g * BitVec.signExtend 64 (lo32 (BitVec.ofInt 64 4)) =
      BitVec.ofNat 64 (4 * g.toNat) := by
  have hm : g.msb = false := by rw [BitVec.msb_eq_false_iff_two_mul_lt]; omega
  rw [BitVec.signExtend_eq_setWidth_of_msb_false hm]
  have : BitVec.signExtend 64 (lo32 (BitVec.ofInt 64 4)) = 4#64 := by decide
  rw [this]
  apply BitVec.eq_of_toNat_eq
  simp
  omega

theorem rd_b4 (m : Mem) (a : Addr) : rd m a .b4 = ext32 (rd32 m a) := rfl

theorem lo32_rd_b4 (m : Mem) (a : Addr) : lo32 (rd m a .b4) = rd32 m a := by
  rw [rd_b4, lo32_ext32]

theorem rd32_wr_same (m : Mem) (a : Addr) (v : Val) : rd32 (wr m a .b4 v) a = lo32 v := by
  have := rd_wr_same m a .b4 v
  simp only [rd] at this
  have h2 := congrArg lo32 this
  simpa [lo32] using h2

theorem rd32_wr_disjoint {m : Mem} {a b : Addr} {sz : Size} {v : Val}
    (h : ∀ x, covers b 4 x → ¬ covers a sz.bytes x) : rd32 (wr m a sz v) b = rd32 m b := by
  have := rd_wr_disjoint (m := m) (v := v) (sz' := .b4) h
  rw [rd_b4, rd_b4] at this
  have h2 := congrArg lo32 this
  simpa using h2

theorem elem_def (base : Addr) (i : Nat) : base + BitVec.ofNat 64 (4 * i) = elem base i := rfl

/-- `setp.ge.s32 n, g` on two non-negative 32-bit values is `n ≤ g`. -/
theorem sle_nonneg {n g : BitVec 32} (hn : n.toNat < 2 ^ 31) (hg : g.toNat < 2 ^ 31) :
    n.sle g = true ↔ n.toNat ≤ g.toNat := by
  rw [BitVec.sle_iff_toInt_le,
    BitVec.toInt_eq_toNat_of_msb (by rw [BitVec.msb_eq_false_iff_two_mul_lt]; omega),
    BitVec.toInt_eq_toNat_of_msb (by rw [BitVec.msb_eq_false_iff_two_mul_lt]; omega)]
  omega

end Ptx
