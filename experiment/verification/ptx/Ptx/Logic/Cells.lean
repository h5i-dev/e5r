/-
Arrays of 32-bit cells described by a function.

`cells base N V m` is memory `m` with the `N` little-endian 32-bit cells at
`base` holding `V 0, …, V (N-1)`. Phase memories of reductions and scans are
written this way: what a phase leaves in shared memory is a function of the
index, and `rd32_cells`, `wr_cells` and `cells_congr` are all the proofs
need about it.
-/
import Ptx.Logic.Regions

namespace Ptx

def cells (base : Addr) (N : Nat) (V : Nat → BitVec 32) (m : Mem) : Mem := fun x =>
  if (x - base).toNat < 4 * N then (V ((x - base).toNat / 4) >>> (8 * ((x - base).toNat % 4))).setWidth 8
  else m x

theorem bytes32' (v : BitVec 32) :
    (v >>> (8 * 3)).setWidth 8 ++ (v >>> (8 * 2)).setWidth 8 ++ (v >>> (8 * 1)).setWidth 8 ++
      (v >>> (8 * 0)).setWidth 8 = v := by
  ext i hi
  simp only [BitVec.getElem_append, BitVec.getElem_setWidth, BitVec.getLsbD_ushiftRight]
  repeat' split
  all_goals (try simp only [BitVec.getElem_eq_testBit_toNat, BitVec.getLsbD])
  all_goals (first | rfl | (congr 1; omega))

theorem sub_elem_toNat {base x : Addr} {N i : Nat} (hf : Fits base N) (hi : i < N)
    (hx : covers (elem base i) 4 x) :
    (x - base).toNat = 4 * i + (x - elem base i).toNat ∧ (x - elem base i).toNat < 4 := by
  rw [covers_elem hf hi] at hx
  have he := toNat_elem hf hi
  unfold Fits at hf
  have := x.isLt
  rw [BitVec.toNat_sub, BitVec.toNat_sub, he,
    show 2 ^ 64 - base.toNat + x.toNat = (x.toNat - base.toNat) + 2 ^ 64 by omega, Nat.add_mod_right,
    Nat.mod_eq_of_lt (by omega),
    show 2 ^ 64 - (base.toNat + 4 * i) + x.toNat = (x.toNat - (base.toNat + 4 * i)) + 2 ^ 64 by omega,
    Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
  omega

theorem cells_cell {base x : Addr} {N i : Nat} {V : Nat → BitVec 32} {m : Mem} (hf : Fits base N)
    (hi : i < N) (hx : covers (elem base i) 4 x) :
    cells base N V m x = (V i >>> (8 * (x - elem base i).toNat)).setWidth 8 := by
  obtain ⟨h1, h2⟩ := sub_elem_toNat hf hi hx
  simp only [cells, h1]
  split
  · congr 3 <;> omega
  · omega

theorem rd32_cells {base : Addr} {N i : Nat} {V : Nat → BitVec 32} {m : Mem} (hf : Fits base N)
    (hi : i < N) : rd32 (cells base N V m) (elem base i) = V i := by
  have cov : ∀ j < 4, covers (elem base i) 4 (elem base i + BitVec.ofNat 64 j) := fun j hj => by
    unfold covers; rw [add_sub_left]; simp; omega
  have off : ∀ j < 4, (elem base i + BitVec.ofNat 64 j - elem base i).toNat = j := fun j hj => by
    rw [add_sub_left]; simp; omega
  have e : ∀ j < 4, cells base N V m (elem base i + BitVec.ofNat 64 j) = (V i >>> (8 * j)).setWidth 8 :=
    fun j hj => by rw [cells_cell hf hi (cov j hj), off j hj]
  have h0 := e 0 (by decide); have h1 := e 1 (by decide)
  have h2 := e 2 (by decide); have h3 := e 3 (by decide)
  simp only [BitVec.add_zero] at h0
  simp only [rd32]
  rw [show elem base i + 3 = elem base i + BitVec.ofNat 64 3 from rfl,
    show elem base i + 2 = elem base i + BitVec.ofNat 64 2 from rfl,
    show elem base i + 1 = elem base i + BitVec.ofNat 64 1 from rfl, h3, h2, h1, h0]
  exact bytes32' (V i)

/-- Storing `v` into cell `i` leaves there the bytes of `cells` with
`V i = lo32 v`. -/
theorem wr_cells {base x : Addr} {N i : Nat} {V : Nat → BitVec 32} {m m' : Mem} {v : Val}
    (hf : Fits base N) (hi : i < N) (hx : covers (elem base i) 4 x) (hv : lo32 v = V i) :
    wr m' (elem base i) .b4 v x = cells base N V m x := by
  rw [wr_inside hx, cells_cell hf hi hx, ← hv]
  have := (sub_elem_toNat hf hi hx).2
  generalize (x - elem base i).toNat = o at *
  ext j hj
  simp only [BitVec.getElem_setWidth, BitVec.getLsbD_ushiftRight, lo32, BitVec.getLsbD_setWidth]
  have : 8 * o + j < 32 := by omega
  simp [this]

/-- Cells that hold the same value, and the same bytes outside the array,
give the same memory. -/
theorem cells_congr {base x : Addr} {N : Nat} {V V' : Nat → BitVec 32} {m m' : Mem}
    (hV : (x - base).toNat < 4 * N → V ((x - base).toNat / 4) = V' ((x - base).toNat / 4))
    (hm : ¬ (x - base).toNat < 4 * N → m x = m' x) : cells base N V m x = cells base N V' m' x := by
  unfold cells
  split
  · next h => rw [hV h]
  · next h => exact hm h

/-- The byte offset of a covered byte determines its cell. -/
theorem cell_of_covers {base x : Addr} {N i : Nat} (hf : Fits base N) (hi : i < N)
    (hx : covers (elem base i) 4 x) : (x - base).toNat / 4 = i ∧ (x - base).toNat < 4 * N := by
  obtain ⟨h1, h2⟩ := sub_elem_toNat hf hi hx
  omega

/-- Every byte inside the array is in one of its cells. -/
theorem covers_of_lt {base x : Addr} {N : Nat} (hf : Fits base N) (h : (x - base).toNat < 4 * N) :
    covers (elem base ((x - base).toNat / 4)) 4 x := by
  have hi : (x - base).toNat / 4 < N := by omega
  rw [covers_elem hf hi]
  have := x.isLt; have := base.isLt
  unfold Fits at hf
  rw [BitVec.toNat_sub] at h ⊢
  by_cases hle : base.toNat ≤ x.toNat
  · rw [show 2 ^ 64 - base.toNat + x.toNat = (x.toNat - base.toNat) + 2 ^ 64 by omega,
      Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)] at h ⊢
    omega
  · rw [Nat.mod_eq_of_lt (by omega)] at h; omega

@[simp] theorem elem_zero (b : Addr) : elem b 0 = b := by simp [elem]

theorem elem_elem (b : Addr) (c i : Nat) : elem (elem b c) i = elem b (c + i) := by
  apply BitVec.eq_of_toNat_eq
  simp only [elem, BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

/-- The part of an array starting at element `c` fits if the array does. -/
theorem fits_tail {b : Addr} {N c M : Nat} (hf : Fits b N) (hc : c + M ≤ N) : Fits (elem b c) M := by
  unfold Fits at *
  by_cases h0 : M = 0
  · subst h0; have := (elem b c).isLt; omega
  · rw [toNat_elem hf (by omega)]; omega

/-- An aligned element of an array that is one allocation of the list. -/
theorem accessOk_elem_mem {al : List Region} {base : Addr} {N i : Nat} (hm : ⟨base, 4 * N⟩ ∈ al)
    (hf : Fits base N) (hal : base.toNat % 4 = 0) (hi : i < N) :
    accessOk al (elem base i) .b4 = true := by
  simp only [accessOk, Size.bytes_b4, Bool.and_eq_true, beq_iff_eq, List.any_eq_true]
  exact ⟨aligned_elem hf hi hal, _, hm, holds_elem hf hi⟩

/-- The bytes of a 32-bit store depend only on the low 32 bits stored. -/
theorem wr_lo32 {m m' : Mem} {a x : Addr} {v v' : Val} (h : lo32 v = lo32 v') (hx : covers a 4 x) :
    wr m a .b4 v x = wr m' a .b4 v' x := by
  rw [wr_inside hx, wr_inside hx]
  have : (x - a).toNat < 4 := hx
  generalize (x - a).toNat = o at *
  have hb := congrArg (fun w : BitVec 32 => w.getLsbD) h
  ext j hj
  simp only [BitVec.getElem_setWidth, BitVec.getLsbD_ushiftRight]
  have h1 : 8 * o + j < 32 := by omega
  have := congrFun hb (8 * o + j)
  simp only [lo32, BitVec.getLsbD_setWidth, h1, decide_true, Bool.true_and] at this
  exact this

end Ptx
