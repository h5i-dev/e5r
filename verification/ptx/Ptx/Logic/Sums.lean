/-
Sums of 32-bit values over the threads of a launch.

The phase theorem states the final value of an accumulator cell as a sum
over `Launch.threads` (`tsum`). For a 1-D launch in which only thread 0 of
each block contributes, `tsum_oneD_first` turns that into the sum over
blocks, `accUpTo v G`.
-/
import Ptx.Logic.PhaseSound
import Ptx.Logic.PhaseWp

namespace Ptx

theorem accUpTo_congr' {f g : Nat → BitVec 32} {N : Nat} (h : ∀ m < N, f m = g m) :
    accUpTo f N = accUpTo g N := by
  induction N with
  | zero => rfl
  | succ N ih => simp only [accUpTo]; rw [ih fun m hm => h m (by omega), h N (by omega)]

theorem accUpTo_add' (f : Nat → BitVec 32) (a b : Nat) :
    accUpTo f (a + b) = accUpTo f a + accUpTo (fun m => f (a + m)) b := by
  induction b with
  | zero => simp [accUpTo]
  | succ b ih => rw [← Nat.add_assoc]; simp only [accUpTo]; rw [ih, BitVec.add_assoc]

/-- Summing block by block is summing everything. -/
theorem accUpTo_blocks (f : Nat → BitVec 32) (B : Nat) : ∀ G,
    accUpTo (fun c => accUpTo (fun i => f (c * B + i)) B) G = accUpTo f (G * B) := by
  intro G
  induction G with
  | zero => simp [accUpTo]
  | succ G ih =>
    show accUpTo _ G + accUpTo (fun i => f (G * B + i)) B = accUpTo f ((G + 1) * B)
    rw [Nat.succ_mul, accUpTo_add' f (G * B) B, ih]

theorem accUpTo_zero (N : Nat) : accUpTo (fun _ => (0 : BitVec 32)) N = 0 := by
  induction N with
  | zero => rfl
  | succ N ih => simp only [accUpTo, ih]; rfl

/-- An `atom.add` adds its operand. -/
theorem addsTo_add (b : BitVec 32) : AddsTo (fun old => ext32 (lo32 old + b)) b := by
  intro w; simp

/-- Only one term is non-zero. -/
theorem accUpTo_single (a : BitVec 32) (K N : Nat) (hK : K < N) :
    accUpTo (fun k => if k = K then a else 0) N = a := by
  induction N with
  | zero => omega
  | succ N ih =>
    simp only [accUpTo]
    by_cases h : K = N
    · subst h
      have : accUpTo (fun k => if k = K then a else 0) K = 0 := by
        have : ∀ M ≤ K, accUpTo (fun k => if k = K then a else 0) M = 0 := by
          intro M hM
          induction M with
          | zero => rfl
          | succ M ihM => simp only [accUpTo]; rw [ihM (by omega)]; simp [show M ≠ K by omega]
        exact this K (Nat.le_refl _)
      rw [this]; simp
    · rw [ih (by omega)]; simp [show N ≠ K from Ne.symm h]

/-- A sum over any list. -/
def lsum {β : Type} (l : List β) (f : β → BitVec 32) : BitVec 32 := (l.map f).foldr (· + ·) 0

theorem lsum_append {β : Type} (l l' : List β) (f : β → BitVec 32) :
    lsum (l ++ l') f = lsum l f + lsum l' f := by
  induction l with
  | nil => simp [lsum]
  | cons a l ih => simp only [lsum, List.cons_append, List.map_cons, List.foldr_cons] at ih ⊢; rw [ih, BitVec.add_assoc]

theorem lsum_flatMap {α β : Type} (l : List α) (g : α → List β) (f : β → BitVec 32) :
    lsum (l.flatMap g) f = lsum l fun a => lsum (g a) f := by
  induction l with
  | nil => rfl
  | cons a l ih => rw [List.flatMap_cons, lsum_append, ih]; rfl

theorem lsum_map {α β : Type} (l : List α) (g : α → β) (f : β → BitVec 32) :
    lsum (l.map g) f = lsum l (f ∘ g) := by
  simp [lsum, List.map_map]

theorem lsum_range (N : Nat) (f : Nat → BitVec 32) : lsum (List.range N) f = accUpTo f N := by
  induction N with
  | zero => rfl
  | succ N ih =>
    rw [List.range_succ, lsum_append, ih]
    simp [lsum, accUpTo]

theorem tsum_eq_lsum (l : List Tid) (f : Tid → BitVec 32) : tsum l f = lsum l f := rfl

theorem lsum_congr {β : Type} {l : List β} {f g : β → BitVec 32} (h : ∀ a ∈ l, f a = g a) :
    lsum l f = lsum l g := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [lsum, List.map_cons, List.foldr_cons] at ih ⊢
    rw [h a (by simp), ih fun x hx => h x (by simp [hx])]

theorem range32_one : range32 1#32 = [0#32] := rfl

/-- The blocks of a 1-D grid. -/
theorem dims_oneD (G : BitVec 32) : dims ⟨G, 1#32, 1#32⟩ = (range32 G).map fun x => ⟨x, 0, 0⟩ := by
  simp [dims, range32_one]

theorem lsum_range32 (G : BitVec 32) (f : BitVec 32 → BitVec 32) :
    lsum (range32 G) f = accUpTo (fun m => f (BitVec.ofNat 32 m)) G.toNat := by
  rw [range32, lsum_map, lsum_range]; rfl

/-- In a 1-D launch with at least one thread per block, summing over the
threads a value only thread 0 of each block contributes is summing over the
blocks. -/
theorem tsum_oneD_first {L : Launch} {G B : BitVec 32} (h1 : L.OneD G B) (hB : 0 < B.toNat)
    (v : Nat → BitVec 32) :
    tsum L.threads (fun t => if t.tid.x.toNat = 0 then v t.ctaid.x.toNat else 0) = accUpTo v G.toNat := by
  rw [tsum_eq_lsum, Launch.threads, h1.1, h1.2, lsum_flatMap]
  -- inside one block only thread 0 counts
  have inner : ∀ c : Dim3, lsum ((dims ⟨B, 1, 1⟩).map fun d => (⟨c, d⟩ : Tid))
      (fun t => if t.tid.x.toNat = 0 then v t.ctaid.x.toNat else 0) = v c.x.toNat := by
    intro c
    rw [show (⟨B, 1, 1⟩ : Dim3) = ⟨B, 1#32, 1#32⟩ from rfl, dims_oneD, List.map_map, lsum_map,
      lsum_range32]
    have hlt := B.isLt
    have key : ∀ N, N ≤ B.toNat →
        accUpTo (fun m => if (BitVec.ofNat 32 m).toNat = 0 then v c.x.toNat else 0) N =
          if 0 < N then v c.x.toNat else 0 := by
      intro N
      induction N with
      | zero => intro _; rfl
      | succ N ih =>
        intro hN
        simp only [accUpTo]
        rw [ih (by omega)]
        have hN' : (BitVec.ofNat 32 N).toNat = N := by simp; omega
        rw [hN']
        by_cases h0 : N = 0
        · subst h0; simp
        · simp [h0, show 0 < N by omega]
    have := key B.toNat (Nat.le_refl _)
    simp only [hB, ↓reduceIte] at this
    exact this
  rw [lsum_congr fun c _ => inner c,
    show (⟨G, 1, 1⟩ : Dim3) = ⟨G, 1#32, 1#32⟩ from rfl, dims_oneD, lsum_map, lsum_range32]
  refine accUpTo_congr' fun m hm => ?_
  have := G.isLt
  show v (BitVec.ofNat 32 m).toNat = v m
  simp; rw [Nat.mod_eq_of_lt (by omega)]

/-- In a 1-D launch, summing a function of the global index over the threads
is summing it over `0 .. G·B`. -/
theorem tsum_oneD_gid {L : Launch} {G B : BitVec 32} (h1 : L.OneD G B) (v : Nat → BitVec 32) :
    tsum L.threads (fun t => v (t.ctaid.x.toNat * B.toNat + t.tid.x.toNat)) =
      accUpTo v (G.toNat * B.toNat) := by
  rw [tsum_eq_lsum, Launch.threads, h1.1, h1.2, lsum_flatMap]
  have inner : ∀ c : Dim3, lsum ((dims ⟨B, 1, 1⟩).map fun d => (⟨c, d⟩ : Tid))
      (fun t => v (t.ctaid.x.toNat * B.toNat + t.tid.x.toNat)) =
        accUpTo (fun i => v (c.x.toNat * B.toNat + i)) B.toNat := by
    intro c
    rw [show (⟨B, 1, 1⟩ : Dim3) = ⟨B, 1#32, 1#32⟩ from rfl, dims_oneD, List.map_map, lsum_map,
      lsum_range32]
    have hlt := B.isLt
    refine accUpTo_congr' fun m hm => ?_
    show v (c.x.toNat * B.toNat + (BitVec.ofNat 32 m).toNat) = _
    simp; rw [Nat.mod_eq_of_lt (by omega)]
  rw [lsum_congr fun c _ => inner c,
    show (⟨G, 1, 1⟩ : Dim3) = ⟨G, 1#32, 1#32⟩ from rfl, dims_oneD, lsum_map, lsum_range32,
    ← accUpTo_blocks v B.toNat G.toNat]
  refine accUpTo_congr' fun m hm => ?_
  have := G.isLt
  show accUpTo (fun i => v ((BitVec.ofNat 32 m).toNat * B.toNat + i)) B.toNat = _
  simp; rw [Nat.mod_eq_of_lt (by omega)]

end Ptx
