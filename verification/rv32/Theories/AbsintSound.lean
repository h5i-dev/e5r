/-
  Soundness of the abstract interpreter (`Theories/Absint.lean`), part 1:
  abstract values. Every value operation the transfer function uses is shown
  to over-approximate the concrete operation of `Theories/Hart.lean`.

  Original e5r code, Apache-2.0. Work in progress: memory, states, the
  transfer function and `check_sound` follow in later parts.
-/
import Theories.Absint

set_option linter.constructorNameAsVariable false

namespace E5R.AI
open E5R

/-! ## Concretization -/

/-- The words an abstract value describes. `ρ` gives the interrupted
    machine's registers (and pc, as 32) for symbolic values. -/
def AV.gam (ρ : Nat → Word) : AV → Word → Prop
  | .top, _ => True
  | .vals l, x => x.toNat ∈ l
  | .rng lo hi, x => lo ≤ x.toNat ∧ x.toNat ≤ hi
  | .sym s o, x => x = ρ s + BitVec.ofNat 32 o

theorem M32_eq : M32 = 2 ^ 32 := rfl

theorem toNat_lt (x : Word) : x.toNat < M32 := x.isLt

theorem w_toNat (x : Word) : w x.toNat = x := by simp [w]

/-! ## Value-set normalization -/

theorem mem_ins {x y : Nat} {l : List Nat} : y ∈ ins x l ↔ y = x ∨ y ∈ l := by
  induction l with
  | nil => simp [ins]
  | cons z zs ih =>
    unfold ins
    by_cases h1 : x < z
    · simp [h1]
    · by_cases h2 : x = z
      · subst h2; simp [h1]
      · simp [h1, h2, ih, or_left_comm]

theorem mem_norm {y : Nat} {l : List Nat} : y ∈ norm l ↔ ∃ z ∈ l, y = z % M32 := by
  induction l with
  | nil => simp [norm]
  | cons z zs ih =>
    simp only [norm, List.foldr_cons] at *
    rw [mem_ins, ih]
    constructor
    · rintro (h | ⟨u, hu, rfl⟩)
      · exact ⟨z, by simp, h⟩
      · exact ⟨u, by simp [hu], rfl⟩
    · rintro ⟨u, hu, rfl⟩
      simp at hu
      rcases hu with rfl | hu
      · exact .inl rfl
      · exact .inr ⟨u, hu, rfl⟩

theorem foldl_min_le_init (b : Nat) (zs : List Nat) : zs.foldl min b ≤ b := by
  induction zs generalizing b with
  | nil => simp
  | cons q qs ih => exact Nat.le_trans (ih _) (Nat.min_le_left _ _)

theorem foldl_min_le_mem (b : Nat) (zs : List Nat) (x : Nat) (h : x ∈ zs) : zs.foldl min b ≤ x := by
  induction zs generalizing b with
  | nil => simp at h
  | cons q qs ih =>
    simp only [List.foldl_cons]
    simp at h
    rcases h with rfl | h
    · exact Nat.le_trans (foldl_min_le_init _ _) (Nat.min_le_right _ _)
    · exact ih _ h

theorem init_le_foldl_max (b : Nat) (zs : List Nat) : b ≤ zs.foldl max b := by
  induction zs generalizing b with
  | nil => simp
  | cons q qs ih => exact Nat.le_trans (Nat.le_max_left _ _) (ih _)

theorem mem_le_foldl_max (b : Nat) (zs : List Nat) (x : Nat) (h : x ∈ zs) : x ≤ zs.foldl max b := by
  induction zs generalizing b with
  | nil => simp at h
  | cons q qs ih =>
    simp only [List.foldl_cons]
    simp at h
    rcases h with rfl | h
    · exact Nat.le_trans (Nat.le_max_right _ _) (init_le_foldl_max _ _)
    · exact ih _ h

theorem lmin_le {l : List Nat} {x : Nat} (h : x ∈ l) : lmin l ≤ x := by
  match l, h with
  | y :: ys, h =>
    simp only [lmin]
    simp at h
    rcases h with rfl | h
    · exact foldl_min_le_init _ _
    · exact foldl_min_le_mem _ _ _ h

theorem le_lmax {l : List Nat} {x : Nat} (h : x ∈ l) : x ≤ lmax l := by
  match l, h with
  | y :: ys, h =>
    simp only [lmax]
    simp at h
    rcases h with rfl | h
    · exact init_le_foldl_max _ _
    · exact mem_le_foldl_max _ _ _ h

/-- The workhorse: a value computed from some element of `l` is described by
    `mkVals l`. -/
theorem mkVals_sound {ρ : Nat → Word} {l : List Nat} {x : Word}
    (h : ∃ z ∈ l, z % M32 = x.toNat) : (mkVals l).gam ρ x := by
  obtain ⟨z, hz, hx⟩ := h
  have hm : x.toNat ∈ norm l := mem_norm.mpr ⟨z, hz, hx.symm⟩
  simp only [mkVals]
  split
  · exact hm
  · exact ⟨lmin_le hm, le_lmax hm⟩

theorem const_sound (ρ : Nat → Word) (c : Nat) : (AV.const c).gam ρ (w c) := by
  simp [AV.const, AV.gam, w, M32]

theorem const_sound' {ρ : Nat → Word} {c : Nat} {x : Word} (h : x.toNat = c % M32) :
    (AV.const c).gam ρ x := by
  simp [AV.const, AV.gam, h]

theorem small_sound {ρ : Nat → Word} {a : AV} {x : Word} (h : a.gam ρ x) : a.small.gam ρ x := by
  cases a with
  | rng lo hi =>
    simp only [AV.small]
    split
    · simp only [AV.gam] at h ⊢
      simp only [List.mem_map, List.mem_range]
      exact ⟨x.toNat - lo, by omega, by omega⟩
    · exact h
  | _ => exact h

/-! ## Order -/

theorem leq_sound {ρ : Nat → Word} {a b : AV} {x : Word} (hl : a.leq b = true) (h : a.gam ρ x) :
    b.gam ρ x := by
  cases b with
  | top => trivial
  | vals l' =>
    cases a with
    | vals l => simp only [AV.leq, List.all_eq_true, decide_eq_true_eq] at hl; exact hl _ h
    | _ => simp [AV.leq] at hl
  | rng lo hi =>
    cases a with
    | vals l =>
      simp only [AV.leq, List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hl
      exact hl _ h
    | rng lo' hi' =>
      simp only [AV.leq, Bool.and_eq_true, decide_eq_true_eq] at hl
      simp only [AV.gam] at h ⊢; omega
    | _ => simp [AV.leq] at hl
  | sym s o =>
    cases a with
    | sym s' o' =>
      simp only [AV.leq, Bool.and_eq_true, beq_iff_eq] at hl
      obtain ⟨rfl, rfl⟩ := hl; exact h
    | _ => simp [AV.leq] at hl

/-! ## Bounds and exact set operations -/

theorem bounds_sound {ρ : Nat → Word} {a : AV} {x : Word} {l h : Nat} (hg : a.gam ρ x)
    (hb : a.bounds = some (l, h)) : l ≤ x.toNat ∧ x.toNat ≤ h := by
  cases a with
  | top => simp [AV.bounds] at hb; obtain ⟨rfl, rfl⟩ := hb; have := toNat_lt x; simp [M32] at this ⊢; omega
  | vals vs =>
    cases vs with
    | nil => simp [AV.gam] at hg
    | cons v vs =>
      simp only [AV.bounds, Option.some.injEq, Prod.mk.injEq] at hb
      obtain ⟨rfl, rfl⟩ := hb
      exact ⟨lmin_le hg, le_lmax hg⟩
  | rng lo hi => simp [AV.bounds] at hb; obtain ⟨rfl, rfl⟩ := hb; exact hg
  | sym _ _ => simp [AV.bounds] at hb

theorem lift2_sound {ρ : Nat → Word} {f : Word → Word → Word} {a b : List Nat} {x y : Word}
    (hx : (AV.vals a).gam ρ x) (hy : (AV.vals b).gam ρ y) : (lift2 f a b).gam ρ (f x y) := by
  unfold lift2
  split
  · apply mkVals_sound
    refine ⟨(f (w x.toNat) (w y.toNat)).toNat, ?_, ?_⟩
    · simp only [List.mem_flatMap, List.mem_map]
      exact ⟨x.toNat, hx, y.toNat, hy, rfl⟩
    · rw [w_toNat, w_toNat]; exact Nat.mod_eq_of_lt (toNat_lt _)
  · trivial

theorem toNat_add_w (x : Word) (c : Nat) : (x + w c).toNat = (x.toNat + c % M32) % M32 := by
  simp [w, BitVec.toNat_add, M32]

theorem addC_sound {ρ : Nat → Word} {a : AV} {x : Word} (c : Nat) (h : a.gam ρ x) :
    (addC a c).gam ρ (x + w c) := by
  have hs := small_sound h
  unfold addC
  generalize a.small = b at hs
  have hc : c % M32 < M32 := Nat.mod_lt _ (by decide)
  cases b with
  | top => trivial
  | vals l =>
    apply mkVals_sound
    exact ⟨x.toNat + c % M32, List.mem_map.mpr ⟨_, hs, rfl⟩, (toNat_add_w x c).symm⟩
  | rng lo hi =>
    simp only [AV.gam] at hs
    have hx := toNat_lt x
    have e := toNat_add_w x c
    simp only [M32] at hx e hc
    dsimp only
    by_cases h1 : hi + c % M32 < M32
    · rw [if_pos h1]; simp only [M32] at h1 ⊢; simp only [AV.gam]; omega
    · rw [if_neg h1]
      by_cases h2 : M32 ≤ lo + c % M32
      · rw [if_pos h2]; simp only [M32] at h1 h2 ⊢; simp only [AV.gam]; omega
      · rw [if_neg h2]; trivial
  | sym s o =>
    simp only [AV.gam] at hs ⊢
    rw [hs, BitVec.add_assoc]
    congr 1
    apply BitVec.eq_of_toNat_eq
    simp [w, BitVec.toNat_add, M32, Nat.add_mod]

/-- An exact single value. -/
theorem gam_single {ρ : Nat → Word} {c : Nat} {y : Word} (h : (AV.vals [c]).gam ρ y) : y = w c := by
  simp [AV.gam] at h; subst h; exact (w_toNat y).symm

end E5R.AI
