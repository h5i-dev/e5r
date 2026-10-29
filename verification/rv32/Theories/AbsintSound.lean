/-
  Soundness of the abstract interpreter (`Theories/Absint.lean`), part 1:
  abstract values. Every value operation the transfer function uses is shown
  to over-approximate the concrete operation of `Theories/Hart.lean`.

  Original e5r code, Apache-2.0. Work in progress: memory, states, the
  transfer function and `check_sound` follow in later parts.
-/
import Theories.Absint
import Theories.Logic

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

/-- Two values whose bounds are known add without wrapping when the bounds
    say so. -/
theorem add_bounds {x y : Word} {l1 h1 l2 h2 : Nat} (hx : l1 ≤ x.toNat ∧ x.toNat ≤ h1)
    (hy : l2 ≤ y.toNat ∧ y.toNat ≤ h2) (h : h1 + h2 < M32) :
    l1 + l2 ≤ (x + y).toNat ∧ (x + y).toNat ≤ h1 + h2 := by
  rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by simp only [M32] at h; omega)]; omega

theorem add_sound {ρ : Nat → Word} {a b : AV} {x y : Word} (ha : a.gam ρ x) (hb : b.gam ρ y) :
    (a.add b).gam ρ (x + y) := by
  unfold AV.add
  split
  · exact lift2_sound ha hb
  · rw [gam_single hb]; exact addC_sound _ ha
  · rw [gam_single ha, BitVec.add_comm]; exact addC_sound _ hb
  · split
    · trivial
    · trivial
    · split
      · rename_i l1 h1 l2 h2 e1 e2
        split
        · exact add_bounds (bounds_sound ha e1) (bounds_sound hb e2) (by assumption)
        · trivial
      · trivial

theorem sub_eq_add (x : Word) (c : Nat) : x - w c = x + w ((M32 - c % M32) % M32) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_sub, BitVec.toNat_add, w, BitVec.toNat_ofNat, M32]
  omega

theorem sub_sound {ρ : Nat → Word} {a b : AV} {x y : Word} (ha : a.gam ρ x) (hb : b.gam ρ y) :
    (a.sub b).gam ρ (x - y) := by
  unfold AV.sub
  split
  · rw [gam_single hb, sub_eq_add]; exact addC_sound _ ha
  · split
    · exact lift2_sound ha hb
    · trivial

theorem and_le_right (x y : Word) : (x &&& y).toNat ≤ y.toNat := by
  rw [BitVec.toNat_and]; exact Nat.and_le_right

theorem and_le_left (x y : Word) : (x &&& y).toNat ≤ x.toNat := by
  rw [BitVec.toNat_and]; exact Nat.and_le_left

theorem band_sound {ρ : Nat → Word} {a b : AV} {x y : Word} (ha : a.gam ρ x) (hb : b.gam ρ y) :
    (a.band b).gam ρ (x &&& y) := by
  unfold AV.band
  split
  · exact lift2_sound ha hb
  · next _ _ c _ =>
    rw [gam_single hb]
    have h1 := and_le_right x (w c)
    have h2 := and_le_left x (w c)
    have hw : (w c).toNat = c % M32 := by simp [w, M32]
    have hm := Nat.mod_le c M32
    split
    · next l h e =>
      have := bounds_sound ha e
      simp only [AV.gam]; omega
    · simp only [AV.gam]; omega
  · next _ _ c _ =>
    rw [gam_single ha]
    have h1 := and_le_left (w c) y
    have h2 := and_le_right (w c) y
    have hw : (w c).toNat = c % M32 := by simp [w, M32]
    have hm := Nat.mod_le c M32
    split
    · next l h e =>
      have := bounds_sound hb e
      simp only [AV.gam]; omega
    · simp only [AV.gam]; omega
  · trivial

theorem shr_mono {a b : Nat} (k : Nat) (h : a ≤ b) : a >>> k ≤ b >>> k := by
  rw [Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow]; exact Nat.div_le_div_right h

theorem shr_sound {ρ : Nat → Word} {a : AV} {x : Word} (k : Nat) (ha : a.gam ρ x) :
    (a.shr k).gam ρ (x >>> k) := by
  unfold AV.shr
  split
  · apply mkVals_sound
    refine ⟨x.toNat >>> k, List.mem_map.mpr ⟨_, ha, rfl⟩, ?_⟩
    rw [BitVec.toNat_ushiftRight]
    exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (by rw [Nat.shiftRight_eq_div_pow]; exact Nat.div_le_self _ _)
      (toNat_lt x))
  · split
    · next l h e =>
      have := bounds_sound ha e
      simp only [AV.gam, BitVec.toNat_ushiftRight]
      exact ⟨shr_mono k this.1, shr_mono k this.2⟩
    · trivial

theorem shl_sound {ρ : Nat → Word} {a : AV} {x : Word} (k : Nat) (ha : a.gam ρ x) :
    (a.shl k).gam ρ (x <<< k) := by
  unfold AV.shl
  split
  · apply mkVals_sound
    refine ⟨(x.toNat <<< k) % M32, List.mem_map.mpr ⟨_, ha, rfl⟩, ?_⟩
    rw [BitVec.toNat_shiftLeft]; simp [M32]
  · next l h =>
    simp only [AV.gam] at ha
    split
    · next hk =>
      simp only [AV.gam, BitVec.toNat_shiftLeft]
      have hx : x.toNat <<< k ≤ h <<< k := by
        rw [Nat.shiftLeft_eq, Nat.shiftLeft_eq]; exact Nat.mul_le_mul_right _ ha.2
      have hl : l <<< k ≤ x.toNat <<< k := by
        rw [Nat.shiftLeft_eq, Nat.shiftLeft_eq]; exact Nat.mul_le_mul_right _ ha.1
      rw [Nat.mod_eq_of_lt (by simp only [M32] at hk; omega)]
      exact ⟨hl, hx⟩
    · trivial
  · trivial

/-- 0 or 1 is always described by `bool01`. -/
theorem bool01_sound {ρ : Nat → Word} (b : Bool) : bool01.gam ρ (if b then 1 else 0) := by
  cases b <;> simp [bool01, AV.gam]

theorem ult_toNat (x y : Word) : x.ult y = decide (x.toNat < y.toNat) := by
  simp [BitVec.ult]

theorem sltu_sound {ρ : Nat → Word} {a b : AV} {x y : Word} (ha : a.gam ρ x) (hb : b.gam ρ y) :
    (a.sltu b).gam ρ (if x.ult y then 1 else 0) := by
  unfold AV.sltu
  split
  · exact lift2_sound (f := fun p q => if p.ult q then 1 else 0) ha hb
  · split
    · next l1 h1 l2 h2 e1 e2 =>
      have hx := bounds_sound ha e1
      have hy := bounds_sound hb e2
      rw [ult_toNat]
      split
      · rw [if_pos (by simp; omega)]; exact const_sound _ 1
      · split
        · rw [if_neg (by simp; omega)]; exact const_sound _ 0
        · exact bool01_sound _
    · exact bool01_sound _

theorem msb_false_of_lt {x : Word} (h : x.toNat < 2^31) : x.msb = false := by
  rw [BitVec.msb_eq_false_iff_two_mul_lt]; omega

theorem slt_sound {ρ : Nat → Word} {a b : AV} {x y : Word} (ha : a.gam ρ x) (hb : b.gam ρ y) :
    (a.slt b).gam ρ (if x.slt y then 1 else 0) := by
  unfold AV.slt
  split
  · exact lift2_sound (f := fun p q => if p.slt q then 1 else 0) ha hb
  · split
    · next l1 h1 l2 h2 e1 e2 =>
      have hx := bounds_sound ha e1
      have hy := bounds_sound hb e2
      split
      · next hn =>
        have hs : x.slt y = x.ult y :=
          BitVec.slt_eq_ult_of_msb_eq (by rw [msb_false_of_lt (by omega), msb_false_of_lt (by omega)])
        rw [hs, ult_toNat]
        split
        · rw [if_pos (by simp; omega)]; exact const_sound _ 1
        · split
          · rw [if_neg (by simp; omega)]; exact const_sound _ 0
          · exact bool01_sound _
      · exact bool01_sound _
    · exact bool01_sound _

theorem shamt_w (k : Nat) : (w k).toNat % 32 = k % 32 := by
  simp only [w, BitVec.toNat_ofNat]
  exact Nat.mod_mod_of_dvd k (by decide)

theorem alu_sound {ρ : Nat → Word} (op : AluOp) {a b : AV} {x y : Word} (ha : a.gam ρ x)
    (hb : b.gam ρ y) : (AV.alu op a b).gam ρ (E5R.alu op x y) := by
  cases op with
  | add => exact add_sound ha hb
  | sub => exact sub_sound ha hb
  | and => exact band_sound ha hb
  | or =>
    simp only [AV.alu, E5R.alu]
    split
    · exact lift2_sound ha hb
    · trivial
  | xor =>
    simp only [AV.alu, E5R.alu]
    split
    · exact lift2_sound ha hb
    · trivial
  | sll =>
    simp only [AV.alu, E5R.alu]
    split
    · next k => rw [gam_single hb, shamt_w]; exact shl_sound _ ha
    · trivial
  | srl =>
    simp only [AV.alu, E5R.alu]
    split
    · next k => rw [gam_single hb, shamt_w]; exact shr_sound _ ha
    · trivial
  | sra =>
    simp only [AV.alu, E5R.alu]
    split
    · exact lift2_sound (f := fun p q => p.sshiftRight (q.toNat % 32)) ha hb
    · next l h k =>
      rw [gam_single hb, shamt_w]
      split
      · next hh =>
        simp only [AV.gam] at ha
        rw [BitVec.sshiftRight_eq_of_msb_false (msb_false_of_lt (by omega))]
        simp only [AV.gam, BitVec.toNat_ushiftRight]
        exact ⟨shr_mono _ ha.1, shr_mono _ ha.2⟩
      · trivial
    · trivial
  | slt => exact slt_sound ha hb
  | sltu => exact sltu_sound ha hb

/-! ## Branches -/

theorem taken_self (c : BrCond) (x : Word) :
    taken c x x = (match c with | .eq | .ge | .geu => true | .ne | .lt | .ltu => false) := by
  cases c <;> simp [taken, BitVec.slt, BitVec.ult]

theorem slt_eq_ult_small {x y : Word} (hx : x.toNat < 2^31) (hy : y.toNat < 2^31) :
    x.slt y = x.ult y :=
  BitVec.slt_eq_ult_of_msb_eq (by rw [msb_false_of_lt hx, msb_false_of_lt hy])

/-- `canTake` says a branch can go a way whenever some described pair goes
    that way. -/
theorem canTake_sound {ρ : Nat → Word} (c : BrCond) {a b : AV} {x y : Word} (ha : a.gam ρ x)
    (hb : b.gam ρ y) :
    (taken c x y = true → (canTake c a b).1 = true) ∧
    (taken c x y = false → (canTake c a b).2 = true) := by
  unfold canTake
  split
  · next xs ys =>
    have mem : taken c x y ∈ xs.flatMap fun p => ys.map fun q => taken c (w p) (w q) :=
      List.mem_flatMap.mpr ⟨x.toNat, ha, List.mem_map.mpr ⟨y.toNat, hb, by rw [w_toNat, w_toNat]⟩⟩
    constructor
    · intro h; rw [h] at mem; simp only [List.any_eq_true]; exact ⟨true, mem, rfl⟩
    · intro h; rw [h] at mem; simp only [List.any_eq_true]; exact ⟨false, mem, rfl⟩
  · next s o s' o' =>
    split
    · next he =>
      obtain ⟨rfl, rfl⟩ := he
      simp only [AV.gam] at ha hb
      rw [ha, ← hb, taken_self]
      cases c <;> simp
    · exact ⟨fun _ => rfl, fun _ => rfl⟩
  · split
    · next l1 h1 l2 h2 e1 e2 =>
      have hx := bounds_sound ha e1
      have hy := bounds_sound hb e2
      cases c with
      | ltu => simp only [taken, ult_toNat, decide_eq_true_eq, decide_eq_false_iff_not]; omega
      | geu =>
        simp only [taken, ult_toNat, Bool.not_eq_true', decide_eq_false_iff_not,
          Bool.not_eq_false', decide_eq_true_eq]; omega
      | eq =>
        simp only [taken, beq_iff_eq, beq_eq_false_iff_ne]
        constructor
        · intro h; subst h; simp; omega
        · intro h
          simp only [Bool.not_eq_true', decide_eq_false_iff_not, not_and]
          intro e1 e2 e3; apply h; apply BitVec.eq_of_toNat_eq; omega
      | ne =>
        simp only [taken, bne_iff_ne, ne_eq, bne_eq_false_iff_eq]
        constructor
        · intro h
          simp only [Bool.not_eq_true', decide_eq_false_iff_not, not_and]
          intro e1 e2 e3; apply h; apply BitVec.eq_of_toNat_eq; omega
        · intro h; subst h; simp; omega
      | lt =>
        simp only
        split
        · next hs =>
          have := slt_eq_ult_small (x := x) (y := y) (by omega) (by omega)
          simp only [taken, this, ult_toNat, decide_eq_true_eq, decide_eq_false_iff_not, if_true]
          omega
        · exact ⟨fun _ => rfl, fun _ => rfl⟩
      | ge =>
        simp only
        split
        · next hs =>
          have := slt_eq_ult_small (x := x) (y := y) (by omega) (by omega)
          simp only [taken, this, ult_toNat, Bool.not_eq_true', decide_eq_false_iff_not,
            Bool.not_eq_false', decide_eq_true_eq]
          simp; omega
        · exact ⟨fun _ => rfl, fun _ => rfl⟩
    · exact ⟨fun _ => rfl, fun _ => rfl⟩

theorem w_toNat_of_lt {k : Nat} (h : k < M32) : (w k).toNat = k := by
  simp only [w, BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt h

theorem topRng_sound {ρ : Nat → Word} {a : AV} {x : Word} (h : a.gam ρ x) : a.topRng.gam ρ x := by
  cases a with
  | top => have := toNat_lt x; simp only [AV.topRng, AV.gam]; simp only [M32] at this ⊢; omega
  | _ => exact h

theorem ne_of_toNat {x : Word} {k : Nat} (hwk : (w k).toNat = k) (h : x ≠ w k) : x.toNat ≠ k :=
  fun e => h (BitVec.eq_of_toNat_eq (by rw [e, hwk]))

/-- Branch refinement against a constant on the right is sound for the
    direction the branch took. -/
theorem refineLCore_sound {ρ : Nat → Word} (c : BrCond) (t : Bool) {a : AV} {x : Word} {k : Nat}
    (hk : k < M32) (ha : a.gam ρ x) (ht : taken c x (w k) = t) : (refineLCore c t a k).gam ρ x := by
  have hwk := w_toNat_of_lt hk
  cases a with
  | vals l =>
    simp only [refineLCore, AV.gam, List.mem_filter]
    exact ⟨ha, by rw [w_toNat, ht]; simp⟩
  | rng l h =>
    simp only [AV.gam] at ha
    cases c <;> cases t <;> simp only [refineLCore]
    all_goals simp only [taken, ult_toNat, hwk, beq_iff_eq, bne_iff_ne, Bool.not_eq_true',
      decide_eq_true_eq, decide_eq_false_iff_not, Bool.not_eq_false', beq_eq_false_iff_ne,
      bne_eq_false_iff_eq, ne_eq, Bool.not_eq_eq_eq_not, Bool.not_true, Bool.not_false] at ht
    all_goals first
      | (simp only [AV.gam]; omega)
      | (split
         · simp only [AV.gam]; omega
         · simp only [AV.gam]; omega)
      | (have e := congrArg BitVec.toNat ht; rw [hwk] at e
         split
         · simp only [AV.gam]; simp only [List.mem_singleton]; omega
         · simp only [AV.gam]; omega)
      | (have hne := ne_of_toNat hwk ht
         split
         · simp only [AV.gam]; omega
         · split
           · simp only [AV.gam]; omega
           · simp only [AV.gam]; omega)
      | (simp only [AV.gam]; exact ha)
  | _ => exact ha

theorem refineL_sound {ρ : Nat → Word} (c : BrCond) (t : Bool) {a : AV} {x : Word} {k : Nat}
    (hk : k < M32) (ha : a.gam ρ x) (ht : taken c x (w k) = t) : (refineL c t a k).gam ρ x :=
  small_sound (refineLCore_sound c t hk (topRng_sound ha) ht)

theorem refineRCore_sound {ρ : Nat → Word} (c : BrCond) (t : Bool) {a : AV} {x : Word} {k : Nat}
    (hk : k < M32) (ha : a.gam ρ x) (ht : taken c (w k) x = t) : (refineRCore c t k a).gam ρ x := by
  have hwk := w_toNat_of_lt hk
  cases a with
  | vals l =>
    simp only [refineRCore, AV.gam, List.mem_filter]
    exact ⟨ha, by rw [w_toNat, ht]; simp⟩
  | rng l h =>
    simp only [AV.gam] at ha
    cases c <;> cases t <;> simp only [refineRCore]
    all_goals simp only [taken, ult_toNat, hwk, beq_iff_eq, bne_iff_ne, Bool.not_eq_true',
      decide_eq_true_eq, decide_eq_false_iff_not, Bool.not_eq_false', beq_eq_false_iff_ne,
      bne_eq_false_iff_eq, ne_eq, Bool.not_eq_eq_eq_not, Bool.not_true, Bool.not_false] at ht
    all_goals first
      | (simp only [AV.gam]; omega)
      | (have e := congrArg BitVec.toNat ht; rw [hwk] at e
         split
         · simp only [AV.gam]; simp only [List.mem_singleton]; omega
         · simp only [AV.gam]; omega)
      | (have hne : x.toNat ≠ k := fun e => ht (BitVec.eq_of_toNat_eq (by rw [e, hwk]))
         split
         · simp only [AV.gam]; omega
         · split
           · simp only [AV.gam]; omega
           · simp only [AV.gam]; omega)
      | (simp only [AV.gam]; exact ha)
  | _ => exact ha

theorem refineR_sound {ρ : Nat → Word} (c : BrCond) (t : Bool) {a : AV} {x : Word} {k : Nat}
    (hk : k < M32) (ha : a.gam ρ x) (ht : taken c (w k) x = t) : (refineR c t k a).gam ρ x :=
  small_sound (refineRCore_sound c t hk (topRng_sound ha) ht)

/-! ## Load extension -/

/-- A loaded value fits its access width. -/
def Fits (wd : Width) (x : Word) : Prop := x.toNat < 256 ^ wd.bytes

theorem and_ff (x : Word) (h : x.toNat < 256) : x &&& 0xff = x := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, show (0xff : Word).toNat = 2^8 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  omega

theorem and_ffff (x : Word) (h : x.toNat < 65536) : x &&& 0xffff = x := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, show (0xffff : Word).toNat = 2^16 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  omega

theorem sext_small (x : Word) (n : Nat) (hn : 0 < n) (hn' : n < 32) (h : x.toNat < 2 ^ (n - 1)) :
    (x.setWidth n).signExtend 32 = x := by
  have hx : x.toNat < 2 ^ n := Nat.lt_of_lt_of_le h (Nat.pow_le_pow_right (by decide) (by omega))
  rw [BitVec.signExtend_eq_setWidth_of_msb_false]
  · apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_setWidth, BitVec.toNat_setWidth, Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt x.isLt]
  · rw [BitVec.msb_eq_false_iff_two_mul_lt, BitVec.toNat_setWidth, Nat.mod_eq_of_lt hx]
    have : 2 * 2 ^ (n - 1) = 2 ^ n := by
      rw [← Nat.pow_succ']; congr 1; omega
    omega

/-- Extending a loaded value: unsigned loads are the raw value (it fits),
    signed ones are exact on sets and unchanged on non-negative ranges. -/
theorem extend_sound {ρ : Nat → Word} (wd : Width) (signed : Bool) {v : AV} {x : Word}
    (hv : v.gam ρ x) (hf : Fits wd x) : (v.extend wd signed).gam ρ (E5R.extend wd signed x) := by
  simp only [Fits, Width.bytes] at hf
  cases wd <;> cases signed
  · simp only [AV.extend, E5R.extend]; rw [and_ff x (by omega)]; exact hv
  · simp only [AV.extend, E5R.extend]
    split
    · next l =>
      apply mkVals_sound
      refine ⟨((x.setWidth 8).signExtend 32).toNat, List.mem_map.mpr ⟨x.toNat, hv, ?_⟩, ?_⟩
      · simp [E5R.extend, w_toNat]
      · exact Nat.mod_eq_of_lt (BitVec.isLt _)
    · next l h =>
      simp only [AV.gam] at hv
      by_cases hh : h < signedLimit .b
      · rw [if_pos hh]; simp only [signedLimit] at hh
        rw [sext_small x 8 (by decide) (by decide) (by simp; omega)]
        exact hv
      · rw [if_neg hh]; trivial
    · trivial
  · simp only [AV.extend, E5R.extend]; rw [and_ffff x (by omega)]; exact hv
  · simp only [AV.extend, E5R.extend]
    split
    · next l =>
      apply mkVals_sound
      refine ⟨((x.setWidth 16).signExtend 32).toNat, List.mem_map.mpr ⟨x.toNat, hv, ?_⟩, ?_⟩
      · simp [E5R.extend, w_toNat]
      · exact Nat.mod_eq_of_lt (BitVec.isLt _)
    · next l h =>
      simp only [AV.gam] at hv
      by_cases hh : h < signedLimit .h
      · rw [if_pos hh]; simp only [signedLimit] at hh
        rw [sext_small x 16 (by decide) (by decide) (by simp; omega)]
        exact hv
      · rw [if_neg hh]; trivial
    · trivial
  · simp only [AV.extend, E5R.extend]; exact hv
  · simp only [AV.extend, E5R.extend]; exact hv

/-! ## Memory cells -/

/-- The address a cell describes: absolute, or relative to the interrupted
    stack pointer `ρ 2`. -/
def Cell.at (ρ : Nat → Word) (c : Cell) : Word :=
  match c.base with
  | .abs => E5R.AI.w c.addr
  | .rel => ρ 2 + E5R.AI.w c.addr

/-- A cell's fact holds in `ram` (when its guard does). -/
def Cell.holds (ρ : Nat → Word) (ram : Word → BitVec 8) (c : Cell) : Prop :=
  (∀ g, c.guard = some g → (ramRead ram (E5R.AI.w g.1) g.2.1).toNat ≠ g.2.2) →
  c.v.gam ρ (ramRead ram (c.at ρ) c.w)

def MemHolds (ρ : Nat → Word) (ram : Word → BitVec 8) (mem : List Cell) : Prop :=
  ∀ c ∈ mem, c.holds ρ ram

def addrOf (ρ : Nat → Word) (base : Base) (a : Nat) : Word :=
  match base with
  | .abs => w a
  | .rel => ρ 2 + w a

theorem find_map_some {α β : Type} {p : α → Bool} {f : α → β} {l : List α} {v : β}
    (h : (l.find? p).map f = some v) : ∃ c ∈ l, p c = true ∧ f c = v := by
  cases hf : l.find? p with
  | none => rw [hf] at h; simp at h
  | some c =>
    rw [hf] at h; simp only [Option.map_some, Option.some.injEq] at h
    exact ⟨c, List.mem_of_find?_eq_some hf, List.find?_some hf, h⟩

theorem cell_at {ρ : Nat → Word} {c : Cell} {base : Base} {a : Nat} (hb : c.base = base)
    (ha : c.addr = a) : c.at ρ = addrOf ρ base a := by
  cases base <;> simp [Cell.at, addrOf, hb, ha]

theorem plain_sound {ρ : Nat → Word} {ram : Word → BitVec 8} {mem : List Cell} {base : Base}
    {a : Nat} {wd : Width} {v : AV} (hm : MemHolds ρ ram mem) (h : plain mem base a wd = some v) :
    v.gam ρ (ramRead ram (addrOf ρ base a) wd) := by
  obtain ⟨c, hc, hp, rfl⟩ := find_map_some h
  simp only [Bool.and_eq_true, beq_iff_eq, Option.isNone_iff_eq_none] at hp
  obtain ⟨⟨⟨hb, ha⟩, hw⟩, hg⟩ := hp
  have := hm c hc (fun g e => by rw [hg] at e; cases e)
  rw [← hw, ← cell_at hb ha]; exact this

theorem guardHolds_sound {ρ : Nat → Word} {ram : Word → BitVec 8} {mem : List Cell}
    {g : Nat × Width × Nat} (hm : MemHolds ρ ram mem) (h : guardHolds mem g = true) :
    (ramRead ram (w g.1) g.2.1).toNat ≠ g.2.2 := by
  unfold guardHolds at h
  cases hp : plain mem .abs g.1 g.2.1 with
  | none => rw [hp] at h; simp at h
  | some v =>
    have hv := plain_sound hm hp
    simp only [addrOf] at hv
    rw [hp] at h
    cases v with
    | vals l =>
      intro e
      simp only [AV.gam] at hv
      rw [e] at hv
      simp [hv] at h
    | rng lo hi =>
      simp only [Bool.or_eq_true, decide_eq_true_eq] at h
      simp only [AV.gam] at hv; omega
    | _ => simp at h

theorem lookup_sound {ρ : Nat → Word} {ram : Word → BitVec 8} {mem : List Cell} {base : Base}
    {a : Nat} {wd : Width} {v : AV} (hm : MemHolds ρ ram mem) (h : lookup mem base a wd = some v) :
    v.gam ρ (ramRead ram (addrOf ρ base a) wd) := by
  obtain ⟨c, hc, hp, rfl⟩ := find_map_some h
  simp only [Bool.and_eq_true, beq_iff_eq] at hp
  obtain ⟨⟨⟨hb, ha⟩, hw⟩, hg⟩ := hp
  have := hm c hc (fun g e => by rw [e] at hg; exact guardHolds_sound hm hg)
  rw [← hw, ← cell_at hb ha]; exact this

theorem ramRead_b_lt (ram : Word → BitVec 8) (a : Word) : (ramRead ram a .b).toNat < 256 := by
  have := (ram a).isLt
  simp only [ramRead, BitVec.toNat_ofNat]; omega

theorem ramRead_h_lt (ram : Word → BitVec 8) (a : Word) : (ramRead ram a .h).toNat < 65536 := by
  have := (ram a).isLt; have := (ram (a+1)).isLt
  simp only [ramRead, BitVec.toNat_ofNat]; omega

theorem ramRead_fits (ram : Word → BitVec 8) (a : Word) (wd : Width) : Fits wd (ramRead ram a wd) := by
  cases wd
  · exact ramRead_b_lt ram a
  · exact ramRead_h_lt ram a
  · simp only [Fits, Width.bytes]; exact BitVec.isLt _

theorem loadCell_sound {ρ : Nat → Word} {ram : Word → BitVec 8} {mem : List Cell} {base : Base}
    {a : Nat} {wd : Width} (hm : MemHolds ρ ram mem) :
    (loadCell mem base a wd).gam ρ (ramRead ram (addrOf ρ base a) wd) := by
  unfold loadCell
  split
  · next v hv => exact lookup_sound hm hv
  · cases wd
    · simp only [AV.gam]; have := ramRead_b_lt ram (addrOf ρ base a); omega
    · simp only [AV.gam]; have := ramRead_h_lt ram (addrOf ρ base a); omega
    · trivial

/-! ## Writing RAM -/

/-- The bytes an access of `wd` at `a` touches. -/
def Touches (a : Word) (wd : Width) (x : Word) : Prop := ∃ k < wd.bytes, x = a + w k

/-- Two accesses share no byte. -/
def Disj (a : Word) (wd : Width) (b : Word) (wd' : Width) : Prop :=
  ∀ x, Touches a wd x → ¬ Touches b wd' x

theorem w0 : w 0 = 0 := rfl
theorem w1 : w 1 = 1 := rfl
theorem w2 : w 2 = 2 := rfl
theorem w3 : w 3 = 3 := rfl

theorem ramWrite_other (ram : Word → BitVec 8) (a v : Word) (wd : Width) (x : Word)
    (h : ¬ Touches a wd x) : ramWrite ram a v wd x = ram x := by
  have hk : ∀ k, k < wd.bytes → x ≠ a + w k := fun k hk e => h ⟨k, hk, e⟩
  have n0 : x ≠ a := by have := hk 0 (by cases wd <;> decide); simpa [w] using this
  cases wd
  · simp only [ramWrite, ramPut]; rw [if_neg n0]
  · simp only [ramWrite, ramPut]
    split
    · next he => exact absurd he (hk 1 (by decide))
    · first | rfl | rw [if_neg n0]
  · simp only [ramWrite, ramPut]
    split
    · next he => exact absurd he (hk 3 (by decide))
    · split
      · next he => exact absurd he (hk 2 (by decide))
      · split
        · next he => exact absurd he (hk 1 (by decide))
        · first | rfl | rw [if_neg n0]

theorem ramRead_frame (ram : Word → BitVec 8) (a v : Word) (wd : Width) (b : Word) (wd' : Width)
    (h : Disj b wd' a wd) : ramRead (ramWrite ram a v wd) b wd' = ramRead ram b wd' := by
  have t : ∀ k < wd'.bytes, ramWrite ram a v wd (b + w k) = ram (b + w k) :=
    fun k hk => ramWrite_other ram a v wd _ (h _ ⟨k, hk, rfl⟩)
  have e0 : ramWrite ram a v wd b = ram b := by
    have := t 0 (by cases wd' <;> decide); simpa [w] using this
  cases wd'
  · simp only [ramRead, e0]
  · have e1 := t 1 (by decide)
    simp only [ramRead, e0]; rw [show b + 1 = b + w 1 from rfl, e1]
  · have e1 := t 1 (by decide); have e2 := t 2 (by decide); have e3 := t 3 (by decide)
    simp only [ramRead, e0]
    rw [show b + 1 = b + w 1 from rfl, show b + 2 = b + w 2 from rfl,
      show b + 3 = b + w 3 from rfl, e1, e2, e3]

theorem ramRead_ramWrite_b (ram : Word → BitVec 8) (a v : Word) :
    ramRead (ramWrite ram a v .b) a .b = v &&& 0xff := by
  apply BitVec.eq_of_toNat_eq
  simp only [ramRead, ramWrite, ramPut, if_true, byteOf, BitVec.toNat_ofNat, BitVec.toNat_and]
  rw [show (0xff : Word).toNat = 2^8 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  have := v.isLt; simp; omega

theorem ramRead_ramWrite_h (ram : Word → BitVec 8) (a v : Word) :
    ramRead (ramWrite ram a v .h) a .h = v &&& 0xffff := by
  have d : a + 1 ≠ a := by
    intro e; have := congrArg BitVec.toNat e; simp [BitVec.toNat_add] at this; omega
  apply BitVec.eq_of_toNat_eq
  simp only [ramRead, ramWrite, ramPut, if_true, d, Ne.symm d, if_false, byteOf, BitVec.toNat_ofNat,
    BitVec.toNat_and]
  rw [show (0xffff : Word).toNat = 2^16 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  have := v.isLt; simp; omega

theorem ramRead_ramWrite_w' (ram : Word → BitVec 8) (a v : Word) :
    ramRead (ramWrite ram a v .w) a .w = v := ramRead_ramWrite_w ram a v

/-- What a store of `v` reads back as, at its own address and width. -/
def stored (wd : Width) (v : Word) : Word :=
  match wd with
  | .b => v &&& 0xff
  | .h => v &&& 0xffff
  | .w => v

theorem ramRead_ramWrite_self (ram : Word → BitVec 8) (a v : Word) (wd : Width) :
    ramRead (ramWrite ram a v wd) a wd = stored wd v := by
  cases wd
  · exact ramRead_ramWrite_b ram a v
  · exact ramRead_ramWrite_h ram a v
  · exact ramRead_ramWrite_w ram a v

/-! ## Joins -/

theorem join_sound_left {ρ : Nat → Word} {a b : AV} {x : Word} (h : a.gam ρ x) : (a.join b).gam ρ x := by
  unfold AV.join
  split
  · trivial
  · trivial
  · next xs ys => exact mkVals_sound ⟨x.toNat, List.mem_append_left _ h, Nat.mod_eq_of_lt (toNat_lt x)⟩
  · next s o s' o' =>
    split
    · exact h
    · trivial
  · trivial
  · trivial
  · split
    · next l1 h1 l2 h2 e1 e2 =>
      have := bounds_sound h e1
      simp only [AV.gam]; omega
    · next e1 =>
      exfalso
      cases a with
      | vals l => cases l with
        | nil => simp [AV.gam] at h
        | cons _ _ => simp [AV.bounds] at e1
      | rng _ _ => simp [AV.bounds] at e1
      | top => simp [AV.bounds] at e1
      | sym _ _ => simp_all
    · exact h

theorem join_sound_right {ρ : Nat → Word} {a b : AV} {x : Word} (h : b.gam ρ x) : (a.join b).gam ρ x := by
  unfold AV.join
  split
  · trivial
  · trivial
  · next xs ys => exact mkVals_sound ⟨x.toNat, List.mem_append_right _ h, Nat.mod_eq_of_lt (toNat_lt x)⟩
  · next s o s' o' =>
    split
    · next he => obtain ⟨rfl, rfl⟩ := he; exact h
    · trivial
  · trivial
  · trivial
  · split
    · next l1 h1 l2 h2 e1 e2 =>
      have := bounds_sound h e2
      simp only [AV.gam]; omega
    · exact h
    · exfalso
      cases b with
      | vals l => cases l <;> simp_all [AV.bounds, AV.gam]
      | _ => simp_all [AV.bounds, AV.gam]

/-! ## Stores -/

/-- What a store must know about each cell it keeps: the cell's bytes, and
    its guard's, are untouched, or the store wrote exactly the guard value. -/
def StoreSep (ρ : Nat → Word) (mem : List Cell) (base : Base) (a : Nat) (wd : Width) (V : AV) : Prop :=
  ∀ c ∈ mem, c.staleAfter base a wd V = false →
    Disj (c.at ρ) c.w (addrOf ρ base a) wd ∧
    (∀ g, c.guard = some g → Disj (w g.1) g.2.1 (addrOf ρ base a) wd ∨
      (base = .abs ∧ g.1 = a ∧ g.2.1 = wd ∧ V = .vals [g.2.2]))

theorem kept_holds {ρ : Nat → Word} {ram : Word → BitVec 8} {c : Cell} {base : Base} {a : Nat}
    {wd : Width} {V : AV} {v : Word} (hc : c.holds ρ ram) (hV : V.gam ρ (stored wd v))
    (hd : Disj (c.at ρ) c.w (addrOf ρ base a) wd)
    (hg : ∀ g, c.guard = some g → Disj (w g.1) g.2.1 (addrOf ρ base a) wd ∨
      (base = .abs ∧ g.1 = a ∧ g.2.1 = wd ∧ V = .vals [g.2.2])) :
    c.holds ρ (ramWrite ram (addrOf ρ base a) v wd) := by
  intro hguard
  rw [ramRead_frame _ _ _ _ _ _ hd]
  apply hc
  intro g hgc
  rcases hg g hgc with hdg | ⟨hb, ha, hw, hv⟩
  · have := hguard g hgc; rwa [ramRead_frame _ _ _ _ _ _ hdg] at this
  · exfalso
    have := hguard g hgc
    subst hb; subst hv
    rw [show w g.1 = addrOf ρ .abs a from by rw [ha]; rfl, hw, ramRead_ramWrite_self] at this
    simp only [AV.gam, List.mem_singleton] at hV
    exact this hV

theorem storeStrong_sound {ρ : Nat → Word} {ram : Word → BitVec 8} {mem : List Cell} {base : Base}
    {a : Nat} {wd : Width} {V : AV} {v : Word} (hm : MemHolds ρ ram mem)
    (hV : V.gam ρ (stored wd v)) (hsep : StoreSep ρ mem base a wd V) :
    MemHolds ρ (ramWrite ram (addrOf ρ base a) v wd) (storeStrong mem base a wd V) := by
  intro c hc
  simp only [storeStrong, List.mem_cons, List.mem_filter, Bool.not_eq_true'] at hc
  rcases hc with rfl | ⟨hc, hns⟩
  · intro _
    show V.gam ρ (ramRead _ (Cell.at ρ ⟨base, a, wd, V, none⟩) wd)
    rw [cell_at rfl rfl, ramRead_ramWrite_self]; exact hV
  · obtain ⟨hd, hg⟩ := hsep c hc hns
    exact kept_holds (hm c hc) hV hd hg

/-- A weak store at a candidate address only weakens or forgets facts, so it
    keeps every fact that held, in any memory. -/
theorem storeWeak_weakens {ρ : Nat → Word} {R : Word → BitVec 8} {mem : List Cell} {base : Base}
    {a : Nat} {wd : Width} {V : AV} (hm : MemHolds ρ R mem) :
    MemHolds ρ R (storeWeak mem base a wd V) := by
  intro c hc
  simp only [storeWeak, List.mem_filterMap] at hc
  obtain ⟨d, hd, he⟩ := hc
  split at he
  · next hx =>
    simp only [Option.some.injEq] at he; subst he
    intro hg
    exact join_sound_left (hm d hd hg)
  · split at he
    · simp at he
    · simp only [Option.some.injEq] at he; subst he; exact hm _ hd

/-- At the address actually written, the weak store's facts hold after the
    write. -/
theorem storeWeak_write {ρ : Nat → Word} {ram : Word → BitVec 8} {mem : List Cell} {base : Base}
    {a : Nat} {wd : Width} {V : AV} {v : Word} (hm : MemHolds ρ ram mem)
    (hV : V.gam ρ (stored wd v)) (hsep : StoreSep ρ mem base a wd V) :
    MemHolds ρ (ramWrite ram (addrOf ρ base a) v wd) (storeWeak mem base a wd V) := by
  intro c hc
  simp only [storeWeak, List.mem_filterMap] at hc
  obtain ⟨d, hd, he⟩ := hc
  split at he
  · next hx =>
    simp only [Option.some.injEq] at he; subst he
    simp only [Bool.and_eq_true, beq_iff_eq, Option.isNone_iff_eq_none] at hx
    obtain ⟨⟨⟨hb, ha⟩, hw⟩, hg⟩ := hx
    intro _
    show (d.v.join V).gam ρ (ramRead _ (d.at ρ) d.w)
    rw [cell_at hb ha, hw, ramRead_ramWrite_self]
    exact join_sound_right hV
  · split at he
    · simp at he
    · next _ hns =>
      simp only [Option.some.injEq] at he; subst he
      obtain ⟨hd', hg⟩ := hsep _ hd (by simpa using hns)
      exact kept_holds (hm _ hd) hV hd' hg

/-- Pinning a just-loaded value keeps every fact and adds a true one. -/
theorem setPlain_sound {ρ : Nat → Word} {ram : Word → BitVec 8} {mem : List Cell} {a : Nat}
    {wd : Width} {v : AV} (hm : MemHolds ρ ram mem) (hv : v.gam ρ (ramRead ram (w a) wd)) :
    MemHolds ρ ram (setPlain mem a wd v) := by
  intro c hc
  simp only [setPlain, List.mem_cons, List.mem_filter] at hc
  rcases hc with rfl | ⟨hc, _⟩
  · intro _; exact hv
  · exact hm c hc

/-! ## From address arithmetic to disjointness -/

theorem toNat_add_small (A : Word) {k : Nat} (h : A.toNat + k < M32) : (A + w k).toNat = A.toNat + k := by
  simp only [w, BitVec.toNat_add, BitVec.toNat_ofNat]; simp only [M32] at h; omega

/-- Accesses whose byte ranges are disjoint as numbers, and do not wrap
    around the address space, share no byte. -/
theorem disj_of_nat {A B : Word} {wa wb : Width} (ha : A.toNat + wa.bytes ≤ M32)
    (hb : B.toNat + wb.bytes ≤ M32) (h : A.toNat + wa.bytes ≤ B.toNat ∨ B.toNat + wb.bytes ≤ A.toNat) :
    Disj A wa B wb := by
  rintro x ⟨i, hi, rfl⟩ ⟨j, hj, e⟩
  have e1 := toNat_add_small A (k := i) (by omega)
  have e2 := toNat_add_small B (k := j) (by omega)
  have := congrArg BitVec.toNat e
  omega

theorem toNat_w_of_lt {a : Nat} (h : a < M32) : (w a).toNat = a := w_toNat_of_lt h

/-- Two absolute ranges the checker's `overlap` says are apart, both below
    the top of the address space, share no byte. -/
theorem disj_abs {a b : Nat} {wa wb : Width} (ha : a + wa.bytes ≤ M32) (hb : b + wb.bytes ≤ M32)
    (h : overlap a wa.bytes b wb.bytes = false) : Disj (w a) wa (w b) wb := by
  have ea : (w a).toNat = a := toNat_w_of_lt (by cases wa <;> simp [Width.bytes] at ha ⊢ <;> omega)
  have eb : (w b).toNat = b := toNat_w_of_lt (by cases wb <;> simp [Width.bytes] at hb ⊢ <;> omega)
  apply disj_of_nat (by rw [ea]; exact ha) (by rw [eb]; exact hb)
  simp only [overlap, Bool.and_eq_false_iff, decide_eq_false_iff_not] at h
  rw [ea, eb]; omega

/-! ## Loads -/

def ValidImg (img : List Segment) : Prop := ∀ seg ∈ img, ∀ b ∈ seg.bytes, b < 256

theorem validImg_of_check {img : List Segment} (h : img.all (fun seg => seg.bytes.all (· < 256)) = true) :
    ValidImg img := by
  intro seg hs b hb
  simp only [List.all_eq_true, decide_eq_true_eq] at h
  exact h seg hs b hb

theorem romByte_lt {img : List Segment} (hv : ValidImg img) {a : Nat} {f : Bool} {b : Nat}
    (h : romByte? img a f = some b) : b < 256 := by
  unfold romByte? at h
  split at h
  · next seg hseg =>
    unfold Segment.byte? at h
    split at h
    · exact hv seg (List.mem_of_find?_eq_some hseg) b (List.mem_of_getElem? h)
    · simp at h
  · simp at h

theorem romGo_lt {img : List Segment} (hv : ValidImg img) {a : Nat} {f : Bool} :
    ∀ k x, romRead?.go img a f k = some x → x < 256 ^ k
  | 0, x, h => by simp [romRead?.go] at h; subst h; decide
  | k+1, x, h => by
    simp only [romRead?.go] at h
    cases hb : romByte? img (a + k) f with
    | none => simp [hb] at h
    | some b =>
      cases hr : romRead?.go img a f k with
      | none => simp [hb, hr] at h
      | some r =>
        simp only [hb, hr, bind, Option.bind, pure, Option.some.injEq] at h
        subst h
        have h1 := romByte_lt hv hb
        have h2 := romGo_lt hv k r hr
        rw [Nat.pow_succ]
        have : b * 256 ^ k ≤ 255 * 256 ^ k := Nat.mul_le_mul_right _ (by omega)
        omega

theorem romRead_fits {img : List Segment} (hv : ValidImg img) {a : Nat} {wd : Width} {r : Word}
    (h : romRead? img a wd.bytes false = some r) : Fits wd r := by
  unfold romRead? at h
  cases hg : romRead?.go img a false wd.bytes with
  | none => rw [hg] at h; simp at h
  | some x =>
    rw [hg] at h; simp only [Option.map_some, Option.some.injEq] at h; subst h
    have := romGo_lt hv wd.bytes x hg
    simp only [Fits, BitVec.toNat_ofNat]
    cases wd <;> simp [Width.bytes] at this ⊢ <;> omega

/-- The concrete facts behind `classify`'s answers. -/
theorem classify_ram {cfg : Config} {a : Nat} {wd : Width} (h : classify cfg a wd = some .ram) :
    a % wd.bytes = 0 ∧ cfg.board.inRam (w a) wd.bytes = true := by
  unfold classify at h
  split at h
  · simp at h
  · next ha =>
    split at h
    · exact ⟨by simpa using ha, by assumption⟩
    · split at h
      · simp at h
      · split at h
        · split at h <;> simp at h
        · simp at h

theorem classify_rom {cfg : Config} {a : Nat} {wd : Width} {v : Nat} (h : classify cfg a wd = some (.rom v)) :
    a % wd.bytes = 0 ∧ cfg.board.inRam (w a) wd.bytes = false ∧
    ∃ r, romRead? cfg.img a wd.bytes false = some r ∧ r.toNat = v := by
  unfold classify at h
  split at h
  · simp at h
  · next ha =>
    split at h
    · simp at h
    · next hr =>
      split at h
      · next r hrom =>
        simp only [Option.some.injEq, Target.rom.injEq] at h
        exact ⟨by simpa using ha, by simpa using hr, r, hrom, h⟩
      · split at h
        · split at h <;> simp at h
        · simp at h

theorem classify_dev {cfg : Config} {a : Nat} {wd : Width} {d : DevReg} (h : classify cfg a wd = some (.dev d)) :
    a % wd.bytes = 0 ∧ cfg.board.inRam (w a) wd.bytes = false ∧
    romRead? cfg.img a wd.bytes false = none ∧ cfg.board.device? (w a) = some d ∧ wd = .w := by
  unfold classify at h
  split at h
  · simp at h
  · next ha =>
    split at h
    · simp at h
    · next hr =>
      split at h
      · simp at h
      · next hrom =>
        split at h
        · next d' hd =>
          split at h
          · next hw =>
            simp only [Option.some.injEq, Target.dev.injEq] at h; subst h
            exact ⟨by simpa using ha, by simpa using hr, hrom, hd, hw⟩
          · simp at h
        · simp at h

/-- A fold that joins per-address contributions covers each contribution. -/
theorem foldJoin_covers {f : Nat → Option AV} {ρ : Nat → Word} :
    ∀ (as : List Nat) (init v : AV),
      as.foldlM (init := init) (fun acc a => (f a).map acc.join) = some v →
      (∀ x, init.gam ρ x → v.gam ρ x) ∧ ∀ a ∈ as, ∃ c, f a = some c ∧ ∀ x, c.gam ρ x → v.gam ρ x
  | [], init, v, h => by
    simp only [List.foldlM, pure, Option.some.injEq] at h; subst h
    exact ⟨fun _ h => h, by simp⟩
  | a :: as, init, v, h => by
    simp only [List.foldlM, bind, Option.bind] at h
    cases hf : f a with
    | none => rw [hf] at h; simp at h
    | some c =>
      rw [hf] at h; simp only [Option.map_some] at h
      obtain ⟨hmono, hcov⟩ := foldJoin_covers as (init.join c) v h
      refine ⟨fun x hx => hmono x (join_sound_left hx), ?_⟩
      intro b hb
      simp only [List.mem_cons] at hb
      rcases hb with rfl | hb
      · exact ⟨c, hf, fun x hx => hmono x (join_sound_right hx)⟩
      · exact hcov b hb

/-- A load from a set of absolute candidates: the platform does not fault and
    hands the continuation a value the abstract load describes. -/
theorem absLoad_vals_sound {cfg : Config} {s : AState} {as : List Nat} {wd : Width} {atomic : Bool}
    {v : AV} (h : absLoad cfg s (.vals as) wd atomic = some v) (hv : ValidImg cfg.img)
    {ρ : Nat → Word} {ram : Word → BitVec 8} {A : Word} (hA : A.toNat ∈ as)
    (hm : MemHolds ρ ram s.mem) (o : Oracle) (i : Nat) (evs : List Event) (k : Word → Eff) :
    ∃ r i', interp cfg.board cfg.img o (.load wd A atomic k) ram i evs =
      interp cfg.board cfg.img o (k r) ram i' evs ∧ v.gam ρ r ∧ Fits wd r := by
  simp only [absLoad] at h
  obtain ⟨_, hcov⟩ := foldJoin_covers (ρ := ρ) as _ v h
  obtain ⟨c, hc, hcv⟩ := hcov _ hA
  have hAw : w A.toNat = A := w_toNat A
  unfold loadAt at hc
  split at hc
  · next hcl =>
    obtain ⟨hal, hin⟩ := classify_ram hcl
    rw [hAw] at hin
    simp only [Option.some.injEq] at hc; subst hc
    refine ⟨ramRead ram A wd, i, interp_load_ram o hal hin, hcv _ ?_, ramRead_fits _ _ _⟩
    have := loadCell_sound (ρ := ρ) (base := .abs) (a := A.toNat) (wd := wd) hm
    simp only [addrOf, hAw] at this; exact this
  · next vv hcl =>
    obtain ⟨hal, hin, r, hr, hrv⟩ := classify_rom hcl
    rw [hAw] at hin
    split at hc
    · simp at hc
    · next hat =>
      simp only [Option.some.injEq] at hc; subst hc
      refine ⟨r, i, interp_load_rom o hal hin (by simpa using hat) hr, hcv _ ?_, romRead_fits hv hr⟩
      exact const_sound' (by rw [hrv]; exact (Nat.mod_eq_of_lt (by rw [← hrv]; exact toNat_lt r)).symm)
  · next d hcl =>
    obtain ⟨hal, hin, hr, hd, hw⟩ := classify_dev hcl
    rw [hAw] at hin hd
    split at hc
    · simp at hc
    · next hat =>
      simp only [Bool.or_eq_true, not_or, Bool.not_eq_true', Bool.not_eq_false'] at hat
      simp only [Option.some.injEq] at hc; subst hc
      refine ⟨o i, i + 1, interp_load_dev o hal hin (by simpa using hat.1) hr hd (by simpa using hat.2) hw,
        hcv _ trivial, ?_⟩
      subst hw; simp only [Fits, Width.bytes]; exact BitVec.isLt _
  · simp at hc

/-! ## Stores -/

theorem inRam_nat {B : Board} {a : Nat} {n : Nat} (ha : a < M32) (h : B.inRam (w a) n = true) :
    B.ramBase ≤ a ∧ a + n ≤ B.ramBase + B.ramSize := by
  simp only [Board.inRam, Bool.and_eq_true, decide_eq_true_eq] at h
  rw [toNat_w_of_lt ha] at h; exact h

/-- The checker's well-formedness and overlap tests give the separation an
    absolute strong store needs for the cells it keeps, provided relative
    cells (handler frames) are apart from it. -/
theorem storeSep_abs {cfg : Config} {ρ : Nat → Word} {mem : List Cell} {a : Nat} {wd : Width} {V : AV}
    (hram : cfg.board.ramBase + cfg.board.ramSize ≤ M32)
    (hwf : ∀ c ∈ mem, c.wf cfg = true) (ha : a < M32) (hin : cfg.board.inRam (w a) wd.bytes = true)
    (hrel : ∀ c ∈ mem, c.base = .rel → Disj (c.at ρ) c.w (w a) wd) :
    StoreSep ρ mem .abs a wd V := by
  have hA := inRam_nat ha hin
  intro c hc hns
  have hw := hwf c hc
  simp only [Cell.wf, Bool.and_eq_true] at hw
  obtain ⟨hcell, hguard⟩ := hw
  simp only [Cell.staleAfter, Bool.or_eq_false_iff] at hns
  obtain ⟨hhit, hg⟩ := hns
  constructor
  · cases hb : c.base with
    | rel => exact hrel c hc hb
    | abs =>
      simp only [hb, Bool.and_eq_true, decide_eq_true_eq] at hcell
      have hC := inRam_nat hcell.1 hcell.2
      simp only [Cell.hits, hb, beq_self_eq_true, Bool.true_and] at hhit
      have : c.at ρ = w c.addr := by simp [Cell.at, hb]
      rw [this]
      exact disj_abs (by omega) (by omega) hhit
  · intro g hgc
    rw [hgc] at hguard hg
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hguard
    have hG := inRam_nat hguard.1 hguard.2
    simp only [beq_self_eq_true, Bool.true_and, Bool.and_eq_false_iff, Bool.not_eq_false',
      Bool.and_eq_true, beq_iff_eq] at hg
    rcases hg with hov | ⟨⟨⟨h1, h2⟩, h3⟩⟩
    · exact .inl (disj_abs (by omega) (by omega) hov)
    · exact .inr ⟨rfl, h1, h2, h3⟩

/-- The device-write property: the first `allow` entry for the written
    register, if any, bounds the written value. -/
def EvOk (cfg : Config) (e : Event) : Prop :=
  match cfg.allow.find? (·.addr == e.addr.toNat) with
  | none => True
  | some al => al.lo ≤ e.val.toNat ∧ e.val.toNat ≤ al.hi

theorem writeOk_sound {cfg : Config} {a : Nat} {V : AV} {ρ : Nat → Word} {x A : Word}
    (h : cfg.writeOk a V = true) (hV : V.gam ρ x) (hA : A.toNat = a) : EvOk cfg ⟨A, x⟩ := by
  unfold Config.writeOk at h
  unfold EvOk
  simp only [hA]
  split
  · trivial
  · next al hal =>
    rw [hal] at h
    simp only at h
    cases hb : V.bounds with
    | none => rw [hb] at h; simp at h
    | some p =>
      obtain ⟨l, hh⟩ := p
      rw [hb] at h
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h
      have := bounds_sound hV hb
      exact ⟨by omega, by omega⟩

/-- What one store did to the machine: wrote RAM, or emitted an allowed
    device event. -/
inductive StoreEffect (cfg : Config) (ram : Word → BitVec 8) (A x : Word) (wd : Width) :
    (Word → BitVec 8) → List Event → Prop
  | ram : StoreEffect cfg ram A x wd (ramWrite ram A x wd) []
  | dev : EvOk cfg ⟨A, x⟩ → StoreEffect cfg ram A x wd ram [⟨A, x⟩]

/-- One candidate address of a store, at the address actually written. -/
theorem storeAt_written {cfg : Config} {s : AState} {mem mem' : List Cell} {a : Nat} {wd : Width}
    {V : AV} {atomic strong : Bool} (h : storeAt cfg s mem a wd V atomic strong = some mem')
    {ρ : Nat → Word} {ram : Word → BitVec 8} {A x : Word} (hAa : A.toNat = a)
    (hV : V.gam ρ (stored wd x)) (hVw : V.gam ρ x ∨ wd ≠ .w) (hm : MemHolds ρ ram mem)
    (hsep : cfg.board.inRam (w a) wd.bytes = true → (s.hnd = true → cfg.isStatic a wd.bytes = true) →
      StoreSep ρ mem .abs a wd V)
    (o : Oracle) (i : Nat) (evs : List Event) (k : Eff) :
    ∃ ram' evs', interp cfg.board cfg.img o (.store wd A x atomic k) ram i evs =
        interp cfg.board cfg.img o k ram' i (evs ++ evs') ∧ StoreEffect cfg ram A x wd ram' evs' ∧
      MemHolds ρ ram' mem' := by
  have hAw : w a = A := by rw [← hAa]; exact w_toNat A
  unfold storeAt at h
  split at h
  · next hcl =>
    obtain ⟨hal, hin⟩ := classify_ram hcl
    split at h
    · simp at h
    · simp only [Option.some.injEq] at h; subst h
      refine ⟨ramWrite ram A x wd, [], ?_, .ram, ?_⟩
      · rw [List.append_nil]; rw [hAw] at hin; exact interp_store_ram o (by rw [hAa]; exact hal) hin
      · next hst =>
        have hs := hsep hin (fun hh => by simpa [hh] using hst)
        rw [← hAw]
        cases strong
        · exact storeWeak_write hm hV hs
        · exact storeStrong_sound hm hV hs
  · next d hcl =>
    obtain ⟨hal, hin, _, hd, hw⟩ := classify_dev hcl
    split at h
    · simp at h
    · next hok =>
      simp only [Bool.or_eq_true, not_or, Bool.not_eq_true', Bool.not_eq_false'] at hok
      obtain ⟨⟨hat, hdw⟩, hwo⟩ := hok
      simp only [Option.some.injEq] at h; subst h
      subst hw
      have hVx : V.gam ρ x := by
        rcases hVw with h | h
        · exact h
        · exact absurd rfl h
      refine ⟨ram, [⟨A, x⟩], ?_, .dev (writeOk_sound (by simpa using hwo) hVx hAa), hm⟩
      rw [hAw] at hin hd
      exact interp_store_dev o (by rw [hAa]; exact hal) hin (by simpa using hat) hd (by simpa using hdw) rfl
  · simp at h

/-- Cells a weak store keeps sit where cells of its input sat. -/
def SameShape (out inp : List Cell) : Prop :=
  ∀ c ∈ out, ∃ d ∈ inp, c.base = d.base ∧ c.addr = d.addr ∧ c.w = d.w ∧ c.guard = d.guard

theorem storeWeak_shape (mem : List Cell) (base : Base) (a : Nat) (wd : Width) (V : AV) :
    SameShape (storeWeak mem base a wd V) mem := by
  intro c hc
  simp only [storeWeak, List.mem_filterMap] at hc
  obtain ⟨d, hd, he⟩ := hc
  split at he
  · simp only [Option.some.injEq] at he; subst he; exact ⟨d, hd, rfl, rfl, rfl, rfl⟩
  · split at he
    · simp at he
    · simp only [Option.some.injEq] at he; subst he; exact ⟨_, hd, rfl, rfl, rfl, rfl⟩

theorem sameShape_trans {a b c : List Cell} (h1 : SameShape a b) (h2 : SameShape b c) : SameShape a c := by
  intro x hx
  obtain ⟨y, hy, e1, e2, e3, e4⟩ := h1 x hx
  obtain ⟨z, hz, f1, f2, f3, f4⟩ := h2 y hy
  exact ⟨z, hz, e1.trans f1, e2.trans f2, e3.trans f3, e4.trans f4⟩

theorem sameShape_refl (a : List Cell) : SameShape a a := fun c hc => ⟨c, hc, rfl, rfl, rfl, rfl⟩

theorem cell_wf_of_shape {cfg : Config} {c d : Cell} (h : c.base = d.base ∧ c.addr = d.addr ∧ c.w = d.w ∧ c.guard = d.guard)
    (hd : d.wf cfg = true) : c.wf cfg = true := by
  obtain ⟨e1, e2, e3, e4⟩ := h
  unfold Cell.wf at *; rw [e1, e2, e3, e4]; exact hd

theorem cell_at_of_shape {ρ : Nat → Word} {c d : Cell} (h : c.base = d.base ∧ c.addr = d.addr ∧ c.w = d.w ∧ c.guard = d.guard) :
    c.at ρ = d.at ρ := by
  obtain ⟨e1, e2, _, _⟩ := h
  unfold Cell.at; rw [e1, e2]

/-- A weak store step at an address that was not written only weakens. -/
theorem storeAt_weak_weakens {cfg : Config} {s : AState} {mem mem' : List Cell} {a : Nat} {wd : Width}
    {V : AV} {atomic : Bool} (h : storeAt cfg s mem a wd V atomic false = some mem')
    {ρ : Nat → Word} {R : Word → BitVec 8} (hm : MemHolds ρ R mem) : MemHolds ρ R mem' ∧ SameShape mem' mem := by
  unfold storeAt at h
  split at h
  · split at h
    · simp at h
    · simp only [Option.some.injEq, Bool.false_eq_true, if_false] at h; subst h
      exact ⟨storeWeak_weakens hm, storeWeak_shape _ _ _ _ _⟩
  · split at h
    · simp at h
    · simp only [Option.some.injEq] at h; subst h; exact ⟨hm, sameShape_refl _⟩
  · simp at h

theorem storeAt_weak_shape {cfg : Config} {s : AState} {mem mem' : List Cell} {a : Nat} {wd : Width}
    {V : AV} {atomic : Bool} (h : storeAt cfg s mem a wd V atomic false = some mem') : SameShape mem' mem := by
  unfold storeAt at h
  split at h
  · split at h
    · simp at h
    · simp only [Option.some.injEq, Bool.false_eq_true, if_false] at h; subst h; exact storeWeak_shape _ _ _ _ _
  · split at h
    · simp at h
    · simp only [Option.some.injEq] at h; subst h; exact sameShape_refl _
  · simp at h

/-- A store to one of several candidates: the platform does not fault, and
    whatever the write did to the original memory `ram0`, the abstract memory
    after the fold holds afterwards. -/
theorem absStore_fold_sound {cfg : Config} {s : AState} {wd : Width} {V : AV} {atomic : Bool}
    {ρ : Nat → Word} {A x : Word} (hram : cfg.board.ramBase + cfg.board.ramSize ≤ M32)
    (hV : V.gam ρ (stored wd x)) (hVw : V.gam ρ x ∨ wd ≠ .w) (ram0 : Word → BitVec 8) (o : Oracle)
    (i : Nat) (evs : List Event) (k : Eff) :
    ∀ (as : List Nat) (mem memF : List Cell),
      as.foldlM (init := mem) (fun mem a => storeAt cfg s mem a wd V atomic false) = some memF →
      (∀ c ∈ mem, c.wf cfg = true) →
      (∀ c ∈ mem, c.base = .rel → s.hnd = true) →
      (∀ c ∈ mem, c.base = .rel → cfg.isStatic A.toNat wd.bytes = true → Disj (c.at ρ) c.w A wd) →
      -- Either the written address is still to come, and `mem` holds now ...
      (A.toNat ∈ as ∧ MemHolds ρ ram0 mem ∨
      -- ... or it was already processed, with this effect, and `mem` holds after it.
       ∃ ram' evs', StoreEffect cfg ram0 A x wd ram' evs' ∧
         interp cfg.board cfg.img o (.store wd A x atomic k) ram0 i evs =
           interp cfg.board cfg.img o k ram' i (evs ++ evs') ∧ MemHolds ρ ram' mem) →
      ∃ ram' evs', StoreEffect cfg ram0 A x wd ram' evs' ∧
        interp cfg.board cfg.img o (.store wd A x atomic k) ram0 i evs =
          interp cfg.board cfg.img o k ram' i (evs ++ evs') ∧ MemHolds ρ ram' memF
  | [], mem, memF, h, _, _, _, hst => by
    simp only [List.foldlM, pure, Option.some.injEq] at h; subst h
    rcases hst with ⟨hA, _⟩ | hdone
    · simp at hA
    · exact hdone
  | a :: as, mem, memF, h, hwf, hrelH, hrel, hst => by
    simp only [List.foldlM, bind, Option.bind] at h
    cases hs : storeAt cfg s mem a wd V atomic false with
    | none => rw [hs] at h; simp at h
    | some mem1 =>
      rw [hs] at h
      have hshape := storeAt_weak_shape hs
      have hwf1 : ∀ c ∈ mem1, c.wf cfg = true := fun c hc => by
        obtain ⟨d, hd, e⟩ := hshape c hc; exact cell_wf_of_shape e (hwf d hd)
      have hrelH1 : ∀ c ∈ mem1, c.base = .rel → s.hnd = true := fun c hc hb => by
        obtain ⟨d, hd, e⟩ := hshape c hc; exact hrelH d hd (e.1 ▸ hb)
      have hrel1 : ∀ c ∈ mem1, c.base = .rel → cfg.isStatic A.toNat wd.bytes = true →
          Disj (c.at ρ) c.w A wd := fun c hc hb hst => by
        obtain ⟨d, hd, e⟩ := hshape c hc
        rw [cell_at_of_shape e, e.2.2.1]; exact hrel d hd (e.1 ▸ hb) hst
      have ih := @absStore_fold_sound cfg s wd V atomic ρ A x hram hV hVw ram0 o i evs k as mem1 memF h hwf1
        hrelH1 hrel1
      rcases hst with ⟨hA, hm⟩ | ⟨ram', evs', he, hi, hm⟩
      · by_cases ha : A.toNat = a
        · -- This candidate is the address written.
          have hsep : cfg.board.inRam (w a) wd.bytes = true → (s.hnd = true → cfg.isStatic a wd.bytes = true) →
              StoreSep ρ mem .abs a wd V := fun hin hst =>
            storeSep_abs hram hwf (by rw [← ha]; exact toNat_lt A) hin
              (fun c hc hb => by
                rw [show w a = A by rw [← ha]; exact w_toNat A]
                exact hrel c hc hb (by rw [ha]; exact hst (hrelH c hc hb)))
          obtain ⟨ram', evs', hi, he, hm'⟩ := storeAt_written hs ha hV hVw hm hsep o i evs k
          exact ih (.inr ⟨ram', evs', he, hi, hm'⟩)
        · simp only [List.mem_cons] at hA
          rcases hA with hA | hA
          · exact absurd hA ha
          · exact ih (.inl ⟨hA, (storeAt_weak_weakens hs hm).1⟩)
      · exact ih (.inr ⟨ram', evs', he, hi, (storeAt_weak_weakens hs hm).1⟩)

theorem stored_sound {ρ : Nat → Word} (wd : Width) {V : AV} {x : Word} (h : V.gam ρ x) :
    (V.stored wd).gam ρ (stored wd x) := by
  cases wd
  · exact band_sound h (const_sound ρ 0xff)
  · exact band_sound h (const_sound ρ 0xffff)
  · exact h

theorem stored_w {ρ : Nat → Word} {V : AV} {x : Word} (h : V.gam ρ x) : (V.stored .w).gam ρ x := h

/-- A store to absolute candidate addresses (one or several). -/
theorem absStore_vals_sound {cfg : Config} {s : AState} {as : List Nat} {wd : Width} {V : AV}
    {atomic : Bool} {memF : List Cell} (h : absStore cfg s (.vals as) wd V atomic = some memF)
    (hram : cfg.board.ramBase + cfg.board.ramSize ≤ M32)
    {ρ : Nat → Word} {ram : Word → BitVec 8} {A x : Word} (hA : A.toNat ∈ as) (hV : V.gam ρ x)
    (hm : MemHolds ρ ram s.mem) (hwf : ∀ c ∈ s.mem, c.wf cfg = true)
    (hrelH : ∀ c ∈ s.mem, c.base = .rel → s.hnd = true)
    (hrel : ∀ c ∈ s.mem, c.base = .rel → cfg.isStatic A.toNat wd.bytes = true → Disj (c.at ρ) c.w A wd)
    (o : Oracle) (i : Nat) (evs : List Event) (k : Eff) :
    ∃ ram' evs', StoreEffect cfg ram A x wd ram' evs' ∧
      interp cfg.board cfg.img o (.store wd A x atomic k) ram i evs =
        interp cfg.board cfg.img o k ram' i (evs ++ evs') ∧ MemHolds ρ ram' memF := by
  have hS := stored_sound wd hV
  have hSw : (V.stored wd).gam ρ x ∨ wd ≠ .w := by cases wd <;> simp [stored_w hV]
  rcases as with _ | ⟨a, _ | ⟨b, rest⟩⟩
  · simp at hA
  · -- one candidate: a strong update
    simp only [absStore] at h
    simp only [List.mem_singleton] at hA
    have hsep : cfg.board.inRam (w a) wd.bytes = true → (s.hnd = true → cfg.isStatic a wd.bytes = true) →
        StoreSep ρ s.mem .abs a wd (V.stored wd) :=
      fun hin hst => storeSep_abs hram hwf (by rw [← hA]; exact toNat_lt A) hin
        (fun c hc hb => by
          rw [show w a = A by rw [← hA]; exact w_toNat A]
          exact hrel c hc hb (by rw [hA]; exact hst (hrelH c hc hb)))
    obtain ⟨ram', evs', hi, he, hm'⟩ := storeAt_written h hA hS hSw hm hsep o i evs k
    exact ⟨ram', evs', he, hi, hm'⟩
  · -- several: weak updates folded over the candidates
    simp only [absStore] at h
    exact absStore_fold_sound (s := s) (atomic := atomic) hram hS hSw ram o i evs k _ s.mem memF h hwf hrelH
      hrel (.inl ⟨hA, hm⟩)

/-! ## The handler's own frame -/

/-- What the checker establishes about an interrupted stack pointer (it is
    one of `sigma`) and the stack layout. -/
structure SpOk (cfg : Config) (σ : Nat) : Prop where
  lo : cfg.stackLow + cfg.hdepth ≤ σ
  hi : σ ≤ cfg.pinLow
  al : σ % 4 = 0
  dep : cfg.hdepth < 2 ^ 31
  base : cfg.board.ramBase ≤ cfg.stackLow
  pin : cfg.pinLow ≤ cfg.ramEnd
  ram : cfg.ramEnd ≤ M32

/-- A handler-frame offset in budget names an address below sp, inside the
    stack region. -/
theorem rel_addr {cfg : Config} {ρ : Nat → Word} {off n : Nat} (hs : SpOk cfg (ρ 2).toNat)
    (ho : M32 - cfg.hdepth ≤ off) (hn : off + n ≤ M32) :
    (ρ 2 + w off).toNat = (ρ 2).toNat + off - M32 ∧
    cfg.stackLow ≤ (ρ 2 + w off).toNat ∧ (ρ 2 + w off).toNat + n ≤ cfg.pinLow := by
  have hl := hs.lo; have hh := hs.hi; have hd := hs.dep; have hp := hs.pin; have hr := hs.ram
  have hσ := toNat_lt (ρ 2)
  unfold Config.ramEnd at hp hr
  have e : (ρ 2 + w off).toNat = (ρ 2).toNat + off - M32 := by
    rw [toNat_add_w]; simp only [M32] at *; omega
  refine ⟨e, ?_, ?_⟩ <;> rw [e] <;> simp only [M32] at * <;> omega

theorem rel_inRam {cfg : Config} {ρ : Nat → Word} {off : Nat} {wd : Width} (hs : SpOk cfg (ρ 2).toNat)
    (ho : M32 - cfg.hdepth ≤ off) (hn : off + wd.bytes ≤ M32) :
    cfg.board.inRam (ρ 2 + w off) wd.bytes = true := by
  obtain ⟨_, h1, h2⟩ := rel_addr (n := wd.bytes) hs ho hn
  have := hs.base; have := hs.pin
  simp only [Board.inRam, Bool.and_eq_true, decide_eq_true_eq]
  unfold Config.ramEnd at *; omega

theorem rel_aligned {cfg : Config} {ρ : Nat → Word} {off : Nat} {wd : Width} (hs : SpOk cfg (ρ 2).toNat)
    (ho : M32 - cfg.hdepth ≤ off) (hn : off + wd.bytes ≤ M32) (ha : off % wd.bytes = 0) :
    (ρ 2 + w off).toNat % wd.bytes = 0 := by
  obtain ⟨e, _, _⟩ := rel_addr (n := wd.bytes) hs ho hn
  rw [e]; have := hs.al; have := hs.lo
  cases wd <;> simp only [Width.bytes, M32] at * <;> omega

/-- A handler-frame load: RAM, aligned, and the abstract cell lookup is sound. -/
theorem absLoad_rel_sound {cfg : Config} {s : AState} {off : Nat} {wd : Width} {atomic : Bool}
    {v : AV} (h : absLoad cfg s (.sym 2 off) wd atomic = some v)
    {ρ : Nat → Word} {ram : Word → BitVec 8} (hs : SpOk cfg (ρ 2).toNat) (hm : MemHolds ρ ram s.mem)
    (o : Oracle) (i : Nat) (evs : List Event) (k : Word → Eff) :
    interp cfg.board cfg.img o (.load wd (ρ 2 + BitVec.ofNat 32 off) atomic k) ram i evs =
      interp cfg.board cfg.img o (k (ramRead ram (ρ 2 + w off) wd)) ram i evs ∧
    v.gam ρ (ramRead ram (ρ 2 + w off) wd) ∧ Fits wd (ramRead ram (ρ 2 + w off) wd) := by
  simp only [absLoad] at h
  split at h
  · next hc =>
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hc
    obtain ⟨⟨⟨_, ha⟩, ho⟩, hn⟩ := hc
    simp only [Option.some.injEq] at h; subst h
    refine ⟨interp_load_ram o (rel_aligned hs ho hn ha) (rel_inRam hs ho hn), ?_, ramRead_fits _ _ _⟩
    have := loadCell_sound (ρ := ρ) (base := .rel) (a := off) (wd := wd) hm
    simpa [addrOf] using this
  · simp at h

theorem static_disj_stack {cfg : Config} {a n : Nat} {A : Word} {m : Nat} (hs : cfg.isStatic a n = true)
    (hA1 : cfg.stackLow ≤ A.toNat) (hA2 : A.toNat + m ≤ cfg.pinLow) (hram : cfg.ramEnd ≤ M32) :
    (a + n ≤ A.toNat ∨ A.toNat + m ≤ a) := by
  simp only [Config.isStatic, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hs
  omega

/-- A handler-frame store: RAM, aligned, and the abstract memory after the
    strong update holds. Needs the handler state's well-formedness. -/
theorem absStore_rel_sound {cfg : Config} {s : AState} {off : Nat} {wd : Width} {V : AV} {atomic : Bool}
    {memF : List Cell} (h : absStore cfg s (.sym 2 off) wd V atomic = some memF)
    {ρ : Nat → Word} {ram : Word → BitVec 8} {x : Word} (hs : SpOk cfg (ρ 2).toNat) (hV : V.gam ρ x)
    (hm : MemHolds ρ ram s.mem) (hwf : s.wf cfg = true) (hnd : s.hnd = true)
    (o : Oracle) (i : Nat) (evs : List Event) (k : Eff) :
    interp cfg.board cfg.img o (.store wd (ρ 2 + BitVec.ofNat 32 off) x atomic k) ram i evs =
      interp cfg.board cfg.img o k (ramWrite ram (ρ 2 + w off) x wd) i evs ∧
    MemHolds ρ (ramWrite ram (ρ 2 + w off) x wd) memF := by
  simp only [absStore] at h
  split at h
  · next hc =>
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hc
    obtain ⟨⟨⟨_, ha⟩, ho⟩, hn⟩ := hc
    simp only [Option.some.injEq] at h; subst h
    refine ⟨interp_store_ram o (rel_aligned hs ho hn ha) (rel_inRam hs ho hn), ?_⟩
    obtain ⟨eA, hA1, hA2⟩ := rel_addr (n := wd.bytes) hs ho hn
    have hram := hs.ram
    have hM : M32 = 4294967296 := rfl
    have hpin := hs.pin
    have hsl := hs.lo
    simp only [AState.wf, Bool.and_eq_true, List.all_eq_true, hnd, Bool.not_true, Bool.false_or,
      Bool.true_or, beq_iff_eq] at hwf
    obtain ⟨⟨⟨_, hcells⟩, _⟩, hhnd⟩ := hwf
    have key : StoreSep ρ s.mem .rel off wd (V.stored wd) := by
      intro c hc hns
      have hcw := hcells c hc
      have hch := hhnd c hc
      simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at hch
      obtain ⟨hbase, hgs⟩ := hch
      simp only [Cell.staleAfter, Bool.or_eq_false_iff] at hns
      obtain ⟨hhit, _⟩ := hns
      constructor
      · cases hb : c.base with
        | abs =>
          have hst : cfg.isStatic c.addr c.w.bytes = true := by
            rcases hbase with e | e
            · rw [hb] at e; cases e
            · exact e
          simp only [Cell.wf, hb, Bool.and_eq_true, decide_eq_true_eq] at hcw
          have hC := inRam_nat hcw.1.1 hcw.1.2
          have hat : c.at ρ = w c.addr := by simp [Cell.at, hb]
          rw [hat, show addrOf ρ .rel off = ρ 2 + w off from rfl]
          apply disj_of_nat (by rw [toNat_w_of_lt hcw.1.1]; unfold Config.ramEnd at hram; omega)
            (by unfold Config.ramEnd at hram; omega)
          rw [toNat_w_of_lt hcw.1.1]
          exact static_disj_stack hst hA1 hA2 hram
        | rel =>
          simp only [Cell.wf, hb, Bool.and_eq_true, decide_eq_true_eq] at hcw
          obtain ⟨⟨hco, hcn⟩, _⟩ := hcw
          obtain ⟨eC, hC1, hC2⟩ := rel_addr (n := c.w.bytes) hs hco hcn
          have hat : c.at ρ = ρ 2 + w c.addr := by simp [Cell.at, hb]
          simp only [Cell.hits, hb, beq_self_eq_true, Bool.true_and, overlap, Bool.and_eq_false_iff,
            decide_eq_false_iff_not] at hhit
          rw [hat, show addrOf ρ .rel off = ρ 2 + w off from rfl]
          apply disj_of_nat (by unfold Config.ramEnd at hram; omega) (by unfold Config.ramEnd at hram; omega)
          rw [eC, eA]; omega
      · intro g hg
        left
        rw [hg] at hgs
        have hgw := hcw
        simp only [Cell.wf, hg, Bool.and_eq_true, decide_eq_true_eq] at hgw
        have hG := inRam_nat hgw.2.1 hgw.2.2
        rw [show addrOf ρ .rel off = ρ 2 + w off from rfl]
        apply disj_of_nat (by rw [toNat_w_of_lt hgw.2.1]; unfold Config.ramEnd at hram; omega)
          (by unfold Config.ramEnd at hram; omega)
        rw [toNat_w_of_lt hgw.2.1]
        exact static_disj_stack (by simpa using hgs) hA1 hA2 hram
    have := storeStrong_sound hm (stored_sound wd hV) key
    simpa [addrOf] using this
  · simp at h

/-! ## Abstract machine states -/

/-- A concrete machine described by an abstract state. The reservation is
    not tracked: the abstract SC allows both outcomes. -/
structure StateHolds (ρ : Nat → Word) (s : AState) (m : Machine) : Prop where
  pc : m.core.pc = w s.pc
  regs : ∀ r : Reg, (s.get r).gam ρ (m.core.get r)
  mem : MemHolds ρ m.ram s.mem
  mie : s.mie.mayBe m.core.mie_ = true
  mpie : s.mpie.mayBe m.core.mpie = true
  mpp : m.core.mpp.toNat ∈ s.mpp
  mieReg : s.mieReg.gam ρ m.core.mieReg
  mtvec : s.mtvec.gam ρ m.core.mtvec
  mepc : s.mepc.gam ρ m.core.mepc
  mcause : s.mcause.gam ρ m.core.mcause
  mscratch : s.mscratch.gam ρ m.core.mscratch

theorem AState.get_zero (s : AState) : s.get 0 = .const 0 := rfl

theorem AState.get_set_self (s : AState) (r : Reg) (v : AV) (h : r.val ≠ 0) (hl : s.regs.length = 31) :
    (s.set r v).get r = v := by
  have := r.isLt
  simp only [AState.set, AState.get, h, if_false]
  rw [List.getD_eq_getElem?_getD, List.getElem?_set_self (by omega)]; rfl

theorem AState.get_set_ne (s : AState) (r q : Reg) (v : AV) (h : q ≠ r) :
    (s.set r v).get q = s.get q := by
  unfold AState.set AState.get
  by_cases hr : r.val = 0
  · simp [hr]
  · simp only [hr, if_false]
    by_cases hq : q.val = 0
    · simp [hq]
    · simp only [hq, if_false]
      rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_set_ne]
      intro e; apply h; apply Fin.ext; omega

theorem AState.set_regs_length (s : AState) (r : Reg) (v : AV) :
    (s.set r v).regs.length = s.regs.length := by
  unfold AState.set; split <;> simp

theorem const0_gam (ρ : Nat → Word) : (AV.const 0).gam ρ 0 := by simp [AV.const, AV.gam, M32]

/-- Writing a register on both sides keeps the description. -/
theorem regs_set {ρ : Nat → Word} {s : AState} {c : Core} (hl : s.regs.length = 31)
    (hr : ∀ q : Reg, (s.get q).gam ρ (c.get q)) (r : Reg) {v : AV} {x : Word} (hv : v.gam ρ x) :
    ∀ q : Reg, ((s.set r v).get q).gam ρ ((c.set r x).get q) := by
  intro q
  by_cases hq : q.val = 0
  · have : q = 0 := Fin.ext hq
    subst this; rw [AState.get_zero, Core.get_zero]; exact const0_gam ρ
  · by_cases e : q = r
    · subst e; rw [AState.get_set_self _ _ _ hq hl, Core.get_set_self _ _ _ hq]; exact hv
    · rw [AState.get_set_ne _ _ _ _ e, Core.get_set_ne _ _ _ _ e]; exact hr q

/-! ## The order on states -/

theorem Tri.leq_mayBe {a b : Tri} {x : Bool} (h : a.leq b = true) (hx : a.mayBe x = true) : b.mayBe x = true := by
  cases a <;> cases b <;> cases x <;> simp_all [Tri.leq, Tri.mayBe]

theorem leqIn_sound {ρ : Nat → Word} {ram : Word → BitVec 8} {mem : List Cell} {c : Cell}
    (hm : MemHolds ρ ram mem) (h : Cell.leqIn mem c = true) : c.holds ρ ram := by
  unfold Cell.leqIn at h
  split at h
  · cases hp : plain mem c.base c.addr c.w with
    | none => rw [hp] at h; simp at h
    | some v =>
      rw [hp] at h
      intro _
      rw [cell_at rfl rfl]
      exact leq_sound h (plain_sound hm hp)
  · next g hg =>
    rw [Bool.or_eq_true] at h
    rcases h with h | h
    · obtain ⟨d, hd, hp⟩ := List.any_eq_true.mp h
      simp only [Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true, Option.isNone_iff_eq_none] at hp
      obtain ⟨⟨⟨⟨hb, ha⟩, hw⟩, hgd⟩, hl⟩ := hp
      intro hguard
      have hat : c.at ρ = d.at ρ := by unfold Cell.at; rw [hb, ha]
      rw [hat, ← hw]
      apply leq_sound hl
      apply hm d hd
      intro g' hg'
      rcases hgd with hn | he
      · rw [hn] at hg'; cases hg'
      · rw [he] at hg'; cases hg'
        exact hguard g hg
    · cases hp : plain mem .abs g.1 g.2.1 with
      | none => rw [hp] at h; simp at h
      | some x =>
        rw [hp] at h
        intro hguard
        exfalso
        have hx := leq_sound h (plain_sound hm hp)
        simp only [addrOf, AV.gam, List.mem_singleton] at hx
        exact hguard g hg hx

theorem zip_all_get {l1 l2 : List AV} (hz : (List.zip l1 l2).all (fun p => p.1.leq p.2) = true)
    (hl : l1.length = l2.length) (i : Nat) (hi : i < l1.length) :
    (l1.getD i .top).leq (l2.getD i .top) = true := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi,
    List.getElem?_eq_getElem (hl ▸ hi)]
  simp only [Option.getD_some]
  rw [List.all_eq_true] at hz
  exact hz (l1[i], l2[i]) (List.mem_iff_getElem.mpr ⟨i, by simp [List.length_zip, hl] at hi ⊢; omega,
    by simp [List.getElem_zip]⟩)

theorem get_leq {a b : AState} (hz : (List.zip a.regs b.regs).all (fun p => p.1.leq p.2) = true)
    (ha : a.regs.length = 31) (hb : b.regs.length = 31) (r : Reg) : (a.get r).leq (b.get r) = true := by
  unfold AState.get
  split
  · simp [AV.leq, AV.const]
  · next h0 => have := r.isLt; exact zip_all_get hz (by rw [ha, hb]) _ (by omega)

/-- `leq` is sound: a state's machines are all machines of a larger state. -/
theorem leq_state_sound {ρ : Nat → Word} {a b : AState} {m : Machine} (h : a.leq b = true)
    (hs : StateHolds ρ a m) : StateHolds ρ b m := by
  simp only [AState.leq, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq,
    and_assoc] at h
  obtain ⟨hpc, _, ha, hb, hz, hmem, hmie, hmpie, hmpp, hmr, htv, hepc, hca, hsc⟩ := h
  refine ⟨hpc ▸ hs.pc, fun r => leq_sound (get_leq (List.all_eq_true.mpr hz) ha hb r) (hs.regs r),
    fun c hc => leqIn_sound hs.mem (hmem c hc), Tri.leq_mayBe hmie hs.mie, Tri.leq_mayBe hmpie hs.mpie,
    hmpp _ hs.mpp, leq_sound hmr hs.mieReg, leq_sound htv hs.mtvec, leq_sound hepc hs.mepc,
    leq_sound hca hs.mcause, leq_sound hsc hs.mscratch⟩

/-! ## One instruction -/

/-- The CSR part of `StateHolds` carries over to a core with the same CSRs. -/
theorem sameCsr_fields {c d : Core} (h : c.sameCsr d) :
    c.mie_ = d.mie_ ∧ c.mpie = d.mpie ∧ c.mpp = d.mpp ∧ c.mieReg = d.mieReg ∧ c.mtvec = d.mtvec ∧
    c.mepc = d.mepc ∧ c.mcause = d.mcause ∧ c.mscratch = d.mscratch := by
  unfold Core.sameCsr Core.ctl at h
  simp only [Prod.mk.injEq] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, _⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩

/-- Build the description of a successor that changed only registers and
    the pc (and possibly RAM), from the old description. -/
theorem holds_succ {ρ : Nat → Word} {s t : AState} {m : Machine} {c : Core} {ram : Word → BitVec 8}
    (hs : StateHolds ρ s m) (hc : c.sameCsr m.core) (hpc : c.pc = w t.pc)
    (hregs : ∀ r : Reg, (t.get r).gam ρ (c.get r)) (hmem : MemHolds ρ ram t.mem)
    (hcsr : t.mie = s.mie ∧ t.mpie = s.mpie ∧ t.mpp = s.mpp ∧ t.mieReg = s.mieReg ∧ t.mtvec = s.mtvec ∧
      t.mepc = s.mepc ∧ t.mcause = s.mcause ∧ t.mscratch = s.mscratch) :
    StateHolds ρ t ⟨c, ram⟩ := by
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8⟩ := sameCsr_fields hc
  obtain ⟨f1, f2, f3, f4, f5, f6, f7, f8⟩ := hcsr
  exact ⟨hpc, hregs, hmem, by rw [f1, e1]; exact hs.mie, by rw [f2, e2]; exact hs.mpie,
    by rw [f3, e3]; exact hs.mpp, by rw [f4, e4]; exact hs.mieReg, by rw [f5, e5]; exact hs.mtvec,
    by rw [f6, e6]; exact hs.mepc, by rw [f7, e7]; exact hs.mcause, by rw [f8, e8]; exact hs.mscratch⟩

theorem next_pc {pc len : Nat} (hl : len < M32) : w ((pc + len) % M32) = w pc + w len := by
  apply BitVec.eq_of_toNat_eq
  simp only [w, BitVec.toNat_ofNat, BitVec.toNat_add, M32]
  omega

/-- A length the decoder produces: 2 or 4. -/
def LenOk (len : Word) : Prop := len = 2 ∨ len = 4

theorem lenOk_lt {len : Word} (h : LenOk len) : len.toNat < M32 := toNat_lt len

theorem w_len {len : Word} : w len.toNat = len := w_toNat len

/-- The pc after a non-jump: what `absExec`'s `adv` puts in the successor. -/
theorem pc_adv {s : AState} {m : Machine} {len : Word} (hpc : m.core.pc = w s.pc) :
    m.core.pc + len = w ((s.pc + len.toNat) % M32) := by
  rw [next_pc (toNat_lt len), hpc, w_len]

/-- What one instruction step must establish: it does not fault, its
    events are allowed, and the machine after it is described by one of the
    abstract successors. -/
def StepOk (cfg : Config) (ρ : Nat → Word) (ts : List AState) (o : Oracle) (e : Eff)
    (ram : Word → BitVec 8) : Prop :=
  ∃ c ram' evs, interp cfg.board cfg.img o e ram 0 [] = .ok c ram' evs ∧ (∀ ev ∈ evs, EvOk cfg ev) ∧
    ∃ t ∈ ts, StateHolds ρ t ⟨c, ram'⟩

theorem AState.set_other (s : AState) (r : Reg) (v : AV) :
    (s.set r v).mem = s.mem ∧ (s.set r v).mie = s.mie ∧ (s.set r v).mpie = s.mpie ∧
    (s.set r v).mpp = s.mpp ∧ (s.set r v).mieReg = s.mieReg ∧ (s.set r v).mtvec = s.mtvec ∧
    (s.set r v).mepc = s.mepc ∧ (s.set r v).mcause = s.mcause ∧ (s.set r v).mscratch = s.mscratch ∧
    (s.set r v).pc = s.pc ∧ (s.set r v).hnd = s.hnd := by
  unfold AState.set; split <;> simp

theorem withPc_get (s : AState) (p : Nat) (r : Reg) : ({ s with pc := p } : AState).get r = s.get r := rfl

/-- An instruction that writes `x` (described by `v`) to `rd` and falls
    through. -/
theorem regwrite_sound {cfg : Config} {ρ : Nat → Word} {s : AState} {m : Machine} {len : Word} {rd : Reg}
    {v : AV} {x : Word} (hs : StateHolds ρ s m) (hl : s.regs.length = 31) (hv : v.gam ρ x) (o : Oracle) :
    StepOk cfg ρ [{ s.set rd v with pc := (s.pc + len.toNat) % M32 }] o
      (.done (m.core.wr rd x (m.core.pc + len))) m.ram := by
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, _, _⟩ := AState.set_other s rd v
  refine ⟨_, _, _, interp_done o _ _ _ _, by simp, _, List.mem_singleton_self _, ?_⟩
  refine holds_succ hs (Core.sameCsr_wr _ _ _ _) (by simp only [Core.wr_pc]; exact pc_adv hs.pc) ?_
    (by simp only; rw [e1]; exact hs.mem) ⟨e2, e3, e4, e5, e6, e7, e8, e9⟩
  intro q
  rw [withPc_get]
  simp only [Core.wr]
  exact regs_set hl hs.regs rd hv q

/-- An instruction that only falls through. -/
theorem nop_sound {cfg : Config} {ρ : Nat → Word} {s : AState} {m : Machine} {len : Word}
    (hs : StateHolds ρ s m) (o : Oracle) :
    StepOk cfg ρ [{ s with pc := (s.pc + len.toNat) % M32 }] o
      (.done { m.core with pc := m.core.pc + len }) m.ram := by
  refine ⟨_, _, _, interp_done o _ _ _ _, by simp, _, List.mem_singleton_self _, ?_⟩
  exact holds_succ hs (Core.sameCsr_goto _ _) (pc_adv hs.pc) (fun r => hs.regs r) hs.mem
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ### Jumps and branches -/

/-- The CSR part of a description. -/
structure CtlHolds (ρ : Nat → Word) (s : AState) (c : Core) : Prop where
  mie : s.mie.mayBe c.mie_ = true
  mpie : s.mpie.mayBe c.mpie = true
  mpp : c.mpp.toNat ∈ s.mpp
  mieReg : s.mieReg.gam ρ c.mieReg
  mtvec : s.mtvec.gam ρ c.mtvec
  mepc : s.mepc.gam ρ c.mepc
  mcause : s.mcause.gam ρ c.mcause
  mscratch : s.mscratch.gam ρ c.mscratch

theorem ctl_of_holds {ρ : Nat → Word} {s : AState} {m : Machine} (hs : StateHolds ρ s m) :
    CtlHolds ρ s m.core :=
  ⟨hs.mie, hs.mpie, hs.mpp, hs.mieReg, hs.mtvec, hs.mepc, hs.mcause, hs.mscratch⟩

theorem ctl_same {ρ : Nat → Word} {s : AState} {c d : Core} (h : CtlHolds ρ s d) (hc : c.sameCsr d) :
    CtlHolds ρ s c := by
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8⟩ := sameCsr_fields hc
  exact ⟨e1 ▸ h.mie, e2 ▸ h.mpie, e3 ▸ h.mpp, e4 ▸ h.mieReg, e5 ▸ h.mtvec, e6 ▸ h.mepc, e7 ▸ h.mcause,
    e8 ▸ h.mscratch⟩

theorem ctl_set {ρ : Nat → Word} {s : AState} {c : Core} (h : CtlHolds ρ s c) (r : Reg) (v : AV) :
    CtlHolds ρ (s.set r v) c := by
  obtain ⟨_, e2, e3, e4, e5, e6, e7, e8, e9, _, _⟩ := AState.set_other s r v
  exact ⟨e2 ▸ h.mie, e3 ▸ h.mpie, e4 ▸ h.mpp, e5 ▸ h.mieReg, e6 ▸ h.mtvec, e7 ▸ h.mepc, e8 ▸ h.mcause,
    e9 ▸ h.mscratch⟩

theorem ctl_withPc {ρ : Nat → Word} {s : AState} {c : Core} (h : CtlHolds ρ s c) (p : Nat) :
    CtlHolds ρ { s with pc := p } c :=
  ⟨h.mie, h.mpie, h.mpp, h.mieReg, h.mtvec, h.mepc, h.mcause, h.mscratch⟩

theorem holds_mk {ρ : Nat → Word} {t : AState} {c : Core} {ram : Word → BitVec 8} (hpc : c.pc = w t.pc)
    (hregs : ∀ r : Reg, (t.get r).gam ρ (c.get r)) (hmem : MemHolds ρ ram t.mem) (hctl : CtlHolds ρ t c) :
    StateHolds ρ t ⟨c, ram⟩ :=
  ⟨hpc, hregs, hmem, hctl.mie, hctl.mpie, hctl.mpp, hctl.mieReg, hctl.mtvec, hctl.mepc, hctl.mcause,
    hctl.mscratch⟩

theorem lsb_even {T : Word} (h : T.toNat % 2 = 0) : T.getLsbD 0 = false := by
  rw [← BitVec.testBit_toNat, Nat.testBit_zero]; simp [h]

/-- An abstract jump to a set of even targets is a real jump that does not
    fault, to a successor the abstract state describes. -/
theorem jumpAbs_sound {cfg : Config} {ρ : Nat → Word} {s : AState} {l : List Nat} {ts : List AState}
    (h : jumpAbs s (.vals l) = some ts) {c : Core} {ram : Word → BitVec 8} {T : Word}
    (hT : T.toNat ∈ l) (hctl : CtlHolds ρ s c) (hregs : ∀ r : Reg, (s.get r).gam ρ (c.get r))
    (hmem : MemHolds ρ ram s.mem) (o : Oracle) :
    StepOk cfg ρ ts o (jump c T) ram := by
  simp only [jumpAbs] at h
  split at h
  · next hall =>
    simp only [Option.some.injEq] at h; subst h
    have heven : T.toNat % 2 = 0 := by
      simp only [List.all_eq_true, decide_eq_true_eq] at hall; exact hall _ hT
    refine ⟨_, _, _, by rw [jump_ok _ _ (lsb_even heven)]; exact interp_done o _ _ _ _, by simp, _,
      List.mem_map.mpr ⟨_, hT, rfl⟩, ?_⟩
    exact holds_mk (by simp [Core.goto, w_toNat]) (fun r => hregs r) hmem
      (ctl_same (ctl_withPc hctl _) (Core.sameCsr_goto _ _))
  · simp at h

theorem isConst_eq {a : AV} {k : Nat} (h : a.isConst = some k) : a = .vals [k] := by
  unfold AV.isConst at h
  split at h
  · simp only [Option.some.injEq] at h; subst h; rfl
  · simp at h

theorem stepOk_mono {cfg : Config} {ρ : Nat → Word} {ts ts' : List AState} {o : Oracle} {e : Eff} {ram : Word → BitVec 8}
    (h : StepOk cfg ρ ts o e ram) (hsub : ∀ t ∈ ts, t ∈ ts') : StepOk cfg ρ ts' o e ram := by
  obtain ⟨c, r, evs, hi, he, t, ht, hh⟩ := h
  exact ⟨c, r, evs, hi, he, t, hsub t ht, hh⟩

/-- What a checked state's well-formedness gives the proofs. -/
theorem wf_parts {cfg : Config} {s : AState} (h : s.wf cfg = true) :
    s.regs.length = 31 ∧ (∀ c ∈ s.mem, c.wf cfg = true) ∧ (∀ c ∈ s.mem, c.base = .rel → s.hnd = true) := by
  simp only [AState.wf, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, Bool.or_eq_true,
    Bool.not_eq_true'] at h
  obtain ⟨⟨⟨hl, hc⟩, habs⟩, _⟩ := h
  refine ⟨hl, hc, fun c hc' hb => ?_⟩
  rcases habs with hh | habs
  · exact hh
  · have := habs c hc'; rw [hb] at this; cases this

/-- A handler-frame cell lies in the stack region, so it is apart from any
    static address. -/
theorem rel_disj_static {cfg : Config} {ρ : Nat → Word} {c : Cell} {A : Word} {wd : Width}
    (hs : SpOk cfg (ρ 2).toNat) (hc : c.wf cfg = true) (hb : c.base = .rel)
    (hst : cfg.isStatic A.toNat wd.bytes = true) : Disj (c.at ρ) c.w A wd := by
  simp only [Cell.wf, hb, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨ho, hn⟩, _⟩ := hc
  obtain ⟨_, h1, h2⟩ := rel_addr (n := c.w.bytes) hs ho hn
  have hat : c.at ρ = ρ 2 + w c.addr := by simp [Cell.at, hb]
  have hram := hs.ram; have hpin := hs.pin; have hbase := hs.base; have hlo := hs.lo
  have hd := static_disj_stack (A := ρ 2 + w c.addr) (m := c.w.bytes) hst h1 h2 hram
  have hsA : A.toNat + wd.bytes ≤ cfg.ramEnd := by
    simp only [Config.isStatic, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hst
    omega
  unfold Config.ramEnd at hram hpin hsA
  rw [hat]
  apply disj_of_nat (by omega) (by omega)
  omega

/-- Any abstract load that succeeds: the platform does not fault and hands
    on a described value. -/
theorem absLoad_sound {cfg : Config} {s : AState} {av : AV} {wd : Width} {atomic : Bool} {v : AV}
    (h : absLoad cfg s av wd atomic = some v) (hv : ValidImg cfg.img) {ρ : Nat → Word}
    {ram : Word → BitVec 8} {A : Word} (hA : av.gam ρ A) (hsp : s.hnd = true → SpOk cfg (ρ 2).toNat)
    (hm : MemHolds ρ ram s.mem) (o : Oracle) (i : Nat) (evs : List Event) (k : Word → Eff) :
    ∃ r i', interp cfg.board cfg.img o (.load wd A atomic k) ram i evs =
      interp cfg.board cfg.img o (k r) ram i' evs ∧ v.gam ρ r ∧ Fits wd r := by
  cases av with
  | vals as => exact absLoad_vals_sound h hv hA hm o i evs k
  | sym sv off =>
    by_cases hsv : sv = 2
    · subst hsv
      have hnd : s.hnd = true := by
        have := h; simp only [absLoad] at this
        split at this
        · next hc => simp only [Bool.and_eq_true] at hc; exact hc.1.1.1
        · simp at this
      simp only [AV.gam] at hA
      obtain ⟨he, hr, hf⟩ := absLoad_rel_sound h (hsp hnd) hm o i evs k
      exact ⟨_, i, by rw [hA]; exact he, hr, hf⟩
    · exfalso; simp [absLoad, hsv] at h
  | _ => simp [absLoad] at h

/-- Any abstract store that succeeds, from a well-formed state. -/
theorem absStore_sound {cfg : Config} {s : AState} {av : AV} {wd : Width} {V : AV} {atomic : Bool}
    {memF : List Cell} (h : absStore cfg s av wd V atomic = some memF)
    (hram : cfg.board.ramBase + cfg.board.ramSize ≤ M32) (hwf : s.wf cfg = true) {ρ : Nat → Word}
    {ram : Word → BitVec 8} {A x : Word} (hA : av.gam ρ A) (hV : V.gam ρ x)
    (hsp : s.hnd = true → SpOk cfg (ρ 2).toNat) (hm : MemHolds ρ ram s.mem)
    (o : Oracle) (i : Nat) (evs : List Event) (k : Eff) :
    ∃ ram' evs', StoreEffect cfg ram A x wd ram' evs' ∧
      interp cfg.board cfg.img o (.store wd A x atomic k) ram i evs =
        interp cfg.board cfg.img o k ram' i (evs ++ evs') ∧ MemHolds ρ ram' memF := by
  obtain ⟨_, hcells, hrelH⟩ := wf_parts hwf
  cases av with
  | vals as =>
    exact absStore_vals_sound h hram hA hV hm hcells hrelH
      (fun c hc hb hstat => rel_disj_static (hsp (hrelH c hc hb)) (hcells c hc) hb hstat) o i evs k
  | sym sv off =>
    by_cases hsv : sv = 2
    · subst hsv
      have hnd : s.hnd = true := by
        have := h; simp only [absStore] at this
        split at this
        · next hc => simp only [Bool.and_eq_true] at hc; exact hc.1.1.1
        · simp at this
      simp only [AV.gam] at hA
      obtain ⟨hi, hm'⟩ := absStore_rel_sound h (hsp hnd) hV hm hwf hnd o i evs k
      have e1 : ρ 2 + BitVec.ofNat 32 off = A := hA.symm
      have e2 : ρ 2 + w off = A := hA.symm
      rw [e1, e2] at hi; rw [e2] at hm'
      exact ⟨_, [], .ram, by rw [hi]; simp, hm'⟩
    · exfalso; simp [absStore, hsv] at h
  | _ => simp [absStore] at h

theorem ctl_resv {ρ : Nat → Word} {s : AState} {c : Core} (h : CtlHolds ρ s c) (b : Bool) :
    CtlHolds ρ s { c with resv := b } :=
  ⟨h.mie, h.mpie, h.mpp, h.mieReg, h.mtvec, h.mepc, h.mcause, h.mscratch⟩

theorem ctl_setc {ρ : Nat → Word} {s : AState} {c : Core} (h : CtlHolds ρ s c) (r : Reg) (x : Word) :
    CtlHolds ρ s (c.set r x) :=
  ctl_same h (by unfold Core.sameCsr; rw [Core.set_ctl])

theorem ctl_pc {ρ : Nat → Word} {s : AState} {c : Core} (h : CtlHolds ρ s c) (p : Word) :
    CtlHolds ρ s { c with pc := p } :=
  ⟨h.mie, h.mpie, h.mpp, h.mieReg, h.mtvec, h.mepc, h.mcause, h.mscratch⟩

theorem ctl_mem {ρ : Nat → Word} {s : AState} {c : Core} (h : CtlHolds ρ s c) (mem : List Cell) :
    CtlHolds ρ { s with mem := mem } c :=
  ⟨h.mie, h.mpie, h.mpp, h.mieReg, h.mtvec, h.mepc, h.mcause, h.mscratch⟩

theorem mstatusOf_toNat_core : ∀ a b : Bool, ∀ p : Fin 4,
    (((if a then 8 else 0) ||| (if b then 0x80 else 0) ||| ((BitVec.ofFin p : BitVec 2).setWidth 32 <<< 11)) :
      Word).toNat = (if a then 8 else 0) + (if b then 0x80 else 0) + p.val * 2048 := by
  decide +kernel

theorem mstatusOf_toNat (c : Core) :
    (mstatusOf c).toNat = (if c.mie_ then 8 else 0) + (if c.mpie then 0x80 else 0) + c.mpp.toNat * 2048 := by
  have := mstatusOf_toNat_core c.mie_ c.mpie c.mpp.toFin
  simpa [mstatusOf] using this

theorem mayBe_mem {t : Tri} {b : Bool} (h : t.mayBe b = true) : b ∈ [false, true].filter t.mayBe := by
  rw [List.mem_filter]; exact ⟨by cases b <;> simp, h⟩

theorem mstatus_sound {ρ : Nat → Word} {s : AState} {c : Core} (h : CtlHolds ρ s c) :
    (mkVals (mstatusVals s)).gam ρ (mstatusOf c) := by
  apply mkVals_sound
  refine ⟨_, ?_, by rw [mstatusOf_toNat]; exact Nat.mod_eq_of_lt (mstatusOf_toNat c ▸ toNat_lt _)⟩
  simp only [mstatusVals, List.mem_flatMap, List.mem_map]
  exact ⟨c.mie_, mayBe_mem h.mie, c.mpie, mayBe_mem h.mpie, c.mpp.toNat, h.mpp, rfl⟩

theorem mip_le (v : Word) : (v &&& mieMask).toNat ≤ 0x888 := by
  rw [BitVec.toNat_and]; exact Nat.and_le_right

/-- Reading a CSR the abstract state describes: no fault, and a described value. -/
theorem csrReadAbs_sound {ρ : Nat → Word} {s : AState} {c : Core} {addr : Nat} {av : AV}
    (h : csrReadAbs s addr = some av) (hc : CtlHolds ρ s c) {B : Board} {img : List Segment} (o : Oracle)
    (k : Word → Eff) (ram : Word → BitVec 8) (i : Nat) (evs : List Event) :
    ∃ r i', interp B img o (csrRead c addr k) ram i evs = interp B img o (k r) ram i' evs ∧ av.gam ρ r := by
  unfold csrReadAbs at h; unfold csrRead
  split at h
  · next h1 => rw [if_pos h1]; cases h; exact ⟨_, i, rfl, mstatus_sound hc⟩
  rw [if_neg ‹_›]; split at h
  · next h1 => rw [if_pos h1]; cases h; exact ⟨_, i, rfl, hc.mieReg⟩
  rw [if_neg ‹_›]; split at h
  · next h1 => rw [if_pos h1]; cases h; exact ⟨_, i, rfl, hc.mtvec⟩
  rw [if_neg ‹_›]; split at h
  · next h1 => rw [if_pos h1]; cases h; exact ⟨_, i, rfl, hc.mscratch⟩
  rw [if_neg ‹_›]; split at h
  · next h1 => rw [if_pos h1]; cases h; exact ⟨_, i, rfl, hc.mepc⟩
  rw [if_neg ‹_›]; split at h
  · next h1 => rw [if_pos h1]; cases h; exact ⟨_, i, rfl, hc.mcause⟩
  rw [if_neg ‹_›]; split at h
  · next h1 =>
    rw [if_pos h1]; cases h
    exact ⟨_, i + 1, rfl, Nat.zero_le _, mip_le _⟩
  rw [if_neg ‹_›]; split at h
  · next h1 => rw [if_pos h1]; cases h; exact ⟨_, i, rfl, const0_gam ρ⟩
  · simp at h

theorem tri_all {l : List Nat} {f : Nat → Bool} {y : Nat} (hy : y ∈ l) :
    Tri.mayBe (if (l.map f).all id then .yes else if (l.map f).all (!·) then .no else .any) (f y) = true := by
  by_cases h1 : (l.map f).all id = true
  · rw [if_pos h1]
    simp only [List.all_eq_true, List.mem_map, id] at h1
    exact h1 _ ⟨y, hy, rfl⟩
  · rw [if_neg h1]
    by_cases h2 : (l.map f).all (!·) = true
    · rw [if_pos h2]
      simp only [List.all_eq_true, List.mem_map] at h2
      simp [Tri.mayBe, h2 _ ⟨y, hy, rfl⟩]
    · rw [if_neg h2]; rfl

theorem getLsbD_div (x : Word) (i : Nat) : x.getLsbD i = (x.toNat / 2 ^ i % 2 == 1) := by
  rw [BitVec.getLsbD, Nat.testBit_eq_decide_div_mod_eq]; cases h : x.toNat / 2 ^ i % 2 == 1 <;> simp_all

theorem mstatus_mask (x : Word) (h : x.toNat &&& (M32 - 1 - 0x1888) = 0) : ¬ (x &&& ~~~(0x1888 : Word) ≠ 0) := by
  intro hne; apply hne
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, BitVec.toNat_not]
  exact h

theorem extract_toNat (x : Word) (s n : Nat) : (x.extractLsb' s n).toNat = x.toNat / 2 ^ s % 2 ^ n := by
  rw [BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]

/-- Writing a CSR from a described value: no fault, and the control state
    after it is described by the abstract one. Registers, RAM and pc are not
    touched. -/
theorem csrWriteAbs_sound {ρ : Nat → Word} {s s'' : AState} {c : Core} {addr : Nat} {nv : AV} {x : Word}
    (h : csrWriteAbs s addr nv = some s'') (hc : CtlHolds ρ s c) (hx : nv.gam ρ x) (fin : Core → Eff) :
    ∃ c', csrWrite c addr x fin = fin c' ∧ CtlHolds ρ s'' c' ∧ (∀ r, c'.get r = c.get r) ∧
      s''.regs = s.regs ∧ s''.mem = s.mem ∧ s''.pc = s.pc := by
  unfold csrWriteAbs at h; unfold csrWrite
  split at h
  · next h1 =>
    rw [if_pos h1]
    cases nv with
    | vals l =>
      simp only at h
      split at h
      · next hall =>
        cases h
        simp only [AV.gam] at hx
        simp only [List.all_eq_true, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hall
        obtain ⟨hm, hp⟩ := hall _ hx
        have hmpp : (x.extractLsb' 11 2).toNat = x.toNat / 2048 % 4 := extract_toNat x 11 2
        have hmpp' : ¬ (x.extractLsb' 11 2 ≠ 0 ∧ x.extractLsb' 11 2 ≠ 3) := by
          intro ⟨a, b⟩
          rcases hp with hp | hp
          · exact a (BitVec.eq_of_toNat_eq (by rw [hmpp, hp]; rfl))
          · exact b (BitVec.eq_of_toNat_eq (by rw [hmpp, hp]; rfl))
        rw [if_neg (mstatus_mask x hm), if_neg hmpp']
        refine ⟨_, rfl, ⟨?_, ?_, ?_, hc.mieReg, hc.mtvec, hc.mepc, hc.mcause, hc.mscratch⟩,
          fun _ => rfl, rfl, rfl, rfl⟩
        · simp only; rw [getLsbD_div x 3]; exact tri_all (f := fun x => x / 8 % 2 == 1) hx
        · simp only; rw [getLsbD_div x 7]; exact tri_all (f := fun x => x / 128 % 2 == 1) hx
        · simp only; rw [hmpp]
          exact mem_norm.mpr ⟨_, List.mem_map_of_mem hx, (Nat.mod_eq_of_lt (by simp [M32]; omega)).symm⟩
      · simp at h
    | _ => simp at h
  rw [if_neg ‹_›]; split at h
  · next h1 =>
    rw [if_pos h1]
    split at h
    · simp at h
    cases h
    exact ⟨_, rfl, ⟨hc.mie, hc.mpie, hc.mpp, band_sound hx (const_sound' (by decide)), hc.mtvec, hc.mepc,
      hc.mcause, hc.mscratch⟩, fun _ => rfl, rfl, rfl, rfl⟩
  rw [if_neg ‹_›]; split at h
  · next h1 =>
    rw [if_pos h1]
    split at h
    · simp at h
    cases nv with
    | vals l =>
      simp only at h
      split at h
      · next hall =>
        cases h
        simp only [AV.gam] at hx
        simp only [List.all_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hall
        have hw : (if x.extractLsb' 0 2 = 0 then fin { c with mtvec := x }
            else if x.extractLsb' 0 2 = 1 ∧ x.toNat % 128 = 1 then fin { c with mtvec := x }
            else .unsupported "mtvec mode or vectored base alignment") = fin { c with mtvec := x } := by
          have he := extract_toNat x 0 2
          simp only [Nat.pow_zero, Nat.div_one] at he
          by_cases h0 : x.extractLsb' 0 2 = 0
          · rw [if_pos h0]
          · rw [if_neg h0]
            rcases hall _ hx with h4 | h128
            · exact absurd (BitVec.eq_of_toNat_eq (by rw [he]; simpa using h4)) h0
            · rw [if_pos ⟨BitVec.eq_of_toNat_eq (by rw [he]; simp; omega), h128⟩]
        rw [hw]
        exact ⟨_, rfl, ⟨hc.mie, hc.mpie, hc.mpp, hc.mieReg, hx, hc.mepc, hc.mcause, hc.mscratch⟩,
          fun _ => rfl, rfl, rfl, rfl⟩
      · simp at h
    | _ => simp at h
  rw [if_neg ‹_›]; split at h
  · next h1 =>
    rw [if_pos h1]
    split at h
    · simp at h
    cases h
    exact ⟨_, rfl, ⟨hc.mie, hc.mpie, hc.mpp, hc.mieReg, hc.mtvec, hc.mepc, hc.mcause, hx⟩,
      fun _ => rfl, rfl, rfl, rfl⟩
  rw [if_neg ‹_›]; split at h
  · next h1 =>
    rw [if_pos h1]; cases h
    exact ⟨_, rfl, ⟨hc.mie, hc.mpie, hc.mpp, hc.mieReg, hc.mtvec,
      band_sound hx (const_sound' (by decide)), hc.mcause, hc.mscratch⟩, fun _ => rfl, rfl, rfl, rfl⟩
  rw [if_neg ‹_›]; split at h
  · next h1 =>
    rw [if_pos h1]; cases h
    exact ⟨_, rfl, hc, fun _ => rfl, rfl, rfl, rfl⟩
  · simp at h

theorem lift_or_top_sound {ρ : Nat → Word} {f : Word → Word → Word} {a b : AV} {x y : Word}
    (ha : a.gam ρ x) (hb : b.gam ρ y) :
    (match a, b with | .vals p, .vals q => lift2 f p q | _, _ => .top).gam ρ (f x y) := by
  split
  · exact lift2_sound ha hb
  · trivial

theorem csr_operand_sound {ρ : Nat → Word} {s : AState} {c : Core}
    (hr : ∀ r : Reg, (s.get r).gam ρ (c.get r)) (src : CsrSrc) :
    (match src with | .reg r => s.get r | .imm v => AV.const v.toNat).gam ρ
      (match src with | .reg r => c.get r | .imm v => v) := by
  cases src with
  | reg r => exact hr r
  | imm v => exact const_sound' (Nat.mod_eq_of_lt (toNat_lt v)).symm

/-! ### Instruction cases -/

section Cases
variable {cfg : Config} {ρ : Nat → Word} {s : AState} {m : Machine} {len : Word} {ts : List AState}
  (hs : StateHolds ρ s m) (hl : s.regs.length = 31) (o : Oracle)
include hs hl

theorem case_lui {rd : Reg} {imm : Word} (h : absExec cfg s len.toNat (.lui rd imm) = some ts) :
    StepOk cfg ρ ts o (exec m.core len (.lui rd imm)) m.ram := by
  simp only [absExec, Option.some.injEq] at h; subst h
  rw [exec_lui]
  exact regwrite_sound hs hl (const_sound' (Nat.mod_eq_of_lt (toNat_lt imm)).symm) o

theorem case_auipc {rd : Reg} {imm : Word} (h : absExec cfg s len.toNat (.auipc rd imm) = some ts) :
    StepOk cfg ρ ts o (exec m.core len (.auipc rd imm)) m.ram := by
  simp only [absExec, Option.some.injEq] at h; subst h
  rw [exec_auipc]
  refine regwrite_sound hs hl (const_sound' ?_) o
  rw [hs.pc]; simp only [w, BitVec.toNat_add, BitVec.toNat_ofNat, M32]; omega

theorem case_opimm {op : AluOp} {rd rs1 : Reg} {imm : Word}
    (h : absExec cfg s len.toNat (.opimm op rd rs1 imm) = some ts) :
    StepOk cfg ρ ts o (exec m.core len (.opimm op rd rs1 imm)) m.ram := by
  simp only [absExec, Option.some.injEq] at h; subst h
  rw [exec_opimm]
  exact regwrite_sound hs hl (alu_sound op (hs.regs rs1)
    (const_sound' (Nat.mod_eq_of_lt (toNat_lt imm)).symm)) o

theorem case_op {op : AluOp} {rd rs1 rs2 : Reg}
    (h : absExec cfg s len.toNat (.op op rd rs1 rs2) = some ts) :
    StepOk cfg ρ ts o (exec m.core len (.op op rd rs1 rs2)) m.ram := by
  simp only [absExec, Option.some.injEq] at h; subst h
  rw [exec_op]
  exact regwrite_sound hs hl (alu_sound op (hs.regs rs1) (hs.regs rs2)) o

theorem case_muldiv {op : MulOp} {rd rs1 rs2 : Reg}
    (h : absExec cfg s len.toNat (.muldiv op rd rs1 rs2) = some ts) :
    StepOk cfg ρ ts o (exec m.core len (.muldiv op rd rs1 rs2)) m.ram := by
  have he : exec m.core len (.muldiv op rd rs1 rs2) =
      .done (m.core.wr rd (E5R.muldiv op (m.core.get rs1) (m.core.get rs2)) (m.core.pc + len)) := rfl
  rw [he]
  simp only [absExec] at h
  split at h
  · next x y ex ey =>
    simp only [Option.some.injEq] at h; subst h
    have h1 := hs.regs rs1; have h2 := hs.regs rs2
    rw [ex] at h1; rw [ey] at h2
    exact regwrite_sound hs hl (lift2_sound h1 h2) o
  · simp only [Option.some.injEq] at h; subst h
    exact regwrite_sound hs hl (v := .top) trivial o

theorem case_fence (h : absExec cfg s len.toNat .fence = some ts) :
    StepOk cfg ρ ts o (exec m.core len .fence) m.ram := by
  simp only [absExec, Option.some.injEq] at h; subst h; exact nop_sound hs o

theorem case_fencei (h : absExec cfg s len.toNat .fencei = some ts) :
    StepOk cfg ρ ts o (exec m.core len .fencei) m.ram := by
  simp only [absExec, Option.some.injEq] at h; subst h; exact nop_sound hs o

theorem case_wfi (h : absExec cfg s len.toNat .wfi = some ts) :
    StepOk cfg ρ ts o (exec m.core len .wfi) m.ram := by
  simp only [absExec, Option.some.injEq] at h; subst h; exact nop_sound hs o

theorem link_holds {rd : Reg} :
    ∀ r : Reg, ((s.set rd (.const ((s.pc + len.toNat) % M32))).get r).gam ρ
      ((m.core.set rd (m.core.pc + len)).get r) :=
  regs_set hl hs.regs rd (const_sound' (by rw [pc_adv hs.pc]; simp [w, M32]))

theorem case_jal {rd : Reg} {off : Word} (h : absExec cfg s len.toNat (.jal rd off) = some ts) :
    StepOk cfg ρ ts o (exec m.core len (.jal rd off)) m.ram := by
  simp only [absExec] at h
  rw [exec_jal]
  refine jumpAbs_sound h ?_ (ctl_same (ctl_set (ctl_of_holds hs) _ _)
    (by unfold Core.sameCsr; rw [Core.set_ctl])) (link_holds hs hl)
    (by rw [(AState.set_other _ _ _).1]; exact hs.mem) o
  simp only [List.mem_singleton]
  rw [hs.pc]; simp only [w, BitVec.toNat_add, BitVec.toNat_ofNat, M32]; omega

theorem case_jalr {rd rs1 : Reg} {off : Word} (h : absExec cfg s len.toNat (.jalr rd rs1 off) = some ts) :
    StepOk cfg ρ ts o (exec m.core len (.jalr rd rs1 off)) m.ram := by
  simp only [absExec] at h
  rw [exec_jalr]
  have hr := hs.regs rs1
  split at h
  · next l el =>
    rw [el] at hr
    have hT := mkVals_sound (ρ := ρ) (l := l.map fun x => ((w x + off) &&& ~~~1).toNat)
      (x := (m.core.get rs1 + off) &&& ~~~1)
      ⟨_, List.mem_map.mpr ⟨_, hr, rfl⟩, by rw [w_toNat]; exact Nat.mod_eq_of_lt (toNat_lt _)⟩
    generalize mkVals (l.map fun x => ((w x + off) &&& ~~~1).toNat) = t at h hT
    cases t with
    | vals l' =>
      exact jumpAbs_sound h hT (ctl_same (ctl_set (ctl_of_holds hs) _ _)
        (by unfold Core.sameCsr; rw [Core.set_ctl])) (link_holds hs hl)
        (by rw [(AState.set_other _ _ _).1]; exact hs.mem) o
    | _ => simp [jumpAbs] at h
  · simp [jumpAbs] at h

/-- Refining one register's fact by the branch outcome keeps the
    description of the (unchanged) core. -/
theorem refine_holds {cond : BrCond} {rs1 rs2 : Reg} (t : Bool)
    (ht : taken cond (m.core.get rs1) (m.core.get rs2) = t) :
    ∀ q : Reg, ((refineState cond t rs1 rs2 s (s.get rs1) (s.get rs2)).get q).gam ρ (m.core.get q) := by
  have keep : ∀ (r : Reg) (v : AV), v.gam ρ (m.core.get r) →
      ∀ q : Reg, ((s.set r v).get q).gam ρ (m.core.get q) := by
    intro r v hv q
    by_cases e : q = r
    · subst e
      by_cases hq : q.val = 0
      · have : q = 0 := Fin.ext hq
        subst this; rw [AState.get_zero, Core.get_zero]; exact const0_gam ρ
      · rw [AState.get_set_self _ _ _ hq hl]; exact hv
    · rw [AState.get_set_ne _ _ _ _ e]; exact hs.regs q
  unfold refineState
  split
  · next k hk =>
    have hb := hs.regs rs2
    rw [isConst_eq hk] at hb
    have hy := gam_single hb
    have hk' : k < M32 := by simp only [AV.gam, List.mem_singleton] at hb; rw [← hb]; exact toNat_lt _
    exact keep rs1 _ (refineL_sound cond t hk' (hs.regs rs1) (hy ▸ ht))
  · next k _ hk =>
    have ha := hs.regs rs1
    rw [isConst_eq hk] at ha
    have hx := gam_single ha
    have hk' : k < M32 := by simp only [AV.gam, List.mem_singleton] at ha; rw [← ha]; exact toNat_lt _
    exact keep rs2 _ (refineR_sound cond t hk' (hs.regs rs2) (hx ▸ ht))
  · exact hs.regs

theorem refine_other {cond : BrCond} {rs1 rs2 : Reg} (t : Bool) :
    (refineState cond t rs1 rs2 s (s.get rs1) (s.get rs2)).mem = s.mem ∧
    CtlHolds ρ (refineState cond t rs1 rs2 s (s.get rs1) (s.get rs2)) m.core := by
  unfold refineState
  split
  · exact ⟨(AState.set_other _ _ _).1, ctl_set (ctl_of_holds hs) _ _⟩
  · exact ⟨(AState.set_other _ _ _).1, ctl_set (ctl_of_holds hs) _ _⟩
  · exact ⟨rfl, ctl_of_holds hs⟩

theorem case_branch {cond : BrCond} {rs1 rs2 : Reg} {off : Word}
    (h : absExec cfg s len.toNat (.branch cond rs1 rs2 off) = some ts) :
    StepOk cfg ρ ts o (exec m.core len (.branch cond rs1 rs2 off)) m.ram := by
  simp only [absExec] at h
  rw [exec_branch]
  have hct := canTake_sound cond (hs.regs rs1) (hs.regs rs2)
  generalize hp : canTake cond (s.get rs1) (s.get rs2) = p at h hct
  obtain ⟨yes, no⟩ := p
  simp only at h hct
  cases htk : taken cond (m.core.get rs1) (m.core.get rs2)
  · -- falls through
    have hno := hct.2 htk
    subst hno
    simp only [if_true] at h
    obtain ⟨hmem, hctl⟩ := refine_other (cond := cond) (rs1 := rs1) (rs2 := rs2) hs hl false
    have hregs := refine_holds hs hl false htk
    cases hy : yes
    · rw [hy] at h; simp only [Bool.false_eq_true, if_false, Option.map_some, List.nil_append,
        Option.some.injEq] at h
      subst h
      refine ⟨_, _, _, interp_done o _ _ _ _, by simp, _, List.mem_singleton_self _, ?_⟩
      exact holds_mk (pc_adv hs.pc) (fun r => hregs r) (by simp only; rw [hmem]; exact hs.mem)
        (ctl_same (ctl_withPc hctl _) (Core.sameCsr_goto _ _))
    · rw [hy] at h
      simp only [if_true] at h
      cases hj : jumpAbs _ (.const (s.pc + off.toNat)) with
      | none => rw [hj] at h; simp at h
      | some tj =>
        rw [hj] at h; simp only [Option.map_some, Option.some.injEq] at h; subst h
        refine ⟨_, _, _, interp_done o _ _ _ _, by simp, _, List.mem_append_right _ (List.mem_singleton_self _), ?_⟩
        exact holds_mk (pc_adv hs.pc) (fun r => hregs r) (by simp only; rw [hmem]; exact hs.mem)
          (ctl_same (ctl_withPc hctl _) (Core.sameCsr_goto _ _))
  · -- taken
    have hyes := hct.1 htk
    subst hyes
    simp only [if_true] at h
    obtain ⟨hmem, hctl⟩ := refine_other (cond := cond) (rs1 := rs1) (rs2 := rs2) hs hl true
    have hregs := refine_holds hs hl true htk
    cases hj : jumpAbs _ (.const (s.pc + off.toNat)) with
    | none => rw [hj] at h; simp at h
    | some tj =>
      rw [hj] at h; simp only [Option.map_some, Option.some.injEq] at h; subst h
      have := jumpAbs_sound (cfg := cfg) hj (T := m.core.pc + off) (ram := m.ram) (c := m.core)
        (by simp only [AV.const, List.mem_singleton]; rw [hs.pc]
            simp only [w, BitVec.toNat_add, BitVec.toNat_ofNat, M32]; omega)
        hctl hregs (by rw [hmem]; exact hs.mem) o
      exact stepOk_mono this (fun t ht => List.mem_append_left _ ht)

theorem case_load {wd : Width} {signed : Bool} {rd rs1 : Reg} {off : Word}
    (hv : ValidImg cfg.img) (hsp : s.hnd = true → SpOk cfg (ρ 2).toNat)
    (h : absExec cfg s len.toNat (.load wd signed rd rs1 off) = some ts) :
    StepOk cfg ρ ts o (exec m.core len (.load wd signed rd rs1 off)) m.ram := by
  simp only [absExec] at h
  rw [exec_load]
  have hA := addC_sound off.toNat (hs.regs rs1)
  rw [w_len] at hA
  cases hl' : absLoad cfg s (addC (s.get rs1) off.toNat) wd false with
  | none => rw [hl'] at h; simp at h
  | some v =>
    rw [hl'] at h
    simp only [Option.bind_some, Option.some.injEq] at h; subst h
    generalize addC (s.get rs1) off.toNat = av at hA hl'
    have finish : ∀ r, v.gam ρ r → Fits wd r →
        StepOk cfg ρ [{ s.set rd (v.extend wd signed) with pc := (s.pc + len.toNat) % M32 }] o
          (.done (m.core.wr rd (extend wd signed r) (m.core.pc + len))) m.ram ∧ True :=
      fun r hr hf => ⟨regwrite_sound hs hl (extend_sound wd signed hr hf) o, trivial⟩
    cases av with
    | vals as =>
      obtain ⟨r, i', he, hr, hf⟩ := absLoad_vals_sound hl' hv hA hs.mem o 0 [] _
      obtain ⟨c, ram', evs, hi, hev, t, ht, hh⟩ := (finish r hr hf).1
      refine ⟨c, ram', evs, ?_, hev, t, ht, hh⟩
      rw [he]; simp only [interp_done] at hi ⊢; exact hi
    | sym sv off' =>
      by_cases hsv : sv = 2
      · subst hsv
        have hnd : s.hnd = true := by
          have := hl'; simp only [absLoad] at this
          split at this
          · next hc => simp only [Bool.and_eq_true] at hc; exact hc.1.1.1
          · simp at this
        simp only [AV.gam] at hA
        rw [hA]
        obtain ⟨he, hr, hf⟩ := absLoad_rel_sound hl' (hsp hnd) hs.mem o 0 [] _
        obtain ⟨c, ram', evs, hi, hev, t, ht, hh⟩ := (finish _ hr hf).1
        exact ⟨c, ram', evs, by rw [he]; exact hi, hev, t, ht, hh⟩
      · exfalso; simp [absLoad, hsv] at hl'
    | _ => simp [absLoad] at hl'

theorem case_store {wd : Width} {rs1 rs2 : Reg} {off : Word}
    (hram : cfg.board.ramBase + cfg.board.ramSize ≤ M32) (hwf : s.wf cfg = true)
    (hsp : s.hnd = true → SpOk cfg (ρ 2).toNat)
    (h : absExec cfg s len.toNat (.store wd rs1 rs2 off) = some ts) :
    StepOk cfg ρ ts o (exec m.core len (.store wd rs1 rs2 off)) m.ram := by
  simp only [absExec] at h
  rw [exec_store]
  obtain ⟨_, hcells, hrelH⟩ := wf_parts hwf
  have hA := addC_sound off.toNat (hs.regs rs1)
  rw [w_len] at hA
  cases hst : absStore cfg s (addC (s.get rs1) off.toNat) wd (s.get rs2) false with
  | none => rw [hst] at h; simp at h
  | some memF =>
    rw [hst] at h
    simp only [Option.bind_some, Option.some.injEq] at h; subst h
    generalize addC (s.get rs1) off.toNat = av at hA hst
    have conclude : ∀ ram' evs', StoreEffect cfg m.ram (m.core.get rs1 + off) (m.core.get rs2) wd ram' evs' →
        MemHolds ρ ram' memF →
        ∃ c, interp cfg.board cfg.img o (.done (m.core.goto (m.core.pc + len))) ram' 0 ([] ++ evs') =
          .ok c ram' evs' ∧ StateHolds ρ { s with mem := memF, pc := (s.pc + len.toNat) % M32 } ⟨c, ram'⟩ := by
      intro ram' evs' _ hm'
      refine ⟨m.core.goto (m.core.pc + len), by simp, ?_⟩
      exact holds_mk (pc_adv hs.pc) (fun r => hs.regs r) hm'
        (ctl_same ⟨hs.mie, hs.mpie, hs.mpp, hs.mieReg, hs.mtvec, hs.mepc, hs.mcause, hs.mscratch⟩
          (Core.sameCsr_goto _ _))
    have evok : ∀ ram' evs', StoreEffect cfg m.ram (m.core.get rs1 + off) (m.core.get rs2) wd ram' evs' →
        ∀ ev ∈ evs', EvOk cfg ev := by
      intro ram' evs' he ev hev
      cases he with
      | ram => simp at hev
      | dev hok => simp only [List.mem_singleton] at hev; subst hev; exact hok
    cases av with
    | vals as =>
      obtain ⟨ram', evs', he, hi, hm'⟩ := absStore_vals_sound hst hram hA (hs.regs rs2) hs.mem hcells hrelH
        (fun c hc hb hstat => rel_disj_static (hsp (hrelH c hc hb)) (hcells c hc) hb hstat) o 0 [] _
      obtain ⟨c, hc, hh⟩ := conclude ram' evs' he hm'
      exact ⟨c, ram', evs', by rw [hi]; exact hc, evok ram' evs' he, _, List.mem_singleton_self _, hh⟩
    | sym sv off' =>
      by_cases hsv : sv = 2
      · subst hsv
        have hnd : s.hnd = true := by
          have := hst; simp only [absStore] at this
          split at this
          · next hc => simp only [Bool.and_eq_true] at hc; exact hc.1.1.1
          · simp at this
        simp only [AV.gam] at hA
        obtain ⟨hi, hm'⟩ := absStore_rel_sound hst (hsp hnd) (hs.regs rs2) hs.mem hwf hnd o 0 [] _
        have e1 : ρ 2 + BitVec.ofNat 32 off' = m.core.get rs1 + off := hA.symm
        have e2 : ρ 2 + w off' = m.core.get rs1 + off := hA.symm
        rw [e1, e2] at hi; rw [e2] at hm'
        obtain ⟨c, hc, hh⟩ := conclude _ [] .ram hm'
        exact ⟨c, _, [], by rw [hi]; simpa using hc, by simp, _, List.mem_singleton_self _, hh⟩
      · exfalso; simp [absStore, hsv] at hst
    | _ => simp [absStore] at hst

/-- The state after an instruction that may have changed RAM and a reservation,
    written `rd` and fallen through. -/
theorem holds_after {memF : List Cell} {ram' : Word → BitVec 8} {c : Core} {rd : Reg} {v : AV} {x : Word}
    (hcg : ∀ r, c.get r = m.core.get r) (hctl : CtlHolds ρ s c) (hm : MemHolds ρ ram' memF)
    (hv : v.gam ρ x) :
    StateHolds ρ { ({ s with mem := memF } : AState).set rd v with pc := (s.pc + len.toNat) % M32 }
      ⟨{ c.set rd x with pc := m.core.pc + len }, ram'⟩ := by
  obtain ⟨e1, _⟩ := AState.set_other ({ s with mem := memF } : AState) rd v
  refine holds_mk (pc_adv hs.pc) ?_ (by simp only; rw [e1]; exact hm)
    (ctl_pc (ctl_setc (ctl_withPc (ctl_set (ctl_mem hctl memF) rd v) _) rd x) _)
  intro q
  rw [withPc_get, Core.get_withPc]
  exact regs_set (s := { s with mem := memF }) hl (fun r => by rw [hcg]; exact hs.regs r) rd hv q

theorem case_lr {rd rs1 : Reg} (hv : ValidImg cfg.img) (hsp : s.hnd = true → SpOk cfg (ρ 2).toNat)
    (h : absExec cfg s len.toNat (.lr rd rs1) = some ts) :
    StepOk cfg ρ ts o (exec m.core len (.lr rd rs1)) m.ram := by
  simp only [absExec, Option.bind_eq_some_iff, Option.some.injEq] at h
  obtain ⟨v, hld, rfl⟩ := h
  have he : exec m.core len (.lr rd rs1) = .load .w (m.core.get rs1) true
      (fun r => .done { ({ m.core with resv := true }.set rd r) with pc := m.core.pc + len }) := rfl
  rw [he]
  obtain ⟨r, i', hi, hr, _⟩ := absLoad_sound hld hv (hs.regs rs1) hsp hs.mem o 0 [] _
  refine ⟨_, _, _, by rw [hi]; exact interp_done o _ _ _ _, by simp, _, List.mem_singleton_self _, ?_⟩
  exact holds_after hs hl (c := { m.core with resv := true }) (fun _ => rfl) (ctl_resv (ctl_of_holds hs) true) hs.mem hr

theorem case_sc {rd rs1 rs2 : Reg} (hv : ValidImg cfg.img)
    (hram : cfg.board.ramBase + cfg.board.ramSize ≤ M32) (hwf : s.wf cfg = true)
    (hsp : s.hnd = true → SpOk cfg (ρ 2).toNat)
    (h : absExec cfg s len.toNat (.sc rd rs1 rs2) = some ts) :
    StepOk cfg ρ ts o (exec m.core len (.sc rd rs1 rs2)) m.ram := by
  simp only [absExec, Option.bind_eq_some_iff, Option.some.injEq] at h
  obtain ⟨_, hld, memF, hst, rfl⟩ := h
  let fail : Eff := .done { ({ m.core with resv := false }.set rd 1) with pc := m.core.pc + len }
  have he : exec m.core len (.sc rd rs1 rs2) = .load .w (m.core.get rs1) true (fun _ =>
      if ¬ m.core.resv then fail else .choose fun ok =>
        if ok then .store .w (m.core.get rs1) (m.core.get rs2) true
          (.done { ({ m.core with resv := false }.set rd 0) with pc := m.core.pc + len })
        else fail) := rfl
  rw [he]
  obtain ⟨r, i', hi, _, _⟩ := absLoad_sound hld hv (hs.regs rs1) hsp hs.mem o 0 [] _
  unfold StepOk; rw [hi]
  have hfail : ∀ j, ∃ c ram' evs, interp cfg.board cfg.img o fail m.ram j [] = .ok c ram' evs ∧
      (∀ ev ∈ evs, EvOk cfg ev) ∧
      ∃ t ∈ [{ (s.set rd (.const 1)) with pc := (s.pc + len.toNat) % M32 },
             { ({ s with mem := memF } : AState).set rd (.const 0) with pc := (s.pc + len.toNat) % M32 }],
        StateHolds ρ t ⟨c, ram'⟩ :=
    fun j => ⟨_, _, _, interp_done o _ _ _ _, by simp, _, List.mem_cons_self ..,
      holds_after (memF := s.mem) hs hl (c := { m.core with resv := false }) (fun _ => rfl) (ctl_resv (ctl_of_holds hs) false) hs.mem
        (const_sound' (by simp [M32]))⟩
  by_cases hres : m.core.resv = true
  · simp only [hres, not_true_eq_false, if_false, interp]
    cases (o i').getLsbD 0
    · exact hfail _
    · simp only [if_true]
      obtain ⟨ram', evs', hse, hsi, hm'⟩ :=
        absStore_sound hst hram hwf (hs.regs rs1) (hs.regs rs2) hsp hs.mem o (i' + 1) [] _
      refine ⟨_, _, _, by rw [hsi]; exact interp_done o _ _ _ _, ?_, _,
        List.mem_cons_of_mem _ (List.mem_singleton_self _), ?_⟩
      · intro ev hev
        cases hse with
        | ram => simp at hev
        | dev hok => simp only [List.nil_append, List.mem_singleton] at hev; subst hev; exact hok
      · exact holds_after hs hl (c := { m.core with resv := false }) (fun _ => rfl) (ctl_resv (ctl_of_holds hs) false) hm'
          (const_sound' (by simp))
  · simp only [hres, Bool.false_eq_true, not_false_eq_true, if_true]
    exact hfail _

theorem case_amo {op : AmoOp} {rd rs1 rs2 : Reg} (hv : ValidImg cfg.img)
    (hram : cfg.board.ramBase + cfg.board.ramSize ≤ M32) (hwf : s.wf cfg = true)
    (hsp : s.hnd = true → SpOk cfg (ρ 2).toNat)
    (h : absExec cfg s len.toNat (.amo op rd rs1 rs2) = some ts) :
    StepOk cfg ρ ts o (exec m.core len (.amo op rd rs1 rs2)) m.ram := by
  simp only [absExec, Option.bind_eq_some_iff, Option.some.injEq] at h
  obtain ⟨old, hld, memF, hst, rfl⟩ := h
  have he : exec m.core len (.amo op rd rs1 rs2) = .load .w (m.core.get rs1) true (fun r =>
      .store .w (m.core.get rs1) (amoOp op r (m.core.get rs2)) true
        (.done { (m.core.set rd r) with pc := m.core.pc + len })) := rfl
  rw [he]
  obtain ⟨r, i', hi, hr, _⟩ := absLoad_sound hld hv (hs.regs rs1) hsp hs.mem o 0 [] _
  unfold StepOk; rw [hi]
  have finish : ∀ {new : AV}, new.gam ρ (amoOp op r (m.core.get rs2)) →
      absStore cfg s (s.get rs1) .w new true = some memF →
      StepOk cfg ρ [{ ({ s with mem := memF } : AState).set rd old with pc := (s.pc + len.toNat) % M32 }] o
        (.store .w (m.core.get rs1) (amoOp op r (m.core.get rs2)) true
          (.done { (m.core.set rd r) with pc := m.core.pc + len })) m.ram := by
    intro new hn hst'
    obtain ⟨ram', evs', hse, hsi, hm'⟩ :=
      absStore_sound hst' hram hwf (hs.regs rs1) hn hsp hs.mem o 0 [] _
    refine ⟨_, _, _, by rw [hsi]; exact interp_done o _ _ _ _, ?_, _, List.mem_singleton_self _,
      holds_after hs hl (c := m.core) (fun _ => rfl) (ctl_of_holds hs) hm' hr⟩
    intro ev hev
    cases hse with
    | ram => simp at hev
    | dev hok => simp only [List.nil_append, List.mem_singleton] at hev; subst hev; exact hok
  have hrun : ∀ i, interp cfg.board cfg.img o (.store .w (m.core.get rs1) (amoOp op r (m.core.get rs2)) true
      (.done { (m.core.set rd r) with pc := m.core.pc + len })) m.ram i [] =
      interp cfg.board cfg.img o (.store .w (m.core.get rs1) (amoOp op r (m.core.get rs2)) true
      (.done { (m.core.set rd r) with pc := m.core.pc + len })) m.ram 0 [] := by
    intro i; simp only [interp]
  rw [hrun]
  split at hst
  · next _ _ y z hy => exact finish (lift2_sound hr (hy ▸ hs.regs rs2)) hst
  · exact finish (new := .top) trivial hst

/-- A CSR instruction, with the source operand and the written value
    abstracted: `wA`/`wC` say whether it writes, `newA`/`newC` what. -/
theorem csr_core {rd : Reg} {addr : Nat} {wA wC : Bool} {newA : AV → AV} {newC : Word → Word}
    (hw : wA = wC) (hnew : ∀ a x, a.gam ρ x → (newA a).gam ρ (newC x))
    (h : (if (wA && addr / 1024 == 3) = true then none else (csrReadAbs s addr).bind fun old =>
        if (!wA) = true then some [{ s.set rd old with pc := (s.pc + len.toNat) % M32 }] else
        (csrWriteAbs (s.set rd old) addr (newA old)).bind fun s'' =>
          some [{ s'' with pc := (s.pc + len.toNat) % M32 }]) = some ts) :
    StepOk cfg ρ ts o (if (wC && addr / 1024 == 3) = true then .trap .illegal else csrRead m.core addr fun old =>
      if (!wC) = true then .done { m.core.set rd old with pc := m.core.pc + len } else
      csrWrite (m.core.set rd old) addr (newC old) fun c' => .done { c' with pc := m.core.pc + len }) m.ram := by
  subst hw
  split at h
  · simp at h
  · next hcond =>
    rw [if_neg hcond]
    obtain ⟨old, hrd, hrest⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨r, i', hi, hr⟩ := csrReadAbs_sound hrd (ctl_of_holds hs) o _ m.ram 0 []
    unfold StepOk; rw [hi]
    cases hwa : wA
    · simp only [hwa, Bool.not_false, if_true, Option.some.injEq] at hrest ⊢
      subst hrest
      exact ⟨_, _, _, interp_done o _ _ _ _, by simp, _, List.mem_singleton_self _,
        holds_after (memF := s.mem) hs hl (c := m.core) (fun _ => rfl) (ctl_of_holds hs) hs.mem hr⟩
    · simp only [hwa, Bool.not_true, Bool.false_eq_true, if_false] at hrest ⊢
      obtain ⟨s'', hwr, hts⟩ := Option.bind_eq_some_iff.mp hrest
      simp only [Option.some.injEq] at hts; subst hts
      obtain ⟨c', hcw, hctl, hget, hregs, hmem, _⟩ := csrWriteAbs_sound hwr
        (ctl_setc (ctl_set (ctl_of_holds hs) rd old) rd r) (hnew _ _ hr)
        (fun c' => .done { c' with pc := m.core.pc + len })
      rw [hcw]
      refine ⟨_, _, _, interp_done o _ _ _ _, by simp, _, List.mem_singleton_self _, ?_⟩
      refine holds_mk (pc_adv hs.pc) ?_ ?_ (ctl_pc (ctl_withPc hctl _) _)
      · intro q
        rw [withPc_get, Core.get_withPc, hget]
        have : s''.get q = (s.set rd old).get q := by unfold AState.get; rw [hregs]
        rw [this]; exact regs_set hl hs.regs rd hr q
      · show MemHolds ρ m.ram s''.mem
        rw [hmem, (AState.set_other s rd old).1]; exact hs.mem

theorem case_csr {op : CsrOp} {rd : Reg} {src : CsrSrc} {addr : Nat}
    (h : absExec cfg s len.toNat (.csr op rd src addr) = some ts) :
    StepOk cfg ρ ts o (exec m.core len (.csr op rd src addr)) m.ram := by
  have he : exec m.core len (.csr op rd src addr) =
      execCsr m.core op rd src addr (fun c' => .done { c' with pc := m.core.pc + len }) := rfl
  rw [he]; unfold execCsr
  simp only [absExec] at h
  refine csr_core hs hl o ?_ ?_ h
  · cases src <;> rfl
  · intro a x hx
    have hop := csr_operand_sound hs.regs src
    cases op
    · exact hop
    · exact lift_or_top_sound (f := fun p q => p ||| q) hx hop
    · exact lift_or_top_sound (f := fun p q => p &&& ~~~q) hx hop

/-- One instruction: whatever the abstract transfer accepts, the concrete
    step does not fault, emits only allowed events, and lands in a state one
    of the abstract successors describes. -/
theorem absExec_sound {i : Instr} (hv : ValidImg cfg.img)
    (hram : cfg.board.ramBase + cfg.board.ramSize ≤ M32) (hwf : s.wf cfg = true)
    (hsp : s.hnd = true → SpOk cfg (ρ 2).toNat)
    (h : absExec cfg s len.toNat i = some ts) :
    StepOk cfg ρ ts o (exec m.core len i) m.ram := by
  cases i with
  | lui => exact case_lui hs hl o h
  | auipc => exact case_auipc hs hl o h
  | jal => exact case_jal hs hl o h
  | jalr => exact case_jalr hs hl o h
  | branch => exact case_branch hs hl o h
  | load => exact case_load hs hl o hv hsp h
  | store => exact case_store hs hl o hram hwf hsp h
  | opimm => exact case_opimm hs hl o h
  | op => exact case_op hs hl o h
  | muldiv => exact case_muldiv hs hl o h
  | lr => exact case_lr hs hl o hv hsp h
  | sc => exact case_sc hs hl o hv hram hwf hsp h
  | amo => exact case_amo hs hl o hv hram hwf hsp h
  | fence => exact case_fence hs hl o h
  | fencei => exact case_fencei hs hl o h
  | csr => exact case_csr hs hl o h
  | wfi => exact case_wfi hs hl o h
  | ecall => simp [absExec] at h
  | ebreak => simp [absExec] at h
  | mret => simp [absExec] at h

end Cases

/-! ### Covering successors -/

theorem covered_sound {ρ : Nat → Word} {cert : Cert} {t : AState} {j : Nat} {m : Machine}
    (h : covered cert t j = true) (hs : StateHolds ρ t m) :
    ∃ n, cert.nodes[j]? = some n ∧ StateHolds ρ n.s m := by
  unfold covered at h
  split at h
  · next n hn => exact ⟨n, hn, leq_state_sound h hs⟩
  · simp at h

theorem holds_with_mem {ρ : Nat → Word} {t : AState} {m : Machine} {mem : List Cell}
    (hs : StateHolds ρ t m) (hm : MemHolds ρ m.ram mem) : StateHolds ρ { t with mem := mem } m :=
  ⟨hs.pc, hs.regs, hm, hs.mie, hs.mpie, hs.mpp, hs.mieReg, hs.mtvec, hs.mepc, hs.mcause, hs.mscratch⟩

theorem Core.set_get_same (c : Core) (r q : Reg) : (c.set r (c.get r)).get q = c.get q := by
  rw [Core.get_set]
  by_cases h0 : q.val = 0
  · rw [if_pos h0]; have : q = 0 := Fin.ext h0
    subst this; rfl
  · rw [if_neg h0]
    by_cases e : q = r
    · rw [if_pos e, e]
    · rw [if_neg e]

/-- Narrowing a register to the value it has. -/
theorem holds_split {ρ : Nat → Word} {t : AState} {m : Machine} (hs : StateHolds ρ t m)
    (hl : t.regs.length = 31) (r : Reg) {v : Nat} (hv : v = (m.core.get r).toNat) :
    StateHolds ρ (t.set r (.vals [v])) m := by
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, _⟩ := AState.set_other t r (.vals [v])
  have hregs := regs_set hl hs.regs r (v := .vals [v]) (x := m.core.get r) (by simp [AV.gam, hv])
  refine ⟨by rw [e10]; exact hs.pc, fun q => ?_, by rw [e1]; exact hs.mem, e2 ▸ hs.mie, e3 ▸ hs.mpie,
    e4 ▸ hs.mpp, e5 ▸ hs.mieReg, e6 ▸ hs.mtvec, e7 ▸ hs.mepc, e8 ▸ hs.mcause, e9 ▸ hs.mscratch⟩
  have := hregs q
  rwa [Core.set_get_same] at this

theorem covered_len {cert : Cert} {t : AState} {j : Nat} (h : covered cert t j = true) :
    t.regs.length = 31 := by
  unfold covered at h
  split at h
  · simp only [AState.leq, Bool.and_eq_true, beq_iff_eq, and_assoc] at h; exact h.2.2.1
  · simp at h

theorem AState.set_len (s : AState) (r : Reg) (v : AV) : (s.set r v).regs.length = s.regs.length := by
  unfold AState.set; split <;> simp

theorem pinned_regs {pin : Option (Nat × Nat × Width)} {e : Edge} {r v : Nat} {t0 t' : AState}
    (h : pinned pin e r v t0 = some t') : t'.regs = t0.regs := by
  unfold pinned at h
  split at h
  · cases h; rfl
  · split at h
    · split at h
      · cases h; rfl
      · simp at h
    · simp at h

/-- A covered successor lands in a node. A pinning edge needs the loaded
    word to equal the destination register, which the load establishes. -/
theorem coveredE_sound {ρ : Nat → Word} {cert : Cert} {pin : Option (Nat × Nat × Width)} {t : AState}
    {e : Edge} {m : Machine} (h : coveredE cert pin t e = true) (hs : StateHolds ρ t m)
    (hpin : e.pin = true → ∀ rd a wd, pin = some (rd, a, wd) → ∀ hr : rd < 32, 0 < rd →
      ramRead m.ram (w a) wd = m.core.get ⟨rd, hr⟩) :
    ∃ j ∈ e.nodes, ∃ n, cert.nodes[j]? = some n ∧ StateHolds ρ n.s m := by
  unfold coveredE at h
  split at h
  · simp only [Bool.and_eq_true, Bool.not_eq_true'] at h
    obtain ⟨_, h⟩ := h
    split at h
    · next j hj => exact ⟨j, by rw [hj]; exact List.mem_singleton_self _, covered_sound h hs⟩
    · simp at h
  · next r _ =>
    split at h
    · next h0 =>
      split at h
      · next l hg =>
        have hx := hs.regs ⟨r, h0.2⟩
        rw [hg] at hx
        have hv := List.all_eq_true.mp h _ hx
        split at hv
        · next t' hp =>
          obtain ⟨j, hj, hc⟩ := List.any_eq_true.mp hv
          have hl : t.regs.length = 31 := by
            rw [← AState.set_len t ⟨r, h0.2⟩ (.vals [(m.core.get ⟨r, h0.2⟩).toNat]), ← pinned_regs hp]
            exact covered_len hc
          have ht' : StateHolds ρ t' m := by
            have hsp := holds_split hs hl ⟨r, h0.2⟩ (v := (m.core.get ⟨r, h0.2⟩).toNat) rfl
            unfold pinned at hp
            split at hp
            · cases hp; exact hsp
            · next hnp =>
              simp only [Bool.not_eq_true', Bool.not_eq_false] at hnp
              split at hp
              · next _ rd a wd =>
                split at hp
                · next hrd =>
                  cases hp
                  subst hrd
                  apply holds_with_mem hsp
                  apply setPlain_sound hsp.mem
                  simp only [AV.gam, List.mem_singleton]
                  rw [hpin hnp rd a wd rfl h0.2 h0.1]
                · simp at hp
              · simp at hp
          exact ⟨j, hj, covered_sound hc ht'⟩
        · simp at hv
      · simp at h
    · simp at h

/-! ### One node, one instruction -/

theorem ram_aligned {cfg : Config} {a : Nat} {wd : Width} (h : classify cfg a wd = some .ram) :
    (w a).toNat % wd.bytes = 0 := by
  have := (classify_ram h).1
  simp only [w, BitVec.toNat_ofNat]
  cases wd <;> simp only [Width.bytes] at this ⊢ <;> omega

/-- A load at a known RAM address, zero-extended or a whole word: the
    destination register ends up equal to the loaded word. -/
theorem load_exact {cfg : Config} {ρ : Nat → Word} {s : AState} {m : Machine} {len : Word}
    {wd : Width} {signed : Bool} {rd rs1 : Reg} {off : Word} {a : Nat}
    (hs : StateHolds ρ s m) (hsg : (signed && wd != .w) = false)
    (ha : addC (s.get rs1) off.toNat = .vals [a]) (hc : classify cfg a wd = some .ram) (o : Oracle) :
    interp cfg.board cfg.img o (exec m.core len (.load wd signed rd rs1 off)) m.ram 0 [] =
      .ok (m.core.wr rd (ramRead m.ram (w a) wd) (m.core.pc + len)) m.ram [] := by
  rw [exec_load]
  have hA := addC_sound off.toNat (hs.regs rs1)
  rw [w_len, ha] at hA
  simp only [AV.gam, List.mem_singleton] at hA
  have hA' : m.core.get rs1 + off = w a := by rw [← hA, w_toNat]
  rw [hA', interp_load_ram o (ram_aligned hc) (classify_ram hc).2, interp_done]
  have hf := ramRead_fits m.ram (w a) wd
  simp only [Fits, Width.bytes] at hf
  cases wd <;> cases signed <;> simp at hsg
  · simp only [E5R.extend]; rw [and_ff _ (by omega)]
  · simp only [E5R.extend]; rw [and_ffff _ (by omega)]
  · rfl
  · rfl

theorem fetch_bridge {img : List Segment} {pc : Nat} {i : Instr} {len : Nat}
    (h : successors.fetchDecode' img pc = some (i, len)) :
    pc % 2 = 0 ∧ ∃ bits len', fetch img (w pc) = some (bits, len') ∧ decode bits len' = some i ∧
      len = len'.toNat := by
  unfold successors.fetchDecode' at h
  split at h
  · simp at h
  · next hpc =>
    refine ⟨by omega, ?_⟩
    split at h
    · next bits len' hf =>
      cases hd : decode bits len' with
      | none => rw [hd] at h; simp at h
      | some i' =>
        rw [hd] at h; simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨bits, len', hf, hd, rfl⟩
    · simp at h

/-- A node's non-`mret` instruction: under every environment the step does
    not fault, emits allowed events, and lands in a node of one of its edges. -/
theorem instr_sound {cfg : Config} {cert : Cert} {n : Node} {ρ : Nat → Word} {m : Machine}
    {i : Instr} {len : Nat} (hok : instrOk cfg cert n = true) (hs : StateHolds ρ n.s m)
    (hwf : n.s.wf cfg = true) (hv : ValidImg cfg.img) (hram : cfg.board.ramBase + cfg.board.ramSize ≤ M32)
    (hsp : n.s.hnd = true → SpOk cfg (ρ 2).toNat)
    (hfd : successors.fetchDecode' cfg.img n.s.pc = some (i, len)) (hnm : i ≠ .mret) (o : Oracle) :
    ∃ c ram evs, stepInstr cfg.board cfg.img m o = .ok c ram evs ∧ (∀ ev ∈ evs, EvOk cfg ev) ∧
      ∃ e ∈ n.succ, ∃ j ∈ e.nodes, ∃ n', cert.nodes[j]? = some n' ∧ StateHolds ρ n'.s ⟨c, ram⟩ := by
  have hl := (wf_parts hwf).1
  obtain ⟨hpc2, bits, len', hf, hd, rfl⟩ := fetch_bridge hfd
  have hstep : stepInstr cfg.board cfg.img m o =
      interp cfg.board cfg.img o (exec m.core len' i) m.ram 0 [] := by
    unfold stepInstr
    rw [hs.pc, lsb_even (by simp only [w, BitVec.toNat_ofNat]; omega)]
    simp only [Bool.false_eq_true, if_false, hf, hd]
  unfold instrOk at hok
  rw [hfd] at hok
  split at hok
  · next heq => simp only [Option.some.injEq, Prod.mk.injEq] at heq; exact absurd heq.1 hnm
  · next _ _ heq =>
    simp only [Option.some.injEq, Prod.mk.injEq] at heq
    obtain ⟨rfl, rfl⟩ := heq
    split at hok
    · next ts habs =>
      simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at hok
      obtain ⟨hlen, hall⟩ := hok
      obtain ⟨c, ram, evs, hi, hev, t, ht, hh⟩ := absExec_sound hs hl o hv hram hwf hsp habs
      refine ⟨c, ram, evs, by rw [hstep, hi], hev, ?_⟩
      obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp ht
      have hk' : k < n.succ.length := hlen ▸ hk
      have hz : (ts[k], n.succ[k]) ∈ List.zip ts n.succ := by
        have hkz : k < (List.zip ts n.succ).length := by simp; omega
        have := List.getElem_mem hkz
        simpa using this
      have hcov := hall _ hz
      refine ⟨n.succ[k], List.getElem_mem hk', coveredE_sound hcov hh ?_⟩
      intro _ rd a wd hpa hr hr0
      unfold pinAddr at hpa
      rw [hfd] at hpa
      split at hpa
      · next wd' signed rd' rs1 off _ heq =>
        simp only [Option.some.injEq, Prod.mk.injEq] at heq
        obtain ⟨rfl, -⟩ := heq
        split at hpa
        · simp at hpa
        · next hsg =>
          split at hpa
          · next a' ha =>
            split at hpa
            · next hc =>
              simp only [Option.some.injEq, Prod.mk.injEq] at hpa
              obtain ⟨rfl, rfl, rfl⟩ := hpa
              have hex := load_exact (len := len') (rd := rd') hs (Bool.eq_false_iff.mpr hsg) ha
                (by simpa using hc) o
              rw [hi] at hex
              simp only [Result.ok.injEq] at hex
              obtain ⟨rfl, rfl, -⟩ := hex
              have : (⟨rd'.val, hr⟩ : Reg) = rd' := rfl
              rw [this, Core.wr_get_self _ _ _ _ (by omega)]
            · simp at hpa
          · simp at hpa
      · simp at hpa
    · simp at hok
  · simp at hok

end E5R.AI
