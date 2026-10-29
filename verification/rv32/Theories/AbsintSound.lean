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

end E5R.AI
