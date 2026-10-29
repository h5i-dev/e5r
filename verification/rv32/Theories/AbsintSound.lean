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

end E5R.AI
