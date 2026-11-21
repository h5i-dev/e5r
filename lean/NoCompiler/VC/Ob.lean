import NoCompiler.VC.Mem

/-
Reflective discharge of access obligations, milestone 3 (docs/design/prior-art-others.md,
"Implementation plan").

An access's address, as the symbolic run builds it, is usually a register
value plus offsets: `Sym.lin` reads such a term as variable + constant. A
function's precondition supplies facts about its variables: a base is
aligned, a base starts a readable or writable region of known size. Both are
data, and `Ob.check facts o` decides an obligation from them by arithmetic
on literals; `Ob.check_sound` is proved once. A run's obligations are then
closed by `obs.all (Ob.check facts) = true`, evaluated by the kernel, and
`Reach.of_runW_checked` gives the trusted `Reach` from that and the facts.
-/
namespace NoCompiler.VC.M

/-- What a precondition tells about the variables. -/
inductive Fact
  /-- Variable `n` is `al`-aligned. -/
  | aligned (n : Nat) (al : Nat)
  /-- Variable `n` starts a region of `size` bytes, readable (and writable when `wr`). -/
  | region (n : Nat) (size : Nat) (wr : Bool)
  deriving DecidableEq, Repr

def Fact.den (ρ : Nat → Word) (P : Perm) : Fact → Prop
  | .aligned n al => NoCompiler.aligned (ρ n) al
  | .region n size wr => if wr then P.canWrite (ρ n) size else P.canRead (ρ n) size

/-- Widths that divide 2^64, the only ones `aligned` is used with. -/
def okWidth (w : Nat) : Bool := w == 1 || w == 2 || w == 4 || w == 8

/-- The checker. -/
def Ob.check (facts : List Fact) : Ob → Bool
  | .aligned a w =>
    -- A byte access is always aligned.
    w == 1 ||
    match a.lin with
    | some (n, k) => okWidth w && k.toNat % w == 0 &&
        facts.any fun f => match f with
          | .aligned m al => m == n && al % w == 0
          | _ => false
    | none => false
  | .canRead a w =>
    match a.lin with
    | some (n, k) => facts.any fun f => match f with
        | .region m size _ => m == n && k.toNat + w ≤ size
        | _ => false
    | none => false
  | .canWrite a w =>
    match a.lin with
    | some (n, k) => facts.any fun f => match f with
        | .region m size wr => m == n && wr && k.toNat + w ≤ size
        | _ => false
    | none => false

/-- A sub-range of a covered range is covered (wrapping only shrinks the offset). -/
theorem covers_sub {r : Region} {b k : Word} {w size : Nat} (h : r.covers b size)
    (hk : k.toNat + w ≤ size) : r.covers (b + k) w := by
  unfold Region.covers at *
  have e : b + k - r.base = (b - r.base) + k := by bv_omega
  rw [e, BitVec.toNat_add]
  exact Nat.le_trans (Nat.add_le_add_right (Nat.mod_le _ _) w) (by omega)

theorem aligned_add {x k : Word} {al w : Nat} (hx : NoCompiler.aligned x al) (hal : al % w = 0)
    (hk : k.toNat % w = 0) (hw : okWidth w = true) : NoCompiler.aligned (x + k) w := by
  unfold NoCompiler.aligned at *
  have hdiv : 2 ^ 64 % w = 0 := by
    simp only [okWidth, Bool.or_eq_true, beq_iff_eq] at hw
    rcases hw with ((rfl | rfl) | rfl) | rfl <;> decide
  have hxw : x.toNat % w = 0 := by
    obtain ⟨q, hq⟩ := Nat.dvd_of_mod_eq_zero hal
    have : x.toNat % (w * q) = 0 := by rw [← hq]; exact hx
    exact Nat.mod_eq_zero_of_dvd (Nat.dvd_trans (Nat.dvd_mul_right w q) (Nat.dvd_of_mod_eq_zero this))
  rw [BitVec.toNat_add]
  have h1 : w ∣ x.toNat + k.toNat := Nat.dvd_add (Nat.dvd_of_mod_eq_zero hxw) (Nat.dvd_of_mod_eq_zero hk)
  have h2 : w ∣ 2 ^ 64 := Nat.dvd_of_mod_eq_zero hdiv
  exact Nat.mod_eq_zero_of_dvd ((Nat.dvd_mod_iff h2).2 h1)

/-- The checker, sound: proved once. -/
theorem Ob.check_sound {ρ : Nat → Word} {μ : Word → Byte} {P : Perm} {facts : List Fact}
    (hf : ∀ f ∈ facts, f.den ρ P) {o : Ob} (h : o.check facts = true) : o.den ρ μ P := by
  cases o with
  | aligned a w =>
    simp only [Ob.check] at h
    by_cases h1 : w = 1
    · subst h1; simp only [Ob.den, NoCompiler.aligned, Nat.mod_one]
    rw [show (w == 1) = false from by simpa using h1, Bool.false_or] at h
    split at h
    · rename_i n k hl
      simp only [Bool.and_eq_true, beq_iff_eq, List.any_eq_true] at h
      obtain ⟨⟨hw, hk⟩, f, hfm, hfa⟩ := h
      cases f with
      | aligned m al =>
        simp only [Bool.and_eq_true, beq_iff_eq] at hfa
        obtain ⟨rfl, hal⟩ := hfa
        simp only [Ob.den, Sym.lin_den hl]
        exact aligned_add (hf _ hfm) hal hk hw
      | region => simp at hfa
    · simp at h
  | canRead a w =>
    simp only [Ob.check] at h
    split at h
    · rename_i n k hl
      simp only [List.any_eq_true] at h
      obtain ⟨f, hfm, hfa⟩ := h
      cases f with
      | region m size wr =>
        simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hfa
        obtain ⟨rfl, hle⟩ := hfa
        simp only [Ob.den, Sym.lin_den hl]
        have hr := hf _ hfm
        simp only [Fact.den] at hr
        split at hr
        · rcases hr with h0 | ⟨r, hr, hc⟩
          · exact .inl (by omega)
          · exact .inr ⟨r, List.mem_append_right _ hr, covers_sub hc hle⟩
        · rcases hr with h0 | ⟨r, hr, hc⟩
          · exact .inl (by omega)
          · exact .inr ⟨r, hr, covers_sub hc hle⟩
      | aligned => simp at hfa
    · simp at h
  | canWrite a w =>
    simp only [Ob.check] at h
    split at h
    · rename_i n k hl
      simp only [List.any_eq_true] at h
      obtain ⟨f, hfm, hfa⟩ := h
      cases f with
      | region m size wr =>
        simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hfa
        obtain ⟨⟨rfl, rfl⟩, hle⟩ := hfa
        simp only [Ob.den, Sym.lin_den hl]
        have hr := hf _ hfm
        simp only [Fact.den, ite_true] at hr
        rcases hr with h0 | ⟨r, hr, hc⟩
        · exact .inl (by omega)
        · exact .inr ⟨r, hr, covers_sub hc hle⟩
      | aligned => simp at hfa
    · simp at h

/-- The trusted `Reach` from a run whose obligations the checker discharges
    from the facts: what a generated proof is, for one segment. -/
theorem Reach.of_runW_checked {ρ : Nat → Word} {μ : Word → Byte} {c : Code} {P : Perm} {D : Dom}
    {Q : State → Prop} {facts : List Fact} {S S' : SState} {obs : List Ob} {s : State}
    (hc : c.base = S.pc) (hb : 4 * c.words.size < 2 ^ 64) (hm : Matches ρ μ S s) (hx : s.exit = none)
    (h : runW D c.words.toList S = some (S', obs)) (hchk : obs.all (Ob.check facts) = true)
    (hf : ∀ f ∈ facts, f.den ρ P) (hQ : ∀ s', Matches ρ μ S' s' → s'.exit = none → Q s') :
    Reach c P D Q s :=
  Reach.of_runW (k := 0) (rest := []) (by simp) (by simpa using hb) (by simp [hc]) hm hx h
    (fun o ho => Ob.check_sound hf (List.all_eq_true.1 hchk o ho)) hQ

end NoCompiler.VC.M
