import NoCompiler.Shift
import NoCompiler.Vocab

/-
Relocatable proofs of leaf functions (docs/isa/v1.md, relocation).

`Module.fetch_link`: at any layout the module can be linked at, the image
`M.link L` holds `f`'s patched words from `L.addr f`. For a function without
relocations those are its words, wherever it is; with `VerifiedImg.shift`
(NoCompiler/Shift.lean) a proof of it at one image gives `Verified M f spec`,
over every layout (`Verified.of_leaf`), provided it calls nothing, all its
instructions are pcFree, and the specification does not look at the pc or
`ra`. The proof is not redone: the same theorem, at every layout.

Functions with calls or data addresses have relocated words, which differ
between layouts; their proofs need the call and data-address lemmas at a
symbolic layout (T1, docs/isa/v1.md).
-/
namespace NoCompiler
namespace Module

theorem find?_eq_of_unique {α : Type} {p : α → Bool} {l : List α} {f : α} (hf : f ∈ l)
    (hp : p f = true) (hu : ∀ g ∈ l, p g = true → g = f) : l.find? p = some f := by
  induction l with
  | nil => simp at hf
  | cons x xs ih =>
    rw [List.find?_cons]
    cases hx : p x
    · simp only
      rcases List.mem_cons.1 hf with rfl | hf
      · rw [hp] at hx; cases hx
      · exact ih hf (fun g hg => hu g (List.mem_cons_of_mem _ hg))
    · simp only [Option.some.injEq]; exact hu x List.mem_cons_self hx

theorem eq_of_nodup_map {α β : Type} (k : α → β) {l : List α} (hn : (l.map k).Nodup) {f g : α}
    (hf : f ∈ l) (hg : g ∈ l) (h : k g = k f) : g = f := by
  induction l with
  | nil => simp at hf
  | cons x xs ih =>
    rw [List.map_cons, List.nodup_cons] at hn
    have hx : ∀ y ∈ xs, k y ≠ k x := fun y hy e => hn.1 (List.mem_map.2 ⟨y, hy, e⟩)
    rcases List.mem_cons.1 hf with hf' | hf' <;> rcases List.mem_cons.1 hg with hg' | hg'
    · rw [hf', hg']
    · exact absurd (hf' ▸ h) (hx g hg')
    · exact absurd (hg' ▸ h).symm (hx f hf')
    · exact ih hn.2 hf' hg'

theorem eq_of_name {M : Module} {L : Layout} (hL : M.Ok L) {f g : RFunc} (hf : f ∈ M.funcs)
    (hg : g ∈ M.funcs) (h : g.name = f.name) : g = f :=
  eq_of_nodup_map (·.name) hL.names hf hg h

/-- The image holds `f`'s patched words from `L.addr f`. -/
theorem fetch_link {M : Module} {L : Layout} (hL : M.Ok L) {f : RFunc} (hf : f ∈ M.funcs)
    {i : Nat} (hi : i < f.words.length) :
    (M.link L).fetch (L.addr f.name + BitVec.ofNat 64 (4 * i)) = some ((f.patched L).getD i 0) := by
  obtain ⟨hal, hin⟩ := hL.funcs f hf
  have hsz := hL.size
  have hb := hL.base
  generalize hyd : L.addr f.name + BitVec.ofNat 64 (4 * i) = y
  have hoff : (y - L.base).toNat = (L.addr f.name - L.base).toNat + 4 * i := by
    have e : y - L.base = (L.addr f.name - L.base) + BitVec.ofNat 64 (4 * i) := by
      rw [← hyd]; bv_omega
    rw [e, BitVec.toNat_add, toNat_ofNat_of_lt (by omega)]
    exact Nat.mod_eq_of_lt (by omega)
  have h4 : (L.addr f.name - L.base).toNat % 4 = 0 := by
    unfold aligned at hal hb
    rw [BitVec.toNat_sub]
    have := BitVec.isLt L.base
    omega
  have hy : (y - L.addr f.name).toNat = 4 * i := by
    rw [← hyd]; rw [add_ofNat_sub_toNat _ (by omega)]
  unfold link
  dsimp only [Code.fetch]
  rw [hoff, if_pos (show _ % 4 = 0 by omega)]
  have hj : ((L.addr f.name - L.base).toNat + 4 * i) / 4 < L.size := by omega
  rw [List.getElem?_toArray, List.getElem?_map, List.getElem?_range hj, Option.map_some]
  congr 1
  have hx : L.base + BitVec.ofNat 64 (4 * (((L.addr f.name - L.base).toNat + 4 * i) / 4)) = y := by
    rw [show 4 * (((L.addr f.name - L.base).toNat + 4 * i) / 4) = (y - L.base).toNat by omega]
    rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]; bv_omega
  rw [hx]
  unfold wordAt
  rw [find?_eq_of_unique hf (by simp [hy]; omega)]
  · simp only [hy]; congr 1; omega
  · intro g hg hp
    by_cases hn : g.name = f.name
    · exact eq_of_name hL hf hg hn
    · exfalso
      have hd : Region.Disjoint ⟨L.addr f.name, 4 * f.words.length⟩ ⟨L.addr g.name, 4 * g.words.length⟩ :=
        ⟨hL.disjoint f hf g hg (Ne.symm hn), hL.disjoint g hg f hf hn⟩
      have := hd.not_mem (x := y) (by show (y - L.addr f.name).toNat < 4 * f.words.length; rw [hy]; omega)
      exact this (by show (y - L.addr g.name).toNat < 4 * g.words.length; simpa using hp)

theorem func?_eq {M : Module} {L : Layout} (hL : M.Ok L) {f : RFunc} (hf : f ∈ M.funcs) :
    M.func? f.name = some f :=
  find?_eq_of_unique hf (by simp) (fun g hg hp => eq_of_name hL hf hg (by simpa using hp))

/-- The domain of a function that calls nothing is its own code. -/
theorem dom_leaf {M : Module} {L : Layout} (hL : M.Ok L) {f : RFunc} (hf : f ∈ M.funcs)
    (hc : f.callees = []) : M.dom L f.name = [f.region L] := by
  unfold dom
  cases h : M.funcs.length with
  | zero => exact absurd (List.length_pos_of_mem hf) (by omega)
  | succ n =>
    simp only [reach, func?_eq hL hf, hc, Option.map_some, List.flatMap_nil, Option.getD_some,
      List.filterMap_cons, List.filterMap_nil, List.map_cons, List.map_nil]
    rfl

end Module

/-- A leaf function without relocations, all of whose instructions are pcFree,
    proved at one image `c₀` from `e₀`, is verified at every layout. The image
    only has to hold the function's words from `e₀` (`hwords`), at an aligned
    base, with `e₀` aligned. -/
theorem Verified.of_leaf {α : Type} {M : Module} {f : RFunc} (hf : f ∈ M.funcs)
    (hrel : f.relocs = []) (hfree : ∀ w ∈ f.words, (decode w).all Instr.pcFree = true)
    {c₀ : Code} {e₀ : Word} (hb₀ : aligned c₀.base 4) (he₀ : aligned e₀ 4)
    (hwords : ∀ i, i < f.words.length →
      c₀.fetch (e₀ + BitVec.ofNat 64 (4 * i)) = some (f.words.getD i 0))
    (hlen : 4 * f.words.length < 2 ^ 64)
    {sp : Spec α} (hs : sp.ShiftInv) (hv : VerifiedImg c₀ [(e₀, 4 * f.words.length)] e₀ sp) :
    Verified M f.name sp := by
  intro L hL
  obtain ⟨hal, _⟩ := hL.funcs f hf
  have hcal : f.callees = [] := by simp [RFunc.callees, hrel]
  rw [Module.dom_leaf hL hf hcal]
  have hpat : f.patched L = f.words := by simp [RFunc.patched, hrel]
  generalize hδd : L.addr f.name - e₀ = δ
  have hδ : aligned δ 4 := by
    unfold aligned at *; rw [← hδd, BitVec.toNat_sub]
    have := BitVec.isLt e₀; omega
  have hD : [f.region L] = Dom.shift δ [(e₀, 4 * f.words.length)] := by
    simp only [Dom.shift, RFunc.region, List.map_cons, List.map_nil, ← hδd]
    congr 2; bv_omega
  have he : L.addr f.name = e₀ + δ := by rw [← hδd]; bv_omega
  rw [hD, he]
  refine VerifiedImg.shift ⟨?_, ?_, hδ⟩ hs hv
  · -- Both images hold the same words, aligned the same way.
    intro x hx
    have hk : (x - e₀).toNat < 4 * f.words.length := by simpa [Dom.mem] using hx
    by_cases h4 : (x - e₀).toNat % 4 = 0
    · obtain ⟨i, hi⟩ : ∃ i, (x - e₀).toNat = 4 * i := ⟨(x - e₀).toNat / 4, by omega⟩
      have hxe : x = e₀ + BitVec.ofNat 64 (4 * i) := by
        rw [← hi, BitVec.ofNat_toNat, BitVec.setWidth_eq]; bv_omega
      have hxd : x + δ = L.addr f.name + BitVec.ofNat 64 (4 * i) := by rw [hxe, he]; bv_omega
      unfold Code.instr
      rw [hxd, Module.fetch_link hL hf (by omega), hxe, hwords i (by omega), hpat]
    · -- Neither image has an instruction at an address that is not word-aligned.
      have hmis : ∀ (c : Code) (y b : Word), aligned c.base 4 → aligned b 4 →
          (y - b).toNat % 4 ≠ 0 → c.fetch y = none := by
        intro c y b hc hb hy
        dsimp only [Code.fetch]; rw [if_neg]
        unfold aligned at hc hb
        intro h; apply hy
        rw [BitVec.toNat_sub] at h ⊢
        have := BitVec.isLt b; have := BitVec.isLt c.base; have := BitVec.isLt y
        omega
      unfold Code.instr
      rw [hmis c₀ x e₀ hb₀ he₀ h4, hmis (M.link L) (x + δ) (L.addr f.name) hL.base hal (by
        rw [show x + δ - L.addr f.name = x - e₀ by rw [he]; bv_omega]; exact h4)]
  · intro x i hx hi
    have hk : (x - e₀).toNat < 4 * f.words.length := by simpa [Dom.mem] using hx
    unfold Code.instr at hi
    cases hfe : c₀.fetch x with
    | none => rw [hfe] at hi; cases hi
    | some w =>
      rw [hfe] at hi
      -- The word is one of f's.
      have h4 : (x - e₀).toNat % 4 = 0 := by
        dsimp only [Code.fetch] at hfe
        split at hfe
        · unfold aligned at hb₀ he₀
          rename_i h
          rw [BitVec.toNat_sub] at h ⊢
          have := BitVec.isLt e₀; have := BitVec.isLt c₀.base; have := BitVec.isLt x
          omega
        · cases hfe
      obtain ⟨j, hj⟩ : ∃ j, (x - e₀).toNat = 4 * j := ⟨(x - e₀).toNat / 4, by omega⟩
      have hxe : x = e₀ + BitVec.ofNat 64 (4 * j) := by
        rw [← hj, BitVec.ofNat_toNat, BitVec.setWidth_eq]; bv_omega
      rw [hxe, hwords j (by omega)] at hfe
      cases hfe
      have hmem : f.words.getD j 0 ∈ f.words := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]; simp
      have := hfree _ hmem
      simp only [Option.bind_some] at hi
      rw [hi] at this; simpa using this

end NoCompiler
