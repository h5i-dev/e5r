import NoCompiler.Refine
import NoCompiler.Relocate

/-
Refinement of unchanged code, at function granularity (docs/isa/ledger.md,
"Reuse of unchanged code").

`RefinesRel.of_code_eq`: code that agrees with A's on A's region refines A
there, by `RefinesRel.refl` and `Reach.congr_code`, with no stepping.

`Refines.of_sub`: two modules that both hold `M`'s functions unchanged (the
same `RFunc`s) and link at a layout `L`: on `f`'s code region at `L`, the second
image refines the first, given the first's run (decision 2026-11-21 (3)). The
side conditions are decided by comparing `RFunc`s.
-/
namespace NoCompiler

theorem RefinesRel.of_code_eq {α : Type} {sp : Spec α} {cA cB : Code} {D : Dom} {e : Word}
    (hc : ∀ x, D.mem x → cB.instr x = cA.instr x) : RefinesRel sp cA D e cB D e :=
  fun a s he hb hp hA => Reach.congr_code hc (RefinesRel.refl cA D e a s he hb hp hA)

theorem Refines.of_code_eq {α : Type} {sp : Spec α} {cA cB : Code} {D : Dom} {e : Word}
    (hA : ARuns sp cA D e) (hc : ∀ x, D.mem x → cB.instr x = cA.instr x) : Refines sp cA D e cB D e :=
  ⟨hA, RefinesRel.of_code_eq hc⟩

/-- Unchanged functions refine themselves across modules: `MA` and `MB` both
    hold `M`'s `RFunc`s and link at `L`; on `f`'s region at `L`, `MB`'s image
    refines `MA`'s. -/
theorem Refines.of_sub {α : Type} {sp : Spec α} {M MA MB : Module} {L : Layout} {f : Sym}
    (hA : MA.Ok L) (hB : MB.Ok L) (hsa : ∀ g ∈ M.funcs, g ∈ MA.funcs) (hsb : ∀ g ∈ M.funcs, g ∈ MB.funcs)
    (hn : (M.funcs.map (·.name)).Nodup)
    (hrun : ARuns sp (MA.link L) (M.dom L f) (L.addr f)) :
    Refines sp (MA.link L) (M.dom L f) (L.addr f) (MB.link L) (M.dom L f) (L.addr f) := by
  have hL := Module.Ok.of_sub hA hsa hn
  refine Refines.of_code_eq hrun (fun x hx => ?_)
  unfold Dom.mem Module.dom at hx
  obtain ⟨r, hr, hx⟩ := List.any_eq_true.1 hx
  simp only [List.mem_map, List.mem_filterMap] at hr
  obtain ⟨g, ⟨_, _, hg⟩, rfl⟩ := hr
  have hgm : g ∈ M.funcs := List.mem_of_find?_eq_some hg
  have hx' : (x - L.addr g.name).toNat < 4 * g.words.length := by
    simpa [RFunc.region] using of_decide_eq_true hx
  rw [Module.instr_congr hL hB hgm (hsb g hgm) hx', Module.instr_congr hL hA hgm (hsa g hgm) hx']

/-- The same, with A's run from a theorem about `M`: an unchanged verified
    function refines itself across the two modules with nothing proved but
    the comparison of `RFunc`s. -/
theorem Refines.of_sub_verified {α : Type} {sp : Layout → Spec α} {M MA MB : Module} {L : Layout} {f : Sym}
    (hA : MA.Ok L) (hB : MB.Ok L) (hsa : ∀ g ∈ M.funcs, g ∈ MA.funcs) (hsb : ∀ g ∈ M.funcs, g ∈ MB.funcs)
    (hn : (M.funcs.map (·.name)).Nodup) (hv : Verified M f sp) :
    Refines (sp L) (MA.link L) (M.dom L f) (L.addr f) (MB.link L) (M.dom L f) (L.addr f) := by
  have hL := Module.Ok.of_sub hA hsa hn
  refine Refines.of_sub hA hB hsa hsb hn (ARuns.of_verified (VerifiedImg.congr_code (fun x hx => ?_) (hv L hL)))
  unfold Dom.mem Module.dom at hx
  obtain ⟨r, hr, hx⟩ := List.any_eq_true.1 hx
  simp only [List.mem_map, List.mem_filterMap] at hr
  obtain ⟨g, ⟨_, _, hg⟩, rfl⟩ := hr
  have hgm : g ∈ M.funcs := List.mem_of_find?_eq_some hg
  exact Module.instr_congr hL hA hgm (hsa g hgm) (by simpa [RFunc.region] using of_decide_eq_true hx)

end NoCompiler
