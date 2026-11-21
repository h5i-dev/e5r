import NoCompiler.Refine

/-
Control for decision 2026-11-21 (3): why a refinement carries A's run.

A is one illegal word (0x00000000 decodes to nothing), so A cannot take a
step from its entry. `RefinesRel` assumes A's safe run, so for this A it holds
against EVERY B, here an arbitrary `cB` (`vacuous`). `Refines` also requires
`ARuns`, which is false for this A at any specification that admits an entry
(`no_runs`), so no `Refines` from it can be proved (`no_refines`).
-/
namespace Examples.Refine.Vacuous
open NoCompiler

def cA : Code := ⟨0x1000#64, #[0#32]⟩
def DA : Dom := [(0x1000#64, 4)]
def eA : Word := 0x1000#64

/-- Every entry: no precondition, no postcondition. -/
def spAny : Spec Unit where
  pre := fun _ _ => True
  post := fun _ _ _ => True

theorem instr_none : cA.instr eA = none := by decide

/-- A has no safe run from its entry. -/
theorem no_exec {P : Perm} {Q : State → Prop} {s : State} (hpc : s.pc = eA) (hx : s.exit = none) :
    ¬ Exec cA P DA Q s := by
  intro h
  cases h with
  | done hq =>
    rcases hq.1 with hd | hd
    · exact hd (by rw [hpc]; decide)
    · exact hd hx
  | step _ hex _ =>
    obtain ⟨_, st⟩ := hex
    cases st with
    | exec _ hi _ _ => rw [hpc, instr_none] at hi; cases hi
    | sys _ hi _ _ => rw [hpc, instr_none] at hi; cases hi

/-- Vacuous: this A "refines" into any code at all, relationally. -/
theorem vacuous (cB : Code) (DB : Dom) (eB : Word) : RefinesRel spAny cA DA eA cB DB eB := by
  intro a s he _ _ hA
  exact absurd hA (no_exec he.pc he.live)

/-- An entry state: pc at A, ra and sp aligned, ra outside A. -/
def s0 : State := ⟨fun _ => 0x8000#64, eA, fun _ => 0, [], none⟩

theorem entry_s0 : Entry DA eA s0 where
  pc := rfl
  live := rfl
  ret := by decide
  retAligned := by decide
  sp := by decide

theorem no_runs : ¬ ARuns spAny cA DA eA :=
  fun h => no_exec rfl rfl (h () s0 entry_s0 trivial)

/-- So no `Refines` from this A can be stated with a proof. -/
theorem no_refines (cB : Code) (DB : Dom) (eB : Word) : ¬ Refines spAny cA DA eA cB DB eB :=
  fun h => no_runs h.runs

end Examples.Refine.Vacuous
