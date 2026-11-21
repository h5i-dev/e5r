import SweBinKernel
/-!
# What swe-bin should pay

The file to review. In plain terms, with no machine words or arrays:
* a submission pays `FULL` exactly when the harness's last test report is about the submitted
  binary and says that every FAIL_TO_PASS and every PASS_TO_PASS test passed;
* it pays `BONUS` more exactly when, in addition, the proof checker's last result is a checked
  proof about that same binary, of the kind the mode asks for: a refinement of the original
  (`Refines`) in patch mode, a `Verified` theorem against a non-vacuous spec in scratch mode;
* nothing else pays.
`Theorems.lean` proves that the extracted Rust kernel does this.
-/
open Aeneas Aeneas.Std swe_bin_kernel

namespace swe_bin_kernel.Spec

def FULL : Nat := 1000
def BONUS : Nat := 250

/-- Two digests are the same binary. -/
def SameBinary (a b : Hash) : Prop := a.w.val = b.w.val

/-- The proof kind each mode pays a bonus for. -/
def bonusKind : Mode → ProofKind
  | .Patch => .Refines
  | .Scratch => .Verified

/-- Every test of the task passed against binary `h`, by the last report. -/
def AllPass (t : Task) (tests : Option Tests) (h : Hash) : Prop :=
  ∃ r, tests = some r ∧ SameBinary r.binary h ∧ r.f2p_passed.val = t.f2p.val ∧
    r.p2p_passed.val = t.p2p.val

/-- The last proof result is a checked proof about binary `h`, of the mode's kind. -/
def ProofOk (t : Task) (proof : Option Proof) (h : Hash) : Prop :=
  ∃ p, proof = some p ∧ p.checked = true ∧ SameBinary p.binary h ∧ p.kind = bonusKind t.mode

open Classical in
/-- What submitting `h` pays. -/
noncomputable def reward (t : Task) (tests : Option Tests) (proof : Option Proof) (h : Hash) : Nat :=
  if AllPass t tests h then (if ProofOk t proof h then FULL + BONUS else FULL) else 0

end swe_bin_kernel.Spec
