import Projects.thermostat.HeadMethodPrefix
import Projects.thermostat.HeadByteInput
namespace E5R.Thermostat.HeadMethodInputSpec
open E5R E5R.Thermostat HttpRequestSpec HeadLineScanSpec

theorem bad_request (g : Nat → Nat) (j : Nat) (bad : ¬HeadMethodPrefix.Good g j) :
    requestLine g 0 j=.bad 400 := by
  unfold requestLine
  dsimp only
  split
  · rfl
  · rename_i inside
    have valid : 0<scan isTchar g 0 j ∧ scan isTchar g 0 j<j := by omega
    have notSpace : g (scan isTchar g 0 j)≠32 := by
      intro space
      exact bad ⟨valid.1,valid.2,space⟩
    split
    · rfl
    · rename_i space
      exact False.elim (space notSpace)

theorem good_congr (g h : Nat → Nat) (j : Nat) (agree : ∀ k, k<j → g k=h k) :
    HeadMethodPrefix.Good g j ↔ HeadMethodPrefix.Good h j := by
  have eq := scan_congr isTchar g h 0 j agree
  unfold HeadMethodPrefix.Good
  rw [eq]
  dsimp only
  by_cases inside : scan isTchar h 0 j<j
  · rw [agree _ inside]
  · constructor <;> intro x <;> exact False.elim (inside x.2.1)

theorem term_zero_bound (g : Nat → Nat) (j n : Nat) (term : lineTerm g j n=0) : j+1<n := by
  unfold lineTerm at term
  split at term
  · contradiction
  · split at term
    · contradiction
    · split at term
      · contradiction
      · omega

def Bad (input : List (BitVec 8)) : Prop :=
  let n := min input.length 1024
  let g := window (HttpRequestBytes.bytes input) n
  ¬HeadMethodPrefix.Good g (lineEnd g 0 n)

instance (input : List (BitVec 8)) : Decidable (Bad input) := by unfold Bad;infer_instance

theorem classification (input : List (BitVec 8)) (term : HeadByteInput.term input=0) (bad : Bad input) :
    HttpRequestBytes.parse input 1024 1024=.reject 400 := by
  unfold HttpRequestBytes.parse parseHead
  rw [HeadByteInput.read_limit]
  dsimp only
  have term' := term
  dsimp only [HeadByteInput.term] at term'
  rw [term']
  simp only [show ¬(0=1) by decide,show ¬(0=2) by decide,ite_false]
  rw [bad_request _ _ bad]
end E5R.Thermostat.HeadMethodInputSpec
