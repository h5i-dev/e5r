import Projects.thermostat.HeadLineScanSpec
namespace E5R.Thermostat.MainQuerySpec
open E5R E5R.Thermostat HttpRequestSpec

/-- First question mark inside the original target span, or its end. -/
def notQuestion (b : Nat) : Bool := decide (b≠63)
def position (g : Nat → Nat) (start finish : Nat) := scan notQuestion g start finish

def pathLength (g : Nat → Nat) (start finish : Nat) := position g start finish-start

def queryStart (g : Nat → Nat) (start finish : Nat) :=
  if position g start finish<finish then position g start finish+1 else start

def queryLength (g : Nat → Nat) (start finish : Nat) :=
  if position g start finish<finish then finish-position g start finish-1 else 0

def bytes (input : List (BitVec 8)) (k : Nat) := (input[k]?.getD 0#8).toNat

def path (input : List (BitVec 8)) (start finish : Nat) :=
  (input.drop start).take (pathLength (bytes input) start finish)

def query (input : List (BitVec 8)) (start finish : Nat) :=
  (input.drop (queryStart (bytes input) start finish)).take (queryLength (bytes input) start finish)

theorem bounds (g : Nat → Nat) (start finish : Nat) (ordered : start≤finish) :
    start≤position g start finish ∧ position g start finish≤finish := ⟨scan_ge _ _ _ _,scan_le _ _ _ _ ordered⟩

theorem step (g : Nat → Nat) (i finish : Nat) (inside : i<finish) (skip : g i≠63) :
    position g i finish=position g (i+1) finish := by
  unfold position
  exact scan_cont inside (by simp [notQuestion,skip])

theorem found (g : Nat → Nat) (i finish : Nat) (inside : i<finish) (hit : g i=63) : position g i finish=i := by
  unfold position
  exact scan_stop inside (by simp [notQuestion,hit])

theorem end_at (g : Nat → Nat) (finish : Nat) : position g finish finish=finish := by
  unfold position
  exact scan_end (by omega)

theorem first (g : Nat → Nat) (start finish : Nat) (found : position g start finish<finish) :
    g (position g start finish)=63 := by
  have stop := HeadLineScanSpec.scan_pred notQuestion g start finish found
  by_cases hit : g (position g start finish)=63
  · exact hit
  · exfalso
    have miss := hit
    have yes : notQuestion (g (position g start finish))=true := by simp [notQuestion,miss]
    change notQuestion (g (position g start finish))=false at stop
    rw [yes] at stop
    contradiction

theorem before_position (g : Nat → Nat) (start finish k : Nat) (lo : start≤k) (hi : k<position g start finish) : g k≠63 := by
  by_cases inside : start<finish
  · by_cases hit : g start=63
    · rw [found g start finish inside hit] at hi;omega
    · by_cases same : k=start
      · simpa only [same] using hit
      · rw [step g start finish inside hit] at hi
        exact before_position g (start+1) finish k (by omega) hi
  · have eq : position g start finish=start := by unfold position;exact scan_end (by omega)
    rw [eq] at hi
    omega
termination_by finish-start
 decreasing_by omega

theorem spans (g : Nat → Nat) (start finish : Nat) (ordered : start≤finish) :
    start+pathLength g start finish=position g start finish ∧
      queryStart g start finish+queryLength g start finish≤finish := by
  have bound := bounds g start finish ordered
  unfold pathLength queryStart queryLength
  split <;> omega
end E5R.Thermostat.MainQuerySpec
