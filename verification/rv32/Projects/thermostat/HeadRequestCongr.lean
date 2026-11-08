import Projects.thermostat.HeadLineScanSpec
import Projects.thermostat.HeadVersionSpec
namespace E5R.Thermostat.HeadRequestCongr
open E5R E5R.Thermostat HttpRequestSpec HeadLineScanSpec

/-- Version decoding depends only on bytes strictly inside its declared line.
    Wrong spans return 3 without reading; an eight-byte span has five prefix
    and three digit bytes, all explicitly bounded below e. -/
theorem version (g h : Nat → Nat) (s e : Nat) (agree : ∀ k, k<e → g k=h k) :
    HttpRequestSpec.version g s e=HttpRequestSpec.version h s e := by
  by_cases bad : e<s ∨ e-s≠8
  · simp only [HttpRequestSpec.version,bad,ite_true]
  · have width : e=s+8 := by omega
    rw [width,HeadVersionSpec.version,HeadVersionSpec.version]
    have p : HeadVersionSpec.Prefix g s ↔ HeadVersionSpec.Prefix h s := by
      unfold HeadVersionSpec.Prefix
      rw [agree s (by omega),agree (s+1) (by omega),agree (s+2) (by omega),agree (s+3) (by omega),agree (s+4) (by omega)]
    simp only [p,agree (s+5) (by omega),agree (s+6) (by omega),agree (s+7) (by omega)]

/-- Request-line parsing is extensional on its actual line slice, including
    all refusal paths and the typed spans of successful results. -/
theorem requestLine (g h : Nat → Nat) (j : Nat) (agree : ∀ k, k<j → g k=h k) :
    HttpRequestSpec.requestLine g 0 j=HttpRequestSpec.requestLine h 0 j := by
  have methods := scan_congr isTchar g h 0 j agree
  let m := scan isTchar h 0 j
  let te := scan isTargetByte h (m+1) j
  unfold HttpRequestSpec.requestLine
  dsimp only
  rw [methods]
  change (if m=0 ∨ j≤m then _ else if g m≠32 then _ else _) =
    (if m=0 ∨ j≤m then _ else if h m≠32 then _ else _)
  by_cases bad : m=0 ∨ j≤m
  · simp only [bad,ite_true]
  · simp only [bad,ite_false]
    rw [agree m (by omega)]
    change (if h m≠32 then _ else _)= (if h m≠32 then _ else _)
    by_cases space : h m≠32
    · simp [space]
    · simp only [space,ite_false]
      have targets := scan_congr isTargetByte g h (m+1) j agree
      rw [targets]
      change (if te=m+1 ∨ j≤te then _ else if g (m+1)≠47 ∨ g te≠32 then _ else _) =
        (if te=m+1 ∨ j≤te then _ else if h (m+1)≠47 ∨ h te≠32 then _ else _)
      by_cases targetBad : te=m+1 ∨ j≤te
      · simp only [targetBad,ite_true]
      · simp only [targetBad,ite_false]
        have lower : m+1≤te := scan_ge isTargetByte h (m+1) j
        rw [agree (m+1) (by omega),agree te (by omega),version g h (te+1) j agree]
end E5R.Thermostat.HeadRequestCongr
