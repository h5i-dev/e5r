import Projects.thermostat.HeadLineScanSpec
namespace E5R.Thermostat.HeadFieldCongr
open E5R E5R.Thermostat HttpRequestSpec HeadLineScanSpec

theorem all_congr (p : Nat → Bool) (g h : Nat → Nat) (s e : Nat) (agree : ∀ k, k<e → g k=h k) :
    allIn p g s e=allIn p h s e := by
  conv => lhs;rw [allIn]
  conv => rhs;rw [allIn]
  by_cases inside : s<e
  · rw [ite_eq_left inside,ite_eq_left inside,agree s inside]
    cases token : p (h s) with
    | false => simp only [Bool.false_eq_true,ite_false]
    | true => simp only [ite_true];exact all_congr p g h (s+1) e agree
  · rw [ite_eq_right inside,ite_eq_right inside]
termination_by e-s
 decreasing_by omega

theorem trim_congr (g h : Nat → Nat) (s p cap : Nat) (bound : p≤cap) (agree : ∀ k, k<cap → g k=h k) :
    trimEnd g s p=trimEnd h s p := by
  conv => lhs;rw [trimEnd]
  conv => rhs;rw [trimEnd]
  by_cases inside : s<p
  · rw [ite_eq_left inside,ite_eq_left inside,agree (p-1) (by omega)]
    cases token : isOws (h (p-1)) with
    | false => simp only [Bool.false_eq_true,ite_false]
    | true => simp only [ite_true];exact trim_congr g h s (p-1) cap (by omega) agree
  · rw [ite_eq_right inside,ite_eq_right inside]
termination_by p
 decreasing_by omega

/-- Header parsing depends only on bytes below its explicit end bound. -/
theorem header_congr (g h : Nat → Nat) (s e : Nat) (agree : ∀ k, k<e → g k=h k) :
    headerLine g s e=headerLine h s e := by
  have names := scan_congr isTchar g h s e agree
  unfold headerLine
  rw [names]
  by_cases early : scan isTchar h s e=s ∨ e≤scan isTchar h s e
  · simp only [early,ite_true]
  · simp only [early,ite_false]
    have inside : scan isTchar h s e<e := by omega
    rw [agree _ inside,all_congr isFieldByte g h _ e agree]
    by_cases colon : h (scan isTchar h s e)≠58
    · simp [colon]
    · simp only [colon,ite_false]
      cases valid : allIn isFieldByte h (scan isTchar h s e+1) e with
      | false => rfl
      | true =>
        simp only [Bool.not_true,Bool.false_eq_true,ite_false]
        rw [scan_congr isOws g h _ e agree,trim_congr g h _ e e (by omega) agree]
end E5R.Thermostat.HeadFieldCongr
