import Projects.thermostat.HeadActionSpec
namespace E5R.Thermostat.HeadActionCongr
open E5R E5R.Thermostat HttpRequestSpec

theorem eqFrom_congr (g h : Nat → Nat) (s : Nat) (lit : List Nat) (q cap : Nat)
    (bound : s+lit.length≤cap) (agree : ∀ k, k<cap → g k=h k) :
    eqFrom g s lit q=eqFrom h s lit q := by
  conv => lhs;rw [eqFrom]
  conv => rhs;rw [eqFrom]
  by_cases inside : q<lit.length
  · rw [ite_eq_left inside,ite_eq_left inside,agree (s+q) (by omega)]
    by_cases same : lower (h (s+q))≠lit.getD q 0
    · rw [ite_eq_left same,ite_eq_left same]
    · rw [ite_eq_right same,ite_eq_right same]
      exact eqFrom_congr g h s lit (q+1) cap bound agree
  · rw [ite_eq_right inside,ite_eq_right inside]
termination_by lit.length-q
 decreasing_by omega

theorem eqCi_congr (g h : Nat → Nat) (s e cap : Nat) (upper : e≤cap)
    (agree : ∀ k, k<cap → g k=h k) (lit : List Nat) : eqCi g s e lit=eqCi h s e lit := by
  unfold eqCi
  by_cases invalid : e<s ∨ e-s≠lit.length
  · rw [ite_eq_left invalid,ite_eq_left invalid]
  · rw [ite_eq_right invalid,ite_eq_right invalid]
    exact eqFrom_congr g h s lit 0 cap (by omega) agree

theorem classify_congr (g h : Nat → Nat) (s e cap : Nat) (upper : e≤cap)
    (agree : ∀ k, k<cap → g k=h k) : classify g s e=classify h s e := by
  unfold classify
  rw [eqCi_congr g h s e cap upper agree litHost,eqCi_congr g h s e cap upper agree litContentLength,
    eqCi_congr g h s e cap upper agree litTransferEncoding]

theorem clLoop_congr (g h : Nat → Nat) (e max acc p cap : Nat) (bound : e≤cap)
    (agree : ∀ k, k<cap → g k=h k) : clLoop g e max acc p=clLoop h e max acc p := by
  conv => lhs;rw [clLoop]
  conv => rhs;rw [clLoop]
  by_cases inside : p<e
  · rw [ite_eq_left inside,ite_eq_left inside,agree p (by omega)]
    by_cases invalid : h p<48 ∨ 57<h p
    · rw [ite_eq_left invalid,ite_eq_left invalid]
    · rw [ite_eq_right invalid,ite_eq_right invalid]
      by_cases overflow : max<acc*10+(h p-48)
      · rw [ite_eq_left overflow,ite_eq_left overflow]
      · rw [ite_eq_right overflow,ite_eq_right overflow]
        exact clLoop_congr g h e max (acc*10+(h p-48)) (p+1) cap bound agree
  · rw [ite_eq_right inside,ite_eq_right inside]
termination_by e-p
 decreasing_by omega

theorem contentLength_congr (g h : Nat → Nat) (s e max cap : Nat) (bound : e≤cap)
    (agree : ∀ k, k<cap → g k=h k) : contentLength g s e max=contentLength h s e max := by
  unfold contentLength
  by_cases empty : e≤s
  · rw [ite_eq_left empty,ite_eq_left empty]
  · rw [ite_eq_right empty,ite_eq_right empty]
    exact clLoop_congr g h e max 0 s cap bound agree

theorem action_congr (g h : Nat → Nat) (f : Fields) (ns ne vs ve le minor max cap : Nat)
    (name : ne≤cap) (value : ve≤cap) (agree : ∀ k, k<cap → g k=h k) :
    HeadActionSpec.action g f ns ne vs ve le minor max=HeadActionSpec.action h f ns ne vs ve le minor max := by
  unfold HeadActionSpec.action
  rw [classify_congr g h ns ne cap name agree,contentLength_congr g h vs ve max cap value agree,
    eqCi_congr g h vs ve cap value agree litChunked]
end E5R.Thermostat.HeadActionCongr
