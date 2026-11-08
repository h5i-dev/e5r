import Projects.thermostat.HttpRequestSpec
namespace E5R.Thermostat.HeadLineScanSpec
open E5R E5R.Thermostat HttpRequestSpec

def bytes (ram : Word → BitVec 8) (buf : Word) (i : Nat) : Nat := (ram (buf+BitVec.ofNat 32 i)).toNat

def pc (g : Nat → Nat) (k n : Nat) : Word :=
  if k<n then if g k=10 then 0x80002d5a#32 else 0x80002ca8#32 else 0x80002ce6#32

theorem stop (g : Nat → Nat) (j n : Nat) (hj : j<n) (he : g j=10 ∨ g j=13) : lineEnd g j n=j := by
  unfold lineEnd
  rw [scan]
  rcases he with h|h <;> simp [hj,notEol,h]

theorem advance (g : Nat → Nat) (j n : Nat) (hj : j<n) (h10 : g j≠10) (h13 : g j≠13) :
    lineEnd g j n=lineEnd g (j+1) n := by
  unfold lineEnd
  rw [scan]
  simp only [hj,ite_true]
  have hn : notEol (g j)=true := by simp [notEol,h10,h13]
  rw [hn]
  rfl

theorem end_at (g : Nat → Nat) (n : Nat) : lineEnd g n n=n := by
  unfold lineEnd
  rw [scan]
  simp
theorem scan_pred (p : Nat → Bool) (g : Nat → Nat) (j n : Nat) (bound : scan p g j n<n) :
    p (g (scan p g j n))=false := by
  by_cases hj : j<n
  · cases hp : p (g j) with
    | false =>
      rw [scan]
      simp only [hj,hp,ite_true,Bool.false_eq_true,ite_false]
    | true =>
      have eq : scan p g j n=scan p g (j+1) n := by rw [scan];simp only [hj,hp,ite_true]
      rw [eq] at bound ⊢
      exact scan_pred p g (j+1) n bound
  · have eq : scan p g j n=j := by rw [scan];simp only [hj,ite_false]
    rw [eq] at bound
    omega
termination_by n-j
 decreasing_by omega

theorem eol (g : Nat → Nat) (j n : Nat) (bound : lineEnd g j n<n) :
    g (lineEnd g j n)=10 ∨ g (lineEnd g j n)=13 := by
  have hp := scan_pred notEol g j n bound
  change notEol (g (lineEnd g j n))=false at hp
  by_cases h10 : g (lineEnd g j n)=10
  · exact Or.inl h10
  · by_cases h13 : g (lineEnd g j n)=13
    · exact Or.inr h13
    · have ht : notEol (g (lineEnd g j n))=true := by simp [notEol,h10,h13]
      rw [ht] at hp
      contradiction
theorem scan_congr (p : Nat → Bool) (g h : Nat → Nat) (j n : Nat)
    (agree : ∀ k, k<n → g k=h k) : scan p g j n=scan p h j n := by
  conv =>
    lhs
    rw [scan]
  conv =>
    rhs
    rw [scan]
  by_cases hj : j<n
  · simp only [hj,ite_true,agree j hj]
    cases hp : p (h j) with
    | false => rfl
    | true =>
      simp only [ite_true]
      exact scan_congr p g h (j+1) n agree
  · simp only [hj,ite_false]
termination_by n-j
 decreasing_by omega

theorem line_congr (g h : Nat → Nat) (j n : Nat) (agree : ∀ k, k<n → g k=h k) :
    lineEnd g j n=lineEnd h j n := scan_congr notEol g h j n agree

theorem term_congr (g h : Nat → Nat) (j n : Nat) (agree : ∀ k, k<n → g k=h k) :
    lineTerm g j n=lineTerm h j n := by
  by_cases hj : j<n
  · by_cases he : n≤j+1
    · simp only [lineTerm,show ¬n≤j by omega,ite_false,agree j hj,he,ite_true]
    · have next : j+1<n := by omega
      simp only [lineTerm,show ¬n≤j by omega,ite_false,agree j hj,agree (j+1) next,he]
  · have bound : n≤j := by omega
    simp only [lineTerm,bound,ite_true]
theorem scan_all (p : Nat → Bool) (g : Nat → Nat) (j n : Nat) (hj : j≤n)
    (good : ∀ k, j≤k → k<n → p (g k)=true) : scan p g j n=n := by
  by_cases inside : j<n
  · rw [scan]
    simp only [inside,ite_true,good j (by omega) inside]
    exact scan_all p g (j+1) n (by omega) (fun k lo hi => good k (by omega) hi)
  · have eq : j=n := by omega
    subst j
    rw [scan]
    simp
termination_by n-j
 decreasing_by omega
end E5R.Thermostat.HeadLineScanSpec
