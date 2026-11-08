import Projects.thermostat.HeadLineScanSpec
namespace E5R.Thermostat.HeadMethodSpec
open E5R E5R.Thermostat HttpRequestSpec

def pc (g : Nat → Nat) (m j : Nat) : Word :=
  if j≤m then 0x80002efc#32 else if g m<33 then 0x80002da2#32 else 0x80002efc#32

theorem stop (g : Nat → Nat) (i j : Nat) (hi : i<j) (hc : isTchar (g i)=false) : scan isTchar g i j=i := by
  rw [scan]
  simp only [hi,hc,ite_true,Bool.false_eq_true,ite_false]

theorem advance (g : Nat → Nat) (i j : Nat) (hi : i<j) (hc : isTchar (g i)=true) :
    scan isTchar g i j=scan isTchar g (i+1) j := by
  rw [scan]
  simp only [hi,hc,ite_true]

theorem end_at (g : Nat → Nat) (j : Nat) : scan isTchar g j j=j := by
  rw [scan]
  simp

theorem token_not_small (b : Nat) (hc : isTchar b=true) : ¬b<33 := by
  intro small
  unfold isTchar at hc
  simp only [small,ite_true] at hc
  contradiction
end E5R.Thermostat.HeadMethodSpec
