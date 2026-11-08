import Projects.thermostat.HeadLineScanSpec
namespace E5R.Thermostat.HeadTargetSpec
open E5R E5R.Thermostat HttpRequestSpec

def pc (endIndex j : Nat) : Word :=
  if endIndex<j then 0x80002dfe#32 else 0x80002efc#32

theorem stop (g : Nat → Nat) (i j : Nat) (hi : i<j) (hc : isTargetByte (g i)=false) : scan isTargetByte g i j=i := by
  rw [scan]
  simp only [hi,hc,ite_true,Bool.false_eq_true,ite_false]

theorem advance (g : Nat → Nat) (i j : Nat) (hi : i<j) (hc : isTargetByte (g i)=true) :
    scan isTargetByte g i j=scan isTargetByte g (i+1) j := by
  rw [scan]
  simp only [hi,hc,ite_true]

theorem end_at (g : Nat → Nat) (j : Nat) : scan isTargetByte g j j=j := by
  rw [scan]
  simp

end E5R.Thermostat.HeadTargetSpec
