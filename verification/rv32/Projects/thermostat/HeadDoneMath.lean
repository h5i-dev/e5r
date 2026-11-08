import Projects.thermostat.HeadFieldsView
namespace E5R.Thermostat.HeadDoneMath
open E5R E5R.Thermostat

theorem host (minor : Nat) (host : Bool) (version : minor≤1) :
    taken .eq (alu .and (alu .or (BitVec.ofNat 32 (1-minor))
      (extend .b false (BitVec.ofNat 32 (HeadFieldsView.flag host).toNat))) 1#32) 0#32=
      decide (minor=1 ∧ host=false) := by
  have casesMinor : minor=0 ∨ minor=1 := by omega
  rcases casesMinor with zero|one <;> subst minor <;> cases host <;> decide +kernel

theorem te (flag : Bool) : taken .ne (alu .and (if flag then 1#32 else 0#32) 1#32) 0#32=flag := by
  cases flag <;> decide +kernel

theorem cl (flag : Bool) : alu .and (extend .b false (BitVec.ofNat 32 (HeadFieldsView.flag flag).toNat)) 1#32=
    if flag then 1#32 else 0#32 := by cases flag <;> decide +kernel

theorem length (len : Nat) (positive : 2≤len) : BitVec.ofNat 32 (len-2)+2#32=BitVec.ofNat 32 len := by
  rw [←BitVec.ofNat_add,show len-2+2=len by omega]
end E5R.Thermostat.HeadDoneMath
