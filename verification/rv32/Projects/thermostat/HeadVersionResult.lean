import Projects.thermostat.HttpRequestSpec
import Theories.Logic
namespace E5R.Thermostat.HeadVersionResult
open E5R E5R.Thermostat

/-- A cutpoint result of actual version parsing, before header initialization
    or request-line rejection stores. No `HeadR.done` result is asserted here. -/
def At (d : Core) (v : Nat) (limits dst : Word) : Prop :=
  if v<2 then d.pc=0x80002f0e#32 ∧ d.get 8=BitVec.ofNat 32 v ∧ d.get 18=BitVec.ofNat 32 (1-v) ∧ d.get 20=limits
  else (d.pc=0x80002efa#32 ∨ d.pc=0x80002efc#32) ∧ d.get 15=(if v=3 then 400#32 else 505#32) ∧
    (d.pc=0x80002efc#32 → d.get 10=dst)
end E5R.Thermostat.HeadVersionResult
