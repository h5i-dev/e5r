import Projects.thermostat.HttpRequestSpec
import Theories.Logic
namespace E5R.Thermostat.HeadFieldsRegs
open E5R E5R.Thermostat HttpRequestSpec

/-- Live register portion of a stable header-loop entry. Scratch registers
    and sequential stores between entries are intentionally unconstrained. -/
structure At (c : Core) (sp : Word) (i length minor : Nat) (f : Fields) : Prop where
  pc : c.pc=0x80002f58#32
  stack : c.get 2=sp
  position : c.get 24=BitVec.ofNat 32 i
  lf : c.get 16=10#32
  cr : c.get 17=13#32
  tcharMin : c.get 5=33#32
  digitMin : c.get 6=48#32
  maskWidth : c.get 7=14#32
  colon : c.get 28=58#32
  upperEnd : c.get 27=91#32
  version : c.get 8=BitVec.ofNat 32 minor
  inverse : c.get 18=BitVec.ofNat 32 (1-minor)
  count : c.get 9=BitVec.ofNat 32 f.headers.length
  te : c.get 23=(if f.te then 1#32 else 0#32)
  negLength : c.get 22=0#32-BitVec.ofNat 32 length
end E5R.Thermostat.HeadFieldsRegs
