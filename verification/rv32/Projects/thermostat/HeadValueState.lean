import Projects.thermostat.Memory
namespace E5R.Thermostat.HeadValueState
open E5R E5R.Thermostat
structure At (c : Core) (buf : Word) (pos finish length : Nat) : Prop where
  ptr : c.get 10=buf+BitVec.ofNat 32 pos
  remaining : c.get 13=BitVec.ofNat 32 (finish-pos)
  rawRemaining : c.get 31=BitVec.ofNat 32 (length-pos)
end E5R.Thermostat.HeadValueState
