import Projects.thermostat.HttpRequestSpec
import Projects.thermostat.Memory
namespace E5R.Thermostat.HeadHeaderLineView
open E5R E5R.Thermostat HttpRequestSpec

/-- Actual internal result of header_line, before classify/add_header.
    The successful result is registers and the name-end scratch word. -/
def At (c : Core) (ram : Word → BitVec 8) (sp buf : Word) (start finish : Nat) : HdrLine → Prop
  | .bad s => c.pc=0x8000342c#32 ∧ c.get 1=BitVec.ofNat 32 s
  | .ok k vs ve => c.pc=0x800030fa#32 ∧ ramRead ram (sp+4#32) .w=BitVec.ofNat 32 k ∧
      c.get 14=BitVec.ofNat 32 (k-start) ∧ c.get 15=BitVec.ofNat 32 vs ∧ c.get 25=BitVec.ofNat 32 ve ∧
      c.get 20=buf+BitVec.ofNat 32 start ∧ start<k ∧ k<vs ∧ vs≤ve ∧ ve≤finish
end E5R.Thermostat.HeadHeaderLineView
