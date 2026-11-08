import Projects.thermostat.ResponseFieldTab
import Projects.thermostat.ResponseFieldNormal
namespace E5R.Thermostat.ResponseFieldCheck
open E5R E5R.Thermostat

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (src : Word) (v : BitVec 8)
    (hp : c.pc=0x80003eb0#32) (h29 : c.get 29=src) (h6 : c.get 6=9#32)
    (h7 : c.get 7=32#32) (h28 : c.get 28=127#32)
    (hs : ReadBytes.Byte B img ram src v) (hf : ResponseHeadSpec.fieldByte v) :
    ∃ d n, n≤4 ∧ Quiet.Steps B img n ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc=0x80003ea8#32 ∧
      d.get 31=ResponseFieldMath.word v ∧ (∀ r : Reg, r≠31 → d.get r=c.get r) ∧ d.sameCsr c := by
  by_cases h9 : v.toNat=9
  · obtain ⟨d,td,pd,d31,dr,dc⟩ := ResponseFieldTab.contract B c ram src v h29 h6 hs h9 hp
    exact ⟨d,2,by decide,td,pd,d31,dr,dc⟩
  · obtain ⟨d,td,pd,d31,dr,dc⟩ := ResponseFieldNormal.contract B c ram src v h29 h6 hs h7 h28 hf h9 hp
    exact ⟨d,4,by decide,td,pd,d31,dr,dc⟩
end E5R.Thermostat.ResponseFieldCheck
