-- Generated stronger trace proofs; Lean checks every decoded-instruction side condition.
import Projects.thermostat.CopyTwoCase
import Projects.thermostat.QuietDet
import Projects.thermostat.RamRunQuiet
import Projects.thermostat.CopyTwoAfterQuiet
import Projects.thermostat.CopyTwoBeforeQuiet
import Projects.thermostat.CopyTwoStoreQuiet
set_option maxHeartbeats 1000000
open E5R E5R.Thermostat
namespace E5R.Thermostat.CopyTwoCase
theorem contract_quiet (B : Board) (c : Core) (ram : Word → BitVec 8) (sp dst finish : Word)
    (hp : c.pc=0x800051e0#32) (h2 : c.get 2=sp) (h7 : c.get 7=0#32)
    (h17 : c.get 17=2#32) (h11 : c.get 11=0x80005ba6#32) (h16 : c.get 16=0#32)
    (h6 : c.get 6=sp+14#32) (h14 : c.get 14=dst) (h13 : c.get 13=finish) (h5 : c.get 5=2#32)
    (hm : Memory.Block B sp 16) (ha : sp.toNat%4=0) (hro : B.inRam 0x80005ba6#32 2=false)
    (hlt : taken .ltu (dst+4#32) finish=true) :
    ∃ d, Quiet.Steps B img 14 ⟨c,CopyUnalignedScratch.memory ram sp⟩ ⟨d,CopyInitData.halfRam ram sp⟩ ∧
      d.pc=0x8000525e#32 ∧ d.get 6=0x80005ba4#32 ∧ d.get 7=16#32 ∧
      d.get 16=16#32 ∧ d.get 17=0x227b0000#32 ∧
      (∀ r : Reg, r≠6 → r≠7 → r≠16 → r≠17 → d.get r=c.get r) ∧ d.sameCsr c := by
  obtain ⟨a,sa,pa,a17,a16,ar,ac⟩ := E5R.Thermostat.CopyTwoBefore.contract_quiet B c (CopyUnalignedScratch.memory ram sp) sp h7 h17 h11 h16 h6 hro hp
  obtain ⟨b,sb,pb,b17,br,bc⟩ := E5R.Thermostat.CopyTwoStore.contract_quiet B a ram sp pa
    (by rw [ar 2 (by decide) (by decide),h2]) a16 a17 hm ha
  obtain ⟨d,sd,pd,d7,d16,d6,dr,dc⟩ := E5R.Thermostat.CopyTwoAfter.contract_quiet B b (CopyInitData.halfRam ram sp) dst finish
    (by rw [br 14 (by decide),ar 14 (by decide) (by decide),h14])
    (by rw [br 13 (by decide),ar 13 (by decide) (by decide),h13])
    (by rw [br 5 (by decide),ar 5 (by decide) (by decide),h5])
    (by rw [br 11 (by decide),ar 11 (by decide) (by decide),h11]) hlt pb
  refine ⟨d,by simpa using (sa.trans sb).trans sd,pd,d6,d7,d16,?_,?_,dc.trans (bc.trans ac)⟩
  · rw [dr 17 (by decide) (by decide) (by decide),b17]
  · intro r h6 h7 h16 h17
    rw [dr r h7 h16 h6,br r h17,ar r h17 h16]

end E5R.Thermostat.CopyTwoCase
