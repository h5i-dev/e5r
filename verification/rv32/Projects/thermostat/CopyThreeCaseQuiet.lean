-- Generated stronger trace proofs; Lean checks every decoded-instruction side condition.
import Projects.thermostat.CopyThreeCase
import Projects.thermostat.QuietDet
import Projects.thermostat.RamRunQuiet
import Projects.thermostat.CopyThreeAfterQuiet
import Projects.thermostat.CopyThreeBeforeQuiet
import Projects.thermostat.CopyThreeStoreQuiet
set_option maxHeartbeats 1000000
open E5R E5R.Thermostat
namespace E5R.Thermostat.CopyThreeCase
theorem contract_quiet (B : Board) (c : Core) (ram : Word → BitVec 8) (sp dst finish : Word)
    (hp : c.pc=0x800051e0#32) (h2 : c.get 2=sp) (h7 : c.get 7=1#32)
    (h17 : c.get 17=1#32) (h11 : c.get 11=0x80005bc7#32)
    (h6 : c.get 6=sp+15#32) (h14 : c.get 14=dst) (h13 : c.get 13=finish) (h5 : c.get 5=3#32)
    (hm : Memory.Block B sp 16) (ha : sp.toNat%4=0) (hro : B.inRam 0x80005bc7#32 1=false)
    (hlt : taken .ltu (dst+4#32) finish=true) :
    ∃ d, Quiet.Steps B img 13 ⟨c,CopyUnalignedScratch.memory ram sp⟩ ⟨d,CopyInitData.byteRam ram sp⟩ ∧
      d.pc=0x8000525e#32 ∧ d.get 6=0x80005bc4#32 ∧ d.get 7=8#32 ∧
      d.get 16=24#32 ∧ d.get 17=0x7b000000#32 ∧
      (∀ r : Reg, r≠6 → r≠7 → r≠16 → r≠17 → d.get r=c.get r) ∧ d.sameCsr c := by
  obtain ⟨a,sa,pa,a16,ar,ac⟩ := E5R.Thermostat.CopyThreeBefore.contract_quiet B c (CopyUnalignedScratch.memory ram sp) h7 h11 hro hp
  have sb := E5R.Thermostat.CopyThreeStore.contract_quiet B a ram sp pa (by rw [ar 6 (by decide),h6]) a16 hm
  obtain ⟨d,sd,pd,d16,d17,d7,d6,dr,dc⟩ := E5R.Thermostat.CopyThreeAfter.contract_quiet B (a.goto 0x8000522c#32) (CopyInitData.byteRam ram sp) sp dst finish
    (by exact (ar 2 (by decide)).trans h2)
    (by exact (ar 17 (by decide)).trans h17)
    (by exact (ar 5 (by decide)).trans h5)
    (by exact (ar 14 (by decide)).trans h14)
    (by exact (ar 13 (by decide)).trans h13)
    (by exact (ar 11 (by decide)).trans h11) hm ha (CopyInitData.byte_word ram sp) hlt rfl
  refine ⟨d,by simpa using (sa.trans (.single sb)).trans sd,pd,d6,d7,d16,d17,?_,dc.trans ac⟩
  intro r h6 h7 h16 h17
  exact (dr r h16 h17 h7 h6).trans (ar r h16)

end E5R.Thermostat.CopyThreeCase
