-- Generated stronger trace proofs; Lean checks every decoded-instruction side condition.
import Projects.thermostat.CopyThreeSetup
import Projects.thermostat.QuietDet
import Projects.thermostat.RamRunQuiet
import Projects.thermostat.CopyThreeCaseQuiet
import Projects.thermostat.CopyUnalignedEntryQuiet
open E5R E5R.Thermostat
namespace E5R.Thermostat.CopyThreeSetup
theorem contract_quiet (c : Core) (ram : Word → BitVec 8) (sp dst : Word)
    (hp : c.pc=0x80005182#32) (hsp : c.get 2=sp+16#32) (h10 : c.get 10=dst)
    (h11 : c.get 11=0x80005bc7#32) (h12 : c.get 12=25#32)
    (had : dst.toNat%4=0) (hm : Memory.Block UartPlatform.board sp 16) (ha : sp.toNat%4=0)
    (hw : dst.toNat+24<2^32) :
    ∃ d, Quiet.Steps UartPlatform.board img 35 ⟨c,ram⟩ ⟨d,CopyInitData.byteRam ram sp⟩ ∧
      d.pc=0x8000525e#32 ∧ d.get 2=sp ∧ d.get 10=dst ∧ d.get 11=0x80005bc7#32 ∧ d.get 12=25#32 ∧
      d.get 13=dst+24#32 ∧ d.get 14=dst ∧ d.get 15=24#32 ∧ d.get 5=3#32 ∧
      d.get 6=0x80005bc4#32 ∧ d.get 7=8#32 ∧ d.get 16=24#32 ∧ d.get 17=0x7b000000#32 ∧
      (∀ r : Reg, CopyRegs.Preserved r → d.get r=c.get r) ∧ d.sameCsr c := by
  obtain ⟨a,ta,pa,a2,a10,a11,a12,a13,a14,a15,a5,a16,a17,a6,a7,ar,ac⟩ := E5R.Thermostat.CopyUnalignedEntry.contract_quiet UartPlatform.board c ram sp 0x80005bc7#32 dst 25 24 3
    hp hsp h10 h11 h12 (by decide) (by decide) had hm ha (by decide) (by decide) (by decide) (by decide)
  have hlt : taken .ltu (dst+4#32) (dst+24#32)=true := by
    change decide ((dst+4#32).toNat < (dst+24#32).toNat)=true
    rw [WordZero.add_nat dst 4 (by omega),WordZero.add_nat dst 24 hw]
    simp only [decide_eq_true_eq];omega
  obtain ⟨d,td,pd,d6,d7,d16,d17,dr,dc⟩ := E5R.Thermostat.CopyThreeCase.contract_quiet UartPlatform.board a ram sp dst (dst+24#32)
    pa a2 (by simpa using a7) (by simpa using a17) a11 (by simpa using a6) a14 a13 a5 hm ha CopyInitData.byte_outside hlt
  refine ⟨d,by simpa using ta.trans td,pd,?_,?_,?_,?_,?_,?_,?_,?_,d6,d7,d16,d17,?_,dc.trans ac⟩
  · exact (dr 2 (by decide) (by decide) (by decide) (by decide)).trans a2
  · exact (dr 10 (by decide) (by decide) (by decide) (by decide)).trans a10
  · exact (dr 11 (by decide) (by decide) (by decide) (by decide)).trans a11
  · exact (dr 12 (by decide) (by decide) (by decide) (by decide)).trans a12
  · exact (dr 13 (by decide) (by decide) (by decide) (by decide)).trans a13
  · exact (dr 14 (by decide) (by decide) (by decide) (by decide)).trans a14
  · exact (dr 15 (by decide) (by decide) (by decide) (by decide)).trans a15
  · exact (dr 5 (by decide) (by decide) (by decide) (by decide)).trans a5
  · intro reg hr
    have ne (q : Reg) (hq : q.val<18) (h1 : q≠1) (h8 : q≠8) (h9 : q≠9) := CopyRegs.ne_low reg q hr hq h1 h8 h9
    exact (dr reg (ne 6 (by decide) (by decide) (by decide) (by decide)) (ne 7 (by decide) (by decide) (by decide) (by decide))
      (ne 16 (by decide) (by decide) (by decide) (by decide)) (ne 17 (by decide) (by decide) (by decide) (by decide))).trans (ar reg hr)

end E5R.Thermostat.CopyThreeSetup
