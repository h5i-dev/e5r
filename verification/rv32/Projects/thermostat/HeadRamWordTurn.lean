import Projects.thermostat.HeadRamWordUpdate
import Projects.thermostat.HeadRamWordBranch
namespace E5R.Thermostat.HeadRamWordTurn
open E5R E5R.Thermostat

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (src dst finish value : Word) (again : Bool)
    (hp : c.pc=0x80005212#32) (h16 : c.get 16=src) (h14 : c.get 14=dst) (h13 : c.get 13=finish)
    (has : src.toNat%4=0) (had : dst.toNat%4=0) (source : B.inRam src 4=true)
    (hv : ramRead ram src .w=value) (destination : B.inRam dst 4=true)
    (ht : taken .ltu (dst+4#32) finish=again) :
    ∃ d, Quiet.Steps B img 5 ⟨c,ram⟩ ⟨d,ramWrite ram dst value .w⟩ ∧
      d.pc=(if again then 0x80005212#32 else 0x80005222#32) ∧ d.get 14=dst+4#32 ∧ d.get 16=src+4#32 ∧
      (∀ r : Reg, r≠14 → r≠16 → r≠17 → d.get r=c.get r) ∧ d.sameCsr c := by
  obtain ⟨a,ta,apc,a17,a14,a16,ar,ac⟩ := HeadRamWordUpdate.contract B c ram src dst value h16 h14 hv has had source destination hp
  simp only [HeadRamWordUpdate.memory,BitVec.add_zero] at ta
  have a13 := ar 13 (by decide) (by decide) (by decide)
  obtain ⟨d,td,dpc,dr,dc⟩ := HeadRamWordBranch.contract B a (ramWrite ram dst value .w) _ finish again apc a14 (a13.trans h13) ht
  refine ⟨d,?_,dpc,(dr 14).trans a14,(dr 16).trans a16,?_,dc.trans ac⟩
  · simpa only [HeadRamWordUpdate.memory,BitVec.add_zero] using ta.trans td
  · intro r h14 h16 h17
    exact (dr r).trans (ar r h17 h14 h16)
end E5R.Thermostat.HeadRamWordTurn
