import Projects.thermostat.HeadFieldsCRCalc
import Projects.thermostat.HeadFieldsCRBranch
import Projects.thermostat.HeadTargetMath
namespace E5R.Thermostat.HeadFieldsCRGuard
open E5R E5R.Thermostat

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (sp : Word) (i t cap : Nat)
    (hp : c.pc=0x80002f9a#32) (h24 : c.get 24=BitVec.ofNat 32 i) (h21 : c.get 21=BitVec.ofNat 32 t) (h2 : c.get 2=sp)
    (hcap : ramRead ram (sp+40#32) .w=BitVec.ofNat 32 cap) (hi : i+t<cap) (hn : cap≤2048)
    (hm : Memory.Block B sp 56) (ha : sp.toNat%4=0) :
    ∃ d, Quiet.Steps B img 4 ⟨c,ram⟩ ⟨d,ram⟩ ∧
      d.pc=(if cap≤i+t+1 then 0x800033ea#32 else 0x80002fa8#32) ∧
      d.get 26=BitVec.ofNat 32 (i+t) ∧ d.get 13=BitVec.ofNat 32 (i+t+1) ∧ d.get 10=BitVec.ofNat 32 cap ∧
      (∀ r : Reg, r≠26 → r≠13 → r≠10 → d.get r=c.get r) ∧ d.sameCsr c := by
  obtain ⟨a,calcTrace,pc,endWord,nextWord,capWord,frame,csr⟩ := HeadFieldsCRCalc.contract B c ram sp
    (BitVec.ofNat 32 i) (BitVec.ofNat 32 t) (BitVec.ofNat 32 cap) h24 h21 h2 hcap hm ha hp
  have endIndex : a.get 26=BitVec.ofNat 32 (i+t) := endWord.trans (BitVec.ofNat_add i t).symm
  have nextIndex : a.get 13=BitVec.ofNat 32 (i+t+1) := nextWord.trans (by rw [←BitVec.ofNat_add,←BitVec.ofNat_add])
  obtain ⟨d,branch,pc2,frame2,csr2⟩ := HeadFieldsCRBranch.contract B a ram (BitVec.ofNat 32 (i+t+1)) (BitVec.ofNat 32 cap)
    (decide (cap≤i+t+1)) pc nextIndex capWord (HeadTargetMath.geu (i+t+1) cap (by omega) hn)
  refine ⟨d,calcTrace.trans branch,?_,(frame2 26).trans endIndex,(frame2 13).trans nextIndex,(frame2 10).trans capWord,?_,csr2.trans csr⟩
  · by_cases full : cap≤i+t+1
    · simpa only [full,decide_true,ite_true] using pc2
    · simpa only [full,decide_false,Bool.false_eq_true,ite_false] using pc2
  · intro r h26 h13 h10;exact (frame2 r).trans (frame r h26 h13 h10)
end E5R.Thermostat.HeadFieldsCRGuard
