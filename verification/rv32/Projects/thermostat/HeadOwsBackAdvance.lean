import Projects.thermostat.HeadOwsBackUpdate
import Projects.thermostat.HeadOwsBackBranch
import Projects.thermostat.HeadTargetMath
namespace E5R.Thermostat.HeadOwsBackAdvance
open E5R E5R.Thermostat

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (start pos : Nat)
    (hp : c.pc=0x800030ca#32) (h15 : c.get 15=BitVec.ofNat 32 start) (h10 : c.get 10=BitVec.ofNat 32 (pos-1))
    (hi : start<pos) (hn : pos≤2048) :
    ∃ d, Quiet.Steps B img 2 ⟨c,ram⟩ ⟨d,ram⟩ ∧
      d.pc=(if start=pos-1 then 0x800030f8#32 else 0x800030d0#32) ∧ d.get 25=BitVec.ofNat 32 (pos-1) ∧
      (∀ r : Reg, r≠25 → d.get r=c.get r) ∧ d.sameCsr c := by
  obtain ⟨a,update,pc,index,frame,csr⟩ := HeadOwsBackUpdate.contract B c ram (BitVec.ofNat 32 (pos-1)) h10 hp
  have test : taken .geu (BitVec.ofNat 32 start) (BitVec.ofNat 32 (pos-1))=decide (start=pos-1) := by
    simpa only [show (pos-1≤start) ↔ (start=pos-1) by omega] using HeadTargetMath.geu start (pos-1) (by omega) (by omega)
  obtain ⟨d,branch,pc2,frame2,csr2⟩ := HeadOwsBackBranch.contract B a ram (BitVec.ofNat 32 start) (BitVec.ofNat 32 (pos-1)) (decide (start=pos-1)) pc
    ((frame 15 (by decide)).trans h15) ((frame 10 (by decide)).trans h10) test
  refine ⟨d,update.trans branch,?_,(frame2 25).trans index,fun r h25 => (frame2 r).trans (frame r h25),csr2.trans csr⟩
  simpa only [decide_eq_true_eq] using pc2
end E5R.Thermostat.HeadOwsBackAdvance
