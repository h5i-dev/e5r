import Projects.thermostat.HeadClNumberAdvanceRaw
import Projects.thermostat.HeadClNumberAdvanceBranch
import Projects.thermostat.HeadTargetMath
namespace E5R.Thermostat.HeadClNumberAdvance
open E5R E5R.Thermostat

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (buf : Word) (pos finish length : Nat)
    (hp : c.pc=0x80003256#32) (h11 : c.get 11=BitVec.ofNat 32 (finish-pos))
    (h10 : c.get 10=buf+BitVec.ofNat 32 pos) (h31 : c.get 31=BitVec.ofNat 32 (length-pos))
    (inside : pos<finish) (upper : finish≤length) (bound : length≤2048) :
    ∃ d, Quiet.Steps B img 4 ⟨c,ram⟩ ⟨d,ram⟩ ∧
      d.pc=(if pos+1<finish then 0x80003206#32 else 0x8000325e#32) ∧
      d.get 11=BitVec.ofNat 32 (finish-(pos+1)) ∧ d.get 10=buf+BitVec.ofNat 32 (pos+1) ∧
      d.get 31=BitVec.ofNat 32 (length-(pos+1)) ∧
      (∀ r : Reg, r≠11 → r≠10 → r≠31 → d.get r=c.get r) ∧ d.sameCsr c := by
  obtain ⟨a,step,pc,v11,v10,v31,frame,csr⟩ := HeadClNumberAdvanceRaw.contract B c ram _ _ _ h11 h10 h31 hp
  rw [HeadTargetMath.remaining_next pos finish inside] at v11
  rw [HeadTargetMath.remaining_next pos length (by omega)] at v31
  have v10' : a.get 10=buf+BitVec.ofNat 32 (pos+1) := by
    rw [v10,BitVec.add_assoc,←BitVec.ofNat_add]
  obtain ⟨d,branch,pc2,frame2,csr2⟩ := HeadClNumberAdvanceBranch.contract B a ram _ (0 : Word) _ pc v11 (Core.get_zero a)
    (HeadTargetMath.again pos finish inside (by omega))
  refine ⟨d,by simpa using step.trans branch,?_,(frame2 11).trans v11,(frame2 10).trans v10',(frame2 31).trans v31,?_,csr2.trans csr⟩
  · by_cases more : pos+1<finish <;> simpa [more] using pc2
  · intro r h11 h10 h31;exact (frame2 r).trans (frame r h11 h10 h31)
end E5R.Thermostat.HeadClNumberAdvance
