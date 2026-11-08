import Projects.thermostat.HeadTeMath
import Projects.thermostat.HeadTeAdvanceUpdate
import Projects.thermostat.HeadTeAdvanceBranch
namespace E5R.Thermostat.HeadTeAdvance
open E5R E5R.Thermostat

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (buf : Word) (start k : Nat)
    (hp : c.pc=0x800032a6#32) (h10 : c.get 10=BitVec.ofNat 32 (17-k))
    (h20 : c.get 20=buf+BitVec.ofNat 32 (start+k))
    (h13 : c.get 13=BitVec.ofNat 32 (0x80005dee+k)) (hk : k<17) :
    ∃ d, Quiet.Steps B img 4 ⟨c,ram⟩ ⟨d,ram⟩ ∧
      d.pc=(if k+1<17 then 0x80003284#32 else 0x800032ae#32) ∧
      d.get 10=BitVec.ofNat 32 (17-(k+1)) ∧
      d.get 20=buf+BitVec.ofNat 32 (start+(k+1)) ∧
      d.get 13=BitVec.ofNat 32 (0x80005dee+(k+1)) ∧
      (∀ r : Reg, r≠10 → r≠20 → r≠13 → d.get r=c.get r) ∧ d.sameCsr c := by
  obtain ⟨a,t0,p0,v10,v20,v13,f0,s0⟩ := HeadTeAdvanceUpdate.contract B c ram _ _ _ h10 h20 h13 hp
  rw [HeadTeMath.count_sub k hk] at v10
  obtain ⟨d,t1,p1,f1,s1⟩ := HeadTeAdvanceBranch.contract B a ram _ _ p0 v10 (HeadTeMath.count_test k hk)
  refine ⟨d,by simpa using t0.trans t1,?_,(f1 10).trans v10,?_,?_,?_,s1.trans s0⟩
  · by_cases more : k+1<17 <;> simpa [more] using p1
  · have off : (buf+BitVec.ofNat 32 (start+k))+1#32=buf+BitVec.ofNat 32 (start+(k+1)) := by
      rw [BitVec.add_assoc,←BitVec.ofNat_add];congr 2 <;> omega
    exact ((f1 20).trans v20).trans off
  · have off : BitVec.ofNat 32 (0x80005dee+k)+1#32=BitVec.ofNat 32 (0x80005dee+(k+1)) := by
      rw [←BitVec.ofNat_add];congr 1 <;> omega
    exact ((f1 13).trans v13).trans off
  · intro r h10 h20 h13
    exact (f1 r).trans (f0 r h10 h20 h13)
end E5R.Thermostat.HeadTeAdvance
