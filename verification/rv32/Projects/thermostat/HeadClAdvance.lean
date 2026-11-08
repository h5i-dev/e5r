import Projects.thermostat.HeadClMath
import Projects.thermostat.HeadClAdvanceUpdate
import Projects.thermostat.HeadClAdvanceBranch
namespace E5R.Thermostat.HeadClAdvance
open E5R E5R.Thermostat

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (buf : Word) (start k : Nat)
    (hp : c.pc=0x800031d4#32) (h10 : c.get 10=BitVec.ofNat 32 (14-k))
    (h31 : c.get 31=buf+BitVec.ofNat 32 (start+k))
    (h30 : c.get 30=BitVec.ofNat 32 (0x80005de0+k)) (hk : k<14) :
    ∃ d, Quiet.Steps B img 4 ⟨c,ram⟩ ⟨d,ram⟩ ∧
      d.pc=(if k+1<14 then 0x800031b2#32 else 0x800031dc#32) ∧
      d.get 10=BitVec.ofNat 32 (14-(k+1)) ∧
      d.get 31=buf+BitVec.ofNat 32 (start+(k+1)) ∧
      d.get 30=BitVec.ofNat 32 (0x80005de0+(k+1)) ∧
      (∀ r : Reg, r≠10 → r≠31 → r≠30 → d.get r=c.get r) ∧ d.sameCsr c := by
  obtain ⟨a,t0,p0,v10,v31,v30,f0,s0⟩ := HeadClAdvanceUpdate.contract B c ram _ _ _ h10 h31 h30 hp
  rw [HeadClMath.count_sub k hk] at v10
  obtain ⟨d,t1,p1,f1,s1⟩ := HeadClAdvanceBranch.contract B a ram _ _ p0 v10 (HeadClMath.count_test k hk)
  refine ⟨d,by simpa using t0.trans t1,?_,(f1 10).trans v10,?_,?_,?_,s1.trans s0⟩
  · by_cases more : k+1<14 <;> simpa [more] using p1
  · have off : (buf+BitVec.ofNat 32 (start+k))+1#32=buf+BitVec.ofNat 32 (start+(k+1)) := by
      rw [BitVec.add_assoc,←BitVec.ofNat_add];congr 2 <;> omega
    exact ((f1 31).trans v31).trans off
  · have off : BitVec.ofNat 32 (0x80005de0+k)+1#32=BitVec.ofNat 32 (0x80005de0+(k+1)) := by
      rw [←BitVec.ofNat_add];congr 1 <;> omega
    exact ((f1 30).trans v30).trans off
  · intro r h10 h31 h30
    exact (f1 r).trans (f0 r h10 h31 h30)
end E5R.Thermostat.HeadClAdvance
