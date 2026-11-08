import Projects.thermostat.HeadTeStatus
import Projects.thermostat.HeadTeSpanBranch
import Projects.thermostat.HeadTeWidthRaw
import Projects.thermostat.HeadTeValueWidthBranch
import Projects.thermostat.HeadTeRuleMath
namespace E5R.Thermostat.HeadTeValueWidth
open E5R E5R.Thermostat

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (ns vs le : Nat)
    (hp : c.pc=0x800032c8#32) (h24 : c.get 24=BitVec.ofNat 32 ns) (h15 : c.get 15=BitVec.ofNat 32 vs)
    (h26 : c.get 26=BitVec.ofNat 32 le) (h21 : c.get 21=BitVec.ofNat 32 (le-ns))
    (name : ns≤le) (value : vs≤le) (bound : le≤2048) :
    ∃ d, Quiet.Steps B img 6 ⟨c,ram⟩ ⟨d,ram⟩ ∧
      d.pc=(if le-vs=7 then 0x800032dc#32 else 0x8000342c#32) ∧ d.get 1=501#32 ∧
      (∀ r : Reg, r≠1 → r≠10 → d.get r=c.get r) ∧ d.sameCsr c := by
  obtain ⟨a,t0,p0,v1,f0,s0⟩ := HeadTeStatus.contract B c ram hp
  have test : taken .ltu (BitVec.ofNat 32 le) (BitVec.ofNat 32 vs)=false := by
    change decide ((BitVec.ofNat 32 le).toNat<(BitVec.ofNat 32 vs).toNat)=false
    simp only [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega : le<2^32),Nat.mod_eq_of_lt (by omega : vs<2^32)]
    simp only [show ¬le<vs by omega,decide_false]
  obtain ⟨b,t1,p1,f1,s1⟩ := HeadTeSpanBranch.contract B a ram _ _ false p0
    ((f0 26 (by decide)).trans h26) ((f0 15 (by decide)).trans h15) test
  have p1' : b.pc=0x800032d0#32 := by simpa using p1
  have source (r : Reg) (hne : r≠1) : b.get r=c.get r := (f1 r).trans (f0 r hne)
  obtain ⟨e,t2,p2,v10,fe,se⟩ := HeadTeWidthRaw.contract B b ram _ _ _
    ((source 24 (by decide)).trans h24) ((source 15 (by decide)).trans h15) ((source 21 (by decide)).trans h21) p1'
  rw [HeadTeRuleMath.span ns vs le name value bound] at v10
  obtain ⟨d,t3,p3,fd,sd⟩ := HeadTeValueWidthBranch.contract B e ram _ (0 : Word) _ p2 v10 (Core.get_zero e)
    (HeadTeRuleMath.width_test (le-vs) (by omega))
  refine ⟨d,by simpa using (t0.trans t1).trans (t2.trans t3),?_,?_,?_,sd.trans (se.trans (s1.trans s0))⟩
  · by_cases same : le-vs=7 <;> simpa [same] using p3
  · exact (fd 1).trans ((fe 1 (by decide)).trans ((f1 1).trans v1))
  · intro r h1 h10
    exact (fd r).trans ((fe r h10).trans (source r h1))
end E5R.Thermostat.HeadTeValueWidth
