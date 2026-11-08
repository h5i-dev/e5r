import Projects.thermostat.HeadTeTrailingLoad
import Projects.thermostat.HeadTeTrailingBranch
import Projects.thermostat.HeadTeVersionRaw
import Projects.thermostat.HeadTeVersionBranch
import Projects.thermostat.HeadTeClRaw
import Projects.thermostat.HeadTeClBranch
import Projects.thermostat.HeadTeRuleMath
namespace E5R.Thermostat.HeadTePreflight
open E5R E5R.Thermostat HttpRequestSpec

def Bad (f : Fields) (ve le minor : Nat) : Prop := minor=0 ∨ f.te ∨ f.hasCl ∨ ve≠le
instance (f : Fields) (ve le minor : Nat) : Decidable (Bad f ve le minor) := by unfold Bad;infer_instance

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (sp : Word) (f : Fields) (ve le minor : Nat)
    (hp : c.pc=0x800032ae#32) (h2 : c.get 2=sp) (h18 : c.get 18=BitVec.ofNat 32 (1-minor))
    (h23 : c.get 23=(if f.te then 1#32 else 0#32))
    (scratch : ramRead ram (sp+0#32) .w=BitVec.ofNat 32 le-BitVec.ofNat 32 ve)
    (fields : HeadFieldsView.At ram sp f) (ordered : ve≤le) (bound : le≤2048) (version : minor≤1)
    (stack : Memory.Block B sp 327) (aligned : sp.toNat%4=0) :
    ∃ n d, 2≤n ∧ n≤8 ∧ Quiet.Steps B img n ⟨c,ram⟩ ⟨d,ram⟩ ∧
      d.pc=(if Bad f ve le minor then 0x8000342c#32 else 0x800032c8#32) ∧
      (∀ r : Reg, r≠10 → d.get r=c.get r) ∧ d.sameCsr c := by
  obtain ⟨a,t0,p0,v0,f0,s0⟩ := HeadTeTrailingLoad.contract B c ram sp _ h2 scratch
    (by simpa only [BitVec.add_zero] using (Memory.sub_block stack (off := 0) (m := 56) (by decide) (by decide))) aligned hp
  obtain ⟨b,t1,p1,f1,s1⟩ := HeadTeTrailingBranch.contract B a ram _ (0 : Word) _ p0 v0 (Core.get_zero a)
    (HeadTeRuleMath.trailing_test ve le ordered bound)
  have fb (r : Reg) (hne : r≠10) : b.get r=c.get r := (f1 r).trans (f0 r hne)
  by_cases trailing : ve≠le
  · have bad : Bad f ve le minor := Or.inr (Or.inr (Or.inr trailing))
    refine ⟨2,b,by decide,by decide,by simpa using t0.trans t1,?_,fb,s1.trans s0⟩
    simpa [trailing,bad] using p1
  · have p1' : b.pc=0x800032b4#32 := by simpa [trailing] using p1
    obtain ⟨e,t2,p2,v2,fe,se⟩ := HeadTeVersionRaw.contract B b ram _ _
      ((fb 18 (by decide)).trans h18) ((fb 23 (by decide)).trans h23) p1'
    obtain ⟨d,t3,p3,fd,sd⟩ := HeadTeVersionBranch.contract B e ram _ (0 : Word) _ p2 v2 (Core.get_zero e)
      (HeadTeRuleMath.version_test minor f.te version)
    have source (r : Reg) (hne : r≠10) : d.get r=c.get r := (fd r).trans ((fe r hne).trans (fb r hne))
    by_cases conflict : minor=0 ∨ f.te
    · have bad : Bad f ve le minor := by rcases conflict with h|h;exact Or.inl h;exact Or.inr (Or.inl h)
      refine ⟨5,d,by decide,by decide,by simpa using (t0.trans t1).trans (t2.trans t3),?_,source,sd.trans (se.trans (s1.trans s0))⟩
      simpa [conflict,bad] using p3
    · have p3' : d.pc=0x800032be#32 := by simpa [conflict] using p3
      have flag : BitVec.ofNat 32 (ram (sp+325#32)).toNat=(if f.hasCl then 1#32 else 0#32) := by
        rw [fields.hasCl,HeadTeRuleMath.flag_word]
      obtain ⟨e2,t4,p4,v4,fe2,se2⟩ := HeadTeClRaw.contract B d ram sp _ ((source 2 (by decide)).trans h2) flag stack p3'
      obtain ⟨d2,t5,p5,fd2,sd2⟩ := HeadTeClBranch.contract B e2 ram _ (0 : Word) f.hasCl p4 v4 (Core.get_zero e2)
        (HeadTeRuleMath.flag_test f.hasCl)
      have badIff : Bad f ve le minor ↔ f.hasCl=true := by
        unfold Bad
        constructor
        · intro h;rcases h with h|h|h|h
          · exact False.elim (conflict (Or.inl h))
          · exact False.elim (conflict (Or.inr h))
          · exact h
          · exact False.elim (trailing h)
        · intro h;exact Or.inr (Or.inr (Or.inl h))
      refine ⟨8,d2,by decide,by decide,by simpa using ((t0.trans t1).trans (t2.trans t3)).trans (t4.trans t5),?_,?_,sd2.trans (se2.trans (sd.trans (se.trans (s1.trans s0))))⟩
      · by_cases hasCl : f.hasCl=true
        · simpa [hasCl,badIff.mpr hasCl] using p5
        · have noBad : ¬Bad f ve le minor := fun h => hasCl (badIff.mp h)
          simpa [hasCl,noBad] using p5
      · intro r hne
        exact (fd2 r).trans ((fe2 r hne).trans (source r hne))
end E5R.Thermostat.HeadTePreflight
