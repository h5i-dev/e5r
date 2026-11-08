import Projects.thermostat.HeadClFlagsRaw
import Projects.thermostat.HeadClFlagsBranch
import Projects.thermostat.HeadClFlagsMath
namespace E5R.Thermostat.HeadClPreflight
open E5R E5R.Thermostat HttpRequestSpec

def Bad (f : Fields) (ve le : Nat) : Prop := f.hasCl ∨ f.te ∨ ve≠le
instance (f : Fields) (ve le : Nat) : Decidable (Bad f ve le) := by unfold Bad;infer_instance

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (sp : Word) (f : Fields) (ve le : Nat)
    (hp : c.pc=0x800031dc#32) (h2 : c.get 2=sp) (h23 : c.get 23=(if f.te then 1#32 else 0#32))
    (scratch : ramRead ram (sp+0#32) .w=BitVec.ofNat 32 le-BitVec.ofNat 32 ve)
    (fields : HeadFieldsView.At ram sp f) (ordered : ve≤le) (bound : le≤2048)
    (stack : Memory.Block B sp 327) (aligned : sp.toNat%4=0) :
    ∃ d, Quiet.Steps B img 7 ⟨c,ram⟩ ⟨d,ram⟩ ∧
      d.pc=(if Bad f ve le then 0x8000342c#32 else 0x800031f2#32) ∧
      (∀ r : Reg, r≠10 → r≠12 → d.get r=c.get r) ∧ d.sameCsr c := by
  have flag : BitVec.ofNat 32 (ram (sp+325#32)).toNat=(if f.hasCl then 1#32 else 0#32) := by
    rw [fields.hasCl,HeadTeRuleMath.flag_word]
  obtain ⟨a,step,pc,v10,v12,frame,csr⟩ := HeadClFlagsRaw.contract B c ram sp _ _ _ h2 h23 flag scratch stack aligned hp
  obtain ⟨d,branch,pc2,frame2,csr2⟩ := HeadClFlagsBranch.contract B a ram _ (0 : Word) _ pc v10 (Core.get_zero a)
    (HeadClFlagsMath.test f.hasCl f.te ve le ordered bound)
  exact ⟨d,by simpa using step.trans branch,(by simpa only [decide_eq_true_eq,Bad] using pc2),fun r h10 h12 => (frame2 r).trans (frame r h10 h12),csr2.trans csr⟩
end E5R.Thermostat.HeadClPreflight
