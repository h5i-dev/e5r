import Projects.thermostat.HeadClassSpec
namespace E5R.Thermostat.HeadHeaderActionView
open E5R E5R.Thermostat HttpRequestSpec

def stored (old : Fields) : Added → Fields
  | .bad _ => old
  | .ok f => f

def At (c : Core) : Added → Prop
  | .bad status => c.pc=0x8000342c#32 ∧ c.get 1=BitVec.ofNat 32 status
  | .ok _ => c.pc=0x800033b6#32

def Effect (ram after : Word → BitVec 8) (sp : Word) : Prop :=
  after=ram ∨ (∃ value : Word, after=HeadClStoreRaw.memory ram sp value) ∨ after=HeadTeFlagStore.memory ram sp

theorem from_cl {ram after sp c f result}
    (post : HeadClNumber.Post ram after sp c result)
    (view : HeadFieldsView.At after sp (HeadClNumber.updated f result)) :
    At c (HeadClassSpec.ofCl f result) ∧
      HeadFieldsView.At after sp (stored f (HeadClassSpec.ofCl f result)) ∧ Effect ram after sp := by
  cases result with
  | bad status => exact ⟨⟨post.1,post.2.1⟩,view,Or.inl post.2.2⟩
  | ok value => exact ⟨post.1,view,Or.inr (Or.inl ⟨BitVec.ofNat 32 value,post.2⟩)⟩

theorem from_te {ram after sp c f result}
    (post : HeadTeValue.Post ram after sp c result)
    (view : HeadFieldsView.At after sp (if result=none then {f with te := true} else f)) :
    At c (HeadClassSpec.ofTe f result) ∧
      HeadFieldsView.At after sp (stored f (HeadClassSpec.ofTe f result)) ∧ Effect ram after sp := by
  cases result with
  | some status => exact ⟨⟨post.1,post.2.1⟩,view,Or.inl post.2.2⟩
  | none => exact ⟨post.1,view,Or.inr (Or.inr post.2)⟩
end E5R.Thermostat.HeadHeaderActionView
