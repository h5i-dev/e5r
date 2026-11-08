import Projects.thermostat.MainCloseSave
import Projects.thermostat.MainCloseRestore
import Projects.thermostat.MainCloseBody
import Projects.thermostat.HeaderFrame
set_option autoImplicit false
set_option maxRecDepth 4000
namespace E5R.Thermostat.MainWantsClose
open E5R E5R.Thermostat

/-- Complete real wants_close ABI call, actual eleven saves/restores and RET.
    Only its 48-byte stack frame is written; the parser-owned Request/raw views
    are explicitly preserved across those stores. -/
theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (sp req rawPtr : Word)
    (raw : List (BitVec 8)) (entries : List HeaderSpec.Entry)
    (h : Header.Pre B ram req rawPtr raw entries) (limit : raw.length≤2048)
    (hp : c.pc=0x800023f2#32) (h2 : c.get 2=sp+48#32) (h10 : c.get 10=req)
    (stack : Memory.Block B sp 48) (aligned : sp.toNat%4=0)
    (requestSeparate : ∀ i : Fin 372, ∀ j : Fin 48, req+BitVec.ofNat 32 i.val≠sp+BitVec.ofNat 32 j.val)
    (rawSeparate : ∀ i : Fin raw.length, ∀ j : Fin 48, rawPtr+BitVec.ofNat 32 i.val≠sp+BitVec.ofNat 32 j.val) :
    ∃ n d, n≤(77+86*raw.length)*entries.length+51 ∧
      Quiet.Steps B img n ⟨c,ram⟩ ⟨d,MainCloseSave.memory ram sp c⟩ ∧ d.pc=c.get 1 &&& ~~~1 ∧
      d.get 10=(if MainCloseSpec.wantsClose raw entries then 1#32 else 0#32) ∧
      (∀ r : Reg, r∈[1,2,3,4,8,9,18,19,20,21,22,23,24,25,26,27] → d.get r=c.get r) ∧ d.sameCsr c := by
  let after := MainCloseSave.memory ram sp c
  have requestFrame : ViewFrame.Region ram after req 372 := fun i => MainCloseSave.frame ram sp c _ (requestSeparate i)
  have rawFrame : ViewFrame.Region ram after rawPtr raw.length := fun i => MainCloseSave.frame ram sp c _ (rawSeparate i)
  have header := HeaderFrame.header h requestFrame rawFrame
  obtain ⟨a,sa,pa,a2,ar,ac⟩ := MainCloseSave.contract B c ram sp c rfl h2 stack aligned hp
  have a10 : a.get 10=req := (ar 10 (by decide)).trans h10
  obtain ⟨m,b,mb,sb,pb,b10,br,bc⟩ := MainCloseBody.contract B a after req rawPtr raw entries header limit pa a10
  have b2 : b.get 2=sp := (br 2 (by simp)).trans a2
  obtain ⟨e,se,pe,e8,e9,e18,e19,e20,e21,e22,e23,e24,e25,e26,e2,er,ec⟩ := MainCloseRestore.contract B b after sp b2 stack aligned pb
  have e1 : e.get 1=c.get 1 := (er 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans ((br 1 (by simp)).trans (ar 1 (by decide)))
  let d := e.goto (c.get 1 &&& ~~~1)
  have ret : Quiet.Step B img ⟨e,after⟩ ⟨d,after⟩ := by
    refine QuietDet.step_of (by rw [pe];decide) (by rw [pe];exact re2147493526) fun o => ?_
    rw [exec_jalr,e1,BitVec.add_zero,jump_ok _ _ (clear_bit0 _)];rfl
  have output : d.get 10=(if MainCloseSpec.wantsClose raw entries then 1#32 else 0#32) := (er 10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans b10
  refine ⟨12+m+12+1,d,by omega,((sa.trans sb).trans se).trans (.single ret),rfl,output,?_,(by exact ec.trans (bc.trans ac))⟩
  intro r member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact (er 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans ((br 1 (by simp)).trans (ar 1 (by decide)))
  · exact e2.trans h2.symm
  · exact (er 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans ((br 3 (by simp)).trans (ar 3 (by decide)))
  · exact (er 4 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans ((br 4 (by simp)).trans (ar 4 (by decide)))
  · exact (e8.trans (MainCloseSave.saved8 ram sp c))
  · exact (e9.trans (MainCloseSave.saved9 ram sp c))
  · exact (e18.trans (MainCloseSave.saved18 ram sp c))
  · exact (e19.trans (MainCloseSave.saved19 ram sp c))
  · exact (e20.trans (MainCloseSave.saved20 ram sp c))
  · exact (e21.trans (MainCloseSave.saved21 ram sp c))
  · exact (e22.trans (MainCloseSave.saved22 ram sp c))
  · exact (e23.trans (MainCloseSave.saved23 ram sp c))
  · exact (e24.trans (MainCloseSave.saved24 ram sp c))
  · exact (e25.trans (MainCloseSave.saved25 ram sp c))
  · exact (e26.trans (MainCloseSave.saved26 ram sp c))
  · exact (er 27 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans ((br 27 (by simp)).trans (ar 27 (by decide)))
end E5R.Thermostat.MainWantsClose
