import Projects.thermostat.MainPathStateSave
import Projects.thermostat.MainPathStateBody
import Projects.thermostat.MainPathStateRestore
import Projects.thermostat.WordRegions
import Projects.thermostat.WordZero
import Projects.thermostat.ViewFrame
set_option autoImplicit false
set_option maxRecDepth 6000
namespace E5R.Thermostat.MainPathState
open E5R E5R.Thermostat

/-- The actual first /state matcher call, including both real memcmp calls,
    thirteen stack saves/restores and RET. Its successful result and zero
    captures follow from exact input bytes, not a desired matcher result. -/
theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (path params : Word)
    (hp : c.pc=0x8000283a#32) (h2 : c.get 2=0x80ffeb90#32) (hret : c.get 1=0x800013d2#32)
    (h10 : c.get 10=0x80005b83#32) (h11 : c.get 11=6#32) (h12 : c.get 12=path)
    (h13 : c.get 13=6#32) (h14 : c.get 14=params)
    (stack : Memory.Block B 0x80ffeb50#32 64)
    (patternBytes : ReadBytes.Span B img ram 0x80005b83#32 (WireSpec.ascii "/state"))
    (pathBytes : Bytes.Span B ram path (WireSpec.ascii "/state"))
    (separate : WordRegions.Disjoint path 6 0x80ffeb30#32 96) :
    ∃ d, Quiet.Steps B img 187 ⟨c,ram⟩ ⟨d,MainPathStateSave.memory ram c⟩ ∧
      d.pc=0x800013d2#32 ∧ d.get 10=1#32 ∧ d.get 11=0#32 ∧
      (∀ r : Reg, r∈[1,2,3,4,8,9,18,19,20,21,22,23,24,25,26,27] → d.get r=c.get r) ∧ d.sameCsr c := by
  let after := MainPathStateSave.memory ram c
  have pathFrame : ViewFrame.Region ram after path (WireSpec.ascii "/state").length := by
    intro i
    dsimp only [after]
    rw [MainPathStateSave.memory_eq]
    apply OuterSave.frame
    exact separate i
  have pathSaved : ReadBytes.Span B img after path (WireSpec.ascii "/state") := ReadBytes.of_ram (ViewFrame.span pathBytes pathFrame)
  have patternSaved : ReadBytes.Span B img after 0x80005b83#32 (WireSpec.ascii "/state") := by
    refine ⟨patternBytes.length,patternBytes.nowrap,?_⟩
    intro i
    apply (patternBytes.bytes i).frame
    dsimp only [after]
    rw [MainPathStateSave.memory_eq]
    apply OuterSave.frame
    exact WordZero.separated 0x80005b83#32 0x80ffeb30#32 6 96 (by decide +kernel) (by decide +kernel) i
  obtain ⟨a,save,pa,a2,ar,ac⟩ := MainPathStateSave.contract B c ram c rfl h2 stack hp
  obtain ⟨b,body,pb,b19,b9,b20,b18,b21,b8,b10,b11,b24,b25,b26,b27,b22,b12,b23,b13,b1,b14,br,bc⟩ := MainPathStateBody.contract B a after path params
    ((ar 10 (by decide)).trans h10) ((ar 11 (by decide)).trans h11) ((ar 12 (by decide)).trans h12)
    ((ar 13 (by decide)).trans h13) ((ar 14 (by decide)).trans h14) patternSaved pathSaved pa
  have b2 : b.get 2=0x80ffeb50#32 := (br 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans a2
  obtain ⟨d,restore,pd,d1,d8,d9,d18,d19,d20,d21,d22,d23,d24,d25,d26,d27,d2,dr,dc⟩ := MainPathStateRestore.contract B b after ram c b2 rfl hret stack pb
  have result : d.get 10=1#32 := (dr 10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans b10
  have captures : d.get 11=0#32 := (dr 11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans b11
  refine ⟨d,(save.trans body).trans restore,pd,result,captures,?_,dc.trans (bc.trans ac)⟩
  intro r member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact d1
  · exact d2.trans h2.symm
  · exact (dr 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans
      ((br 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans (ar 3 (by decide)))
  · exact (dr 4 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans
      ((br 4 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans (ar 4 (by decide)))
  · exact d8
  · exact d9
  · exact d18
  · exact d19
  · exact d20
  · exact d21
  · exact d22
  · exact d23
  · exact d24
  · exact d25
  · exact d26
  · exact d27
end E5R.Thermostat.MainPathState
