import Projects.thermostat.MainRelayBody
import Projects.thermostat.MainPathCapturedReturn
import Projects.thermostat.WordZero
set_option autoImplicit false
namespace E5R.Thermostat.MainRelayMatch
open E5R E5R.Thermostat

/-- Actual relay matcher, including saves, arbitrary suffix, capture stores,
    thirteen restores and real RET. Caller layouts are not assumed unchanged. -/
theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (path params ret : Word) (param : List (BitVec 8))
    (retAligned : ret.getLsbD 0=false) (retMask : ret &&& ~~~1=ret)
    (hp : c.pc=0x8000283a#32) (h2 : c.get 2=0x80ffeb90#32) (hret : c.get 1=ret)
    (h10 : c.get 10=0x80005b9c#32) (h11 : c.get 11=10#32) (h12 : c.get 12=path)
    (h13 : c.get 13=BitVec.ofNat 32 (7+param.length)) (h14 : c.get 14=params)
    (stack : Memory.Block B 0x80ffeb50#32 64)
    (patternBytes : ReadBytes.Span B img ram 0x80005b9c#32 (WireSpec.ascii "/relay/{i}"))
    (pathBytes : Bytes.Span B ram path (WireSpec.ascii "/relay/"++param))
    (nonempty : param≠[]) (noSlash : ∀ b∈param, b≠47#8)
    (block : Memory.Block B params 8) (aligned : params.toNat%4=0)
    (pathSeparate : WordRegions.Disjoint path (WireSpec.ascii "/relay/"++param).length 0x80ffeb30#32 96)
    (paramsSeparate : WordRegions.Disjoint params 8 0x80ffeb30#32 96) :
    ∃ d, Quiet.Steps B img (240+5*param.length) ⟨c,ram⟩
      ⟨d,MainRelayCapture.memory (MainPathStateSave.memory ram c) params (BitVec.ofNat 32 (7+param.length))⟩ ∧
      d.pc=ret ∧ d.get 10=1#32 ∧ d.get 11=1#32 ∧
      (∀ r : Reg, r∈[1,2,3,4,8,9,18,19,20,21,22,23,24,25,26,27] → d.get r=c.get r) ∧ d.sameCsr c := by
  let saved := MainPathStateSave.memory ram c
  let after := MainRelayCapture.memory saved params (BitVec.ofNat 32 (7+param.length))
  have pathFrame : ViewFrame.Region ram saved path (WireSpec.ascii "/relay/"++param).length := by
    intro i
    dsimp only [saved]
    rw [MainPathStateSave.memory_eq]
    exact OuterSave.frame ram 0x80ffeb30#32 c _ (pathSeparate i)
  have pathSaved := ViewFrame.span pathBytes pathFrame
  have patternSaved : ReadBytes.Span B img saved 0x80005b9c#32 (WireSpec.ascii "/relay/{i}") := by
    refine ⟨patternBytes.length,patternBytes.nowrap,?_⟩
    intro i
    apply (patternBytes.bytes i).frame
    dsimp only [saved]
    rw [MainPathStateSave.memory_eq]
    apply OuterSave.frame
    exact WordZero.separated 0x80005b9c#32 0x80ffeb30#32 10 96 (by decide +kernel) (by decide +kernel) i
  obtain ⟨a,save,pa,a2,ar,ac⟩ := MainPathStateSave.contract B c ram c rfl h2 stack hp
  obtain ⟨b,body,pb,b10,b11,basic,bc⟩ := MainRelayBody.contract B a saved path params param pa
    ((ar 10 (by decide)).trans h10) ((ar 11 (by decide)).trans h11) ((ar 12 (by decide)).trans h12)
    ((ar 13 (by decide)).trans h13) ((ar 14 (by decide)).trans h14) patternSaved pathSaved nonempty noSlash block aligned
  have b2 : b.get 2=0x80ffeb50#32 := (basic 2 (by decide)).trans a2
  have savedFrame : ViewFrame.Region saved after 0x80ffeb30#32 96 :=
    MainRelayCapture.region saved params _ _ _ (WordRegions.symm paramsSeparate)
  obtain ⟨d,restore,pd,d1,d8,d9,d18,d19,d20,d21,d22,d23,d24,d25,d26,d27,d2,dr,dc⟩ :=
    MainPathCapturedReturn.contract B b after ram c ret retAligned retMask b2 savedFrame hret stack pb
  have result : d.get 10=1#32 := (dr 10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans b10
  have count : d.get 11=1#32 := (dr 11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans b11
  have steps : 14+(211+5*param.length)+15=240+5*param.length := by omega
  refine ⟨d,by simpa only [steps] using (save.trans body).trans restore,pd,result,count,?_,dc.trans (bc.trans ac)⟩
  intro r member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact d1
  · exact d2.trans h2.symm
  · exact (dr 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans ((basic 3 (by decide)).trans (ar 3 (by decide)))
  · exact (dr 4 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans ((basic 4 (by decide)).trans (ar 4 (by decide)))
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
end E5R.Thermostat.MainRelayMatch
