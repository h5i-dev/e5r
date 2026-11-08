import Projects.thermostat.HeadMethodTarget
import Projects.thermostat.HeadVersionReject
import Projects.thermostat.HeadRequestLineSpec
import Projects.thermostat.HeadLineReadyFromVersion
import Projects.thermostat.HeadRequestOutcome
namespace E5R.Thermostat.HeadFutureChecked
open E5R E5R.Thermostat HttpRequestSpec HeadLineScanSpec

/-- Actual first-line request parser for byte-classified valid method/target
    prefixes. Version errors really return an encoded reject; valid versions
    reach the real header initializer with all memory/layout prerequisites. -/
theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (sp : Word) (j length cap : Nat) (values : Reg → Word)
    (hp : c.pc=0x80002cba#32) (h2 : c.get 2=sp) (h9 : c.get 9=BitVec.ofNat 32 j)
    (h10 : c.get 10=sp+4904#32) (h11 : c.get 11=sp+516#32) (h12 : c.get 12=BitVec.ofNat 32 length)
    (h13 : c.get 13=sp+3664#32) (h14 : c.get 14=BitVec.ofNat 32 cap) (h16 : c.get 16=1024#32)
    (hj : j≤length) (hlen : length≤2048) (hm : Memory.Block B sp 5312) (ha : sp.toNat%4=0)
    (saved : HeadSaved.At ram sp values) (good : HeadMethodTarget.Good (bytes ram (sp+516#32)) j) :
    ∃ n d after, 0<n ∧ n≤126+29*j ∧ Quiet.Steps B img n ⟨c,ram⟩ ⟨d,after⟩ ∧
      HeadRequestOutcome.At d after sp values j length cap (requestLine (bytes ram (sp+516#32)) 0 j) ∧
      ViewFrame.Region ram after (sp+516#32) 2048 ∧
      (sp=0x80ffea10#32 → ∀ state, AppState.At ram state → AppState.At after state) ∧ HeadSaved.At after sp values ∧ d.sameCsr c ∧ ViewFrame.Region ram after (sp+3588#32) 449 := by
  let buf := sp+516#32
  let g := bytes ram buf
  let m := scan isTchar g 0 j
  let te := scan isTargetByte g (m+1) j
  let v := HttpRequestSpec.version g (te+1) (te+9)
  have methodGood : HeadMethodPrefix.Good g j := good.1
  have targetGood : HeadTargetValidationSpec.Good g m te j := good.2
  have target : m+1<te ∧ te<j ∧ g te=32 ∧ g (m+1)=47 ∧ j-te=9 := targetGood
  have width : te+9=j := by omega
  have versionEnd : HttpRequestSpec.version g (te+1) j=v := by rw [←width]
  have parsed : requestLine g 0 j=(if v=3 then ReqLine.bad 400 else if v=2 then ReqLine.bad 505 else ReqLine.ok 0 m (m+1) te v) := by
    have spec := HeadRequestLineSpec.checked_target g j methodGood targetGood
    change requestLine g 0 j=(if HttpRequestSpec.version g (te+1) j=3 then _ else if HttpRequestSpec.version g (te+1) j=2 then _ else _) at spec
    rw [versionEnd] at spec
    exact spec
  have buffer : Memory.Block B buf length := Memory.sub_block hm (off := 516) (by omega) (by omega)
  obtain ⟨a,e,alo,ahi,first,pc,status,cache,frame,csr⟩ := HeadMethodTarget.contract B c ram buf j length hp h9 h12 h11 hj hlen buffer
  have atVersion : e.pc=0x80002e20#32 := by
    change e.pc=(if HeadMethodTarget.Good g j then _ else _) at pc
    simpa only [show HeadMethodTarget.Good g j from good,ite_true] using pc
  obtain ⟨mask,index,endIndex,start,off,pos,ptr⟩ := cache good
  have arg_stack := (frame 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h2
  have arg_dst := (frame 10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h10
  have arg_buf := (frame 11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h11
  have arg_len := (frame 12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h12
  have arg_limits := (frame 13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h13
  have arg_cap := (frame 14 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h14
  have arg_maxHead := (frame 16 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h16
  have arg_line := (frame 9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h9
  by_cases accepted : v<2
  · obtain ⟨b,d,blo,bhi,version,result,stack,reloadWord,frame2,csr2⟩ := HeadVersion.contract B e ram sp m te length atVersion
      arg_stack arg_dst arg_buf arg_len index off pos ptr status hm ha (by omega) (by omega) hlen
    have ready : HeadLineReady.At d (HeadVersion.memory ram sp e te) sp m te j v length cap :=
      HeadLineReadyFromVersion.contract e d ram sp m te j length cap (by omega) mask arg_dst arg_buf arg_len arg_limits arg_cap arg_maxHead
        index endIndex start stack
        ((frame2 9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans arg_line) accepted result
    refine ⟨a+b,d,_,by omega,by omega,first.trans version,?_,?_,?_,?_,csr2.trans csr,?_⟩
    · change HeadRequestOutcome.At d _ sp values j length cap (requestLine g 0 j)
      rw [parsed]
      have three : ¬v=3 := by omega
      have two : ¬v=2 := by omega
      simp only [three,two,ite_false,HeadRequestOutcome.At]
      exact ⟨True.intro,True.intro,ready⟩
    · exact HeadVersion.region ram sp e te 516 2048 (by decide) (by decide)
    · intro actual state app
      rw [actual]
      exact HeadVersion.app ram e te state app
    · exact HeadVersion.saved ram sp e te values saved
    · exact HeadVersion.region ram sp e te 3588 449 (by decide) (by decide)
  · obtain ⟨b,d,blo,bhi,version,endPC,endSP,abi,out,rx,app,csr2⟩ := HeadVersionReject.contract B e ram sp m te length atVersion
      arg_stack arg_dst arg_buf arg_len index off pos ptr status hm ha (by omega) (by omega) hlen values saved accepted
    have upper : v≤3 := HeadVersionSpec.version_le g (te+1) (te+9)
    have badSpec : requestLine g 0 j=ReqLine.bad (HeadVersionReject.status ram sp te) := by
      rw [parsed]
      change (if v=3 then ReqLine.bad 400 else if v=2 then ReqLine.bad 505 else ReqLine.ok 0 m (m+1) te v)=ReqLine.bad (if v=3 then 400 else 505)
      by_cases three : v=3
      · simp only [three,ite_true]
      · have two : v=2 := by omega
        simp only [three,two,show ¬(2=3) by decide,ite_false,ite_true]
    refine ⟨a+b,d,_,by omega,by omega,first.trans version,?_,rx,app,?_,csr2.trans csr,?_⟩
    · change HeadRequestOutcome.At d _ sp values j length cap (requestLine g 0 j)
      rw [badSpec]
      exact ⟨endPC,endSP,abi,out⟩
    · exact HeadResultFrame.reject_saved (HeadVersion.saved ram sp e te values saved)
    · have f1 := HeadVersion.region ram sp e te 3588 449 (by decide) (by decide)
      have f2 := HeadResultFrame.reject_region (HeadVersion.memory ram sp e te) sp 4#32 (BitVec.ofNat 32 (HeadVersionReject.status ram sp te)) 3588 449 (by decide) (by decide)
      exact fun i => (f2 i).trans (f1 i)
end E5R.Thermostat.HeadFutureChecked
