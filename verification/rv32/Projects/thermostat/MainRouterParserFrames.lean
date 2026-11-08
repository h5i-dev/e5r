-- G3: retain initialized router/App/capacity bytes across the real parser.
import Projects.thermostat.HeadFutureChecked
import Projects.thermostat.HeadFutureLine
import Projects.thermostat.HeadFutureInput
import Projects.thermostat.HeadColdFutureComplete
import Projects.thermostat.HeadColdFuture
import Projects.thermostat.MainHeadParser
set_option autoImplicit false
set_option maxRecDepth 4000
set_option maxHeartbeats 3000000
namespace E5R.Thermostat.HeadFutureChecked
open E5R E5R.Thermostat HttpRequestSpec HeadLineScanSpec

theorem contract_routes (B : Board) (c : Core) (ram : Word → BitVec 8) (sp : Word) (j length cap : Nat) (values : Reg → Word)
    (hp : c.pc=0x80002cba#32) (h2 : c.get 2=sp) (h9 : c.get 9=BitVec.ofNat 32 j)
    (h10 : c.get 10=sp+4904#32) (h11 : c.get 11=sp+516#32) (h12 : c.get 12=BitVec.ofNat 32 length)
    (h13 : c.get 13=sp+3664#32) (h14 : c.get 14=BitVec.ofNat 32 cap) (h16 : c.get 16=1024#32)
    (hj : j≤length) (hlen : length≤2048) (hm : Memory.Block B sp 5312) (ha : sp.toNat%4=0)
    (saved : HeadSaved.At ram sp values) (good : HeadMethodTarget.Good (bytes ram (sp+516#32)) j) :
    ∃ n d after, 0<n ∧ n≤126+29*j ∧ Quiet.Steps B img n ⟨c,ram⟩ ⟨d,after⟩ ∧
      HeadRequestOutcome.At d after sp values j length cap (requestLine (bytes ram (sp+516#32)) 0 j) ∧
      ViewFrame.Region ram after (sp+516#32) 2048 ∧
      ViewFrame.Region ram after (sp+384#32) 132 ∧ HeadSaved.At after sp values ∧ d.sameCsr c ∧ ViewFrame.Region ram after (sp+3588#32) 449 := by
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
    · exact HeadVersion.region ram sp e te 384 132 (by decide) (by decide)
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
    refine ⟨a+b,d,_,by omega,by omega,first.trans version,?_,rx,?_,?_,csr2.trans csr,?_⟩
    · change HeadRequestOutcome.At d _ sp values j length cap (requestLine g 0 j)
      rw [badSpec]
      exact ⟨endPC,endSP,abi,out⟩
    · exact HeadRegionFrame.trans (HeadVersion.region ram sp e te 384 132 (by decide) (by decide))
        (HeadResultFrame.reject_region (HeadVersion.memory ram sp e te) sp 4#32 (BitVec.ofNat 32 (HeadVersionReject.status ram sp te)) 384 132 (by decide) (by decide))
    · exact HeadResultFrame.reject_saved (HeadVersion.saved ram sp e te values saved)
    · have f1 := HeadVersion.region ram sp e te 3588 449 (by decide) (by decide)
      have f2 := HeadResultFrame.reject_region (HeadVersion.memory ram sp e te) sp 4#32 (BitVec.ofNat 32 (HeadVersionReject.status ram sp te)) 3588 449 (by decide) (by decide)
      exact fun i => (f2 i).trans (f1 i)
end E5R.Thermostat.HeadFutureChecked

namespace E5R.Thermostat.HeadFutureLine
open E5R E5R.Thermostat HttpRequestSpec HeadLineScanSpec

theorem contract_routes (B : Board) (c : Core) (ram : Word → BitVec 8) (sp : Word) (j length cap : Nat) (values : Reg → Word)
    (hp : c.pc=0x80002cba#32) (h2 : c.get 2=sp) (h9 : c.get 9=BitVec.ofNat 32 j)
    (h10 : c.get 10=sp+4904#32) (h11 : c.get 11=sp+516#32) (h12 : c.get 12=BitVec.ofNat 32 length)
    (h13 : c.get 13=sp+3664#32) (h14 : c.get 14=BitVec.ofNat 32 cap) (h16 : c.get 16=1024#32)
    (hj : j≤length) (hlen : length≤2048) (hm : Memory.Block B sp 5312) (ha : sp.toNat%4=0)
    (saved : HeadSaved.At ram sp values) (positive : 0<length) :
    ∃ n d after, 0<n ∧ n≤126+29*j ∧ Quiet.Steps B img n ⟨c,ram⟩ ⟨d,after⟩ ∧
      HeadRequestOutcome.At d after sp values j length cap (requestLine (bytes ram (sp+516#32)) 0 j) ∧
      ViewFrame.Region ram after (sp+516#32) 2048 ∧
      ViewFrame.Region ram after (sp+384#32) 132 ∧ HeadSaved.At after sp values ∧ d.sameCsr c ∧ ViewFrame.Region ram after (sp+3588#32) 449 := by
  by_cases good : HeadMethodTarget.Good (bytes ram (sp+516#32)) j
  · exact HeadFutureChecked.contract_routes B c ram sp j length cap values hp h2 h9 h10 h11 h12 h13 h14 h16 hj hlen hm ha saved good
  · have buffer : Memory.Block B (sp+516#32) length := Memory.sub_block hm (off := 516) positive (by omega)
    obtain ⟨a,e,alo,ahi,first,pc,status,cache,frame,csr⟩ := HeadMethodTarget.contract B c ram (sp+516#32) j length hp h9 h12 h11 hj hlen buffer
    have atReject : e.pc=0x80002efc#32 := by simpa only [good,ite_false] using pc
    obtain ⟨d,finish,endPC,endSP,abi,out,csr2⟩ := HeadRequestReject.contract B e ram sp values 400 atReject
      ((frame 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h2) ((frame 10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h10) status (by decide) hm ha saved
    refine ⟨a+20,d,_,by omega,by omega,first.trans finish,?_,?_,?_,?_,csr2.trans csr,?_⟩
    · rw [HeadRequestLineSpec.bad_prefix (bytes ram (sp+516#32)) j good]
      exact ⟨endPC,endSP,abi,out⟩
    · exact HeadResultFrame.reject_region ram sp 4#32 400#32 516 2048 (by decide) (by decide)
    · exact HeadResultFrame.reject_region ram sp 4#32 400#32 384 132 (by decide) (by decide)
    · exact HeadResultFrame.reject_saved saved
    · exact HeadResultFrame.reject_region ram sp 4#32 400#32 3588 449 (by decide) (by decide)
end E5R.Thermostat.HeadFutureLine

namespace E5R.Thermostat.HeadFutureInput
open E5R E5R.Thermostat HttpRequestSpec HeadLineScanSpec

theorem contract_routes (B : Board) (c : Core) (ram : Word → BitVec 8) (sp : Word) (input : List (BitVec 8))
    (hp : c.pc=0x80002c46#32) (h2 : c.get 2=sp+384#32) (h10 : c.get 10=sp+4904#32)
    (h11 : c.get 11=sp+516#32) (h12 : c.get 12=BitVec.ofNat 32 input.length) (h13 : c.get 13=sp+3664#32)
    (hm : Memory.Block B sp 5312) (ha : sp.toNat%4=0) (hlen : input.length≤2048)
    (hmax : ramRead ram (sp+3664#32) .w=1024#32) (bytesAt : Bytes.At ram (sp+516#32) input)
    (complete : HeadByteInput.term input=0) :
    ∃ steps d after, 19≤steps ∧ steps≤153+36*min input.length 1024 ∧ Quiet.Steps B img steps ⟨c,ram⟩ ⟨d,after⟩ ∧
      HeadRequestOutcome.At d after sp c.get (line input) input.length (min input.length 1024) (request input) ∧
      ViewFrame.Region ram after (sp+516#32) 2048 ∧
      ViewFrame.Region ram after (sp+384#32) 132 ∧ HeadSaved.At after sp c.get ∧ d.sameCsr c ∧ ViewFrame.Region ram after (sp+3588#32) 449 := by
  let n := min input.length 1024
  let g := bytes ram (sp+516#32)
  let w := window (HttpRequestBytes.bytes input) n
  let j := line input
  let saved := HeadStackSave.memory ram sp c.get
  let gs := bytes saved (sp+516#32)
  have agree : ∀ k, k<n → g k=w k := HeadByteInput.agree bytesAt
  have lines : lineEnd g 0 n=j := HeadLineScanSpec.line_congr g w 0 n agree
  have term : lineTerm g (lineEnd g 0 n) n=0 := by
    rw [HeadLineScanSpec.term_congr g w _ _ agree,lines]
    exact complete
  have inside : j+1<n := by
    rw [lines] at term
    exact HeadMethodInputSpec.term_zero_bound g j n term
  have rawBound : j≤input.length := by have := Nat.min_le_left input.length 1024;omega
  have positive : 0<input.length := by have := Nat.min_le_left input.length 1024;omega
  obtain ⟨a,e,alo,ahi,first,pc,stack,cap,max,index,frame,rx,csr⟩ := HeadFirstLine.contract B c ram sp input.length hp h2 h13 h12 h11 hlen hm ha hmax
  have atLine : e.pc=0x80002cba#32 := by
    change e.pc=HeadLineTerm.pc (lineTerm g (lineEnd g 0 n) n) at pc
    simpa only [term,HeadLineTerm.pc,ite_true] using pc
  have indexJ : e.get 9=BitVec.ofNat 32 j := by
    have idx := index (by omega)
    change e.get 9=BitVec.ofNat 32 (lineEnd g 0 n) at idx
    exact idx.trans (congrArg (BitVec.ofNat 32) lines)
  obtain ⟨b,d,after,blo,bhi,body,result,rx2,appFrame,savedAfter,csr2,config⟩ := HeadFutureLine.contract_routes B e saved sp j input.length n c.get atLine stack indexJ
    ((frame 10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h10) ((frame 11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h11) ((frame 12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h12) ((frame 13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h13) cap max
    rawBound hlen hm ha (HeadSaved.stored ram sp c.get) positive
  have savedAgree : ∀ k, k<j → gs k=w k := by
    intro k hk
    have raw : gs k=g k := congrArg BitVec.toNat (rx ⟨k,by have := Nat.min_le_right input.length 1024;omega⟩)
    exact raw.trans (agree k (by omega))
  have reqEq : requestLine gs 0 j=request input := HeadRequestCongr.requestLine gs w j savedAgree
  refine ⟨a+b,d,after,by omega,by omega,first.trans body,?_,?_,?_,savedAfter,csr2.trans csr,?_⟩
  · change HeadRequestOutcome.At d after sp c.get j input.length n (requestLine gs 0 j) at result
    rw [reqEq] at result
    exact result
  · exact fun i => (rx2 i).trans (rx i)
  · exact HeadRegionFrame.trans (HeadStackMemory.region ram sp c.get 384 132 (by decide) (by decide)) appFrame
  · have f1 := HeadStackMemory.region ram sp c.get 3588 449 (by decide) (by decide)
    exact fun i => (config i).trans (f1 i)
end E5R.Thermostat.HeadFutureInput

namespace E5R.Thermostat.HeadColdFutureComplete
open E5R E5R.Thermostat HttpRequestSpec HeadLineScanSpec

theorem contract_routes (B : Board) (c : Core) (ram : Word → BitVec 8) (sp : Word) (input : List (BitVec 8))
    (hp : c.pc=0x80002c46#32) (h2 : c.get 2=sp+384#32) (h10 : c.get 10=sp+4904#32)
    (h11 : c.get 11=sp+516#32) (h12 : c.get 12=BitVec.ofNat 32 input.length) (h13 : c.get 13=sp+3664#32)
    (hm : Memory.Block B sp 5312) (ha : sp.toNat%4=0) (hlen : input.length≤2048)
    (hmax : ramRead ram (sp+3664#32) .w=1024#32) (bytesAt : Bytes.At ram (sp+516#32) input)
    (complete : HeadByteInput.term input=0) (hbody : ramRead ram (sp+3668#32) .w=1024#32)
    (clOutside : ∀ q : Fin 14, B.inRam (BitVec.ofNat 32 (0x80005de0+q.val)) 1=false)
    (teOutside : ∀ q : Fin 17, B.inRam (BitVec.ofNat 32 (0x80005dee+q.val)) 1=false) :
    ∃ steps d after, 19≤steps ∧ steps≤budget (min input.length 1024) ∧ Quiet.Steps B img steps ⟨c,ram⟩ ⟨d,after⟩ ∧
      d.pc=c.get 1 &&& ~~~1 ∧ d.get 2=sp+384#32 ∧ HeadSaved.CoreAt d c.get ∧
      HeadFinalResult.At after (sp+4904#32) (HttpRequestBytes.parse input 1024 1024) ∧
      ViewFrame.Region ram after (sp+516#32) 2048 ∧
      ViewFrame.Region ram after (sp+384#32) 132 ∧ d.sameCsr c ∧ ViewFrame.Region ram after (sp+3588#32) 449 := by
  let cap := min input.length 1024
  let j := HeadFutureInput.line input
  have capBound : cap≤1024 := Nat.min_le_right input.length 1024
  have lineBound : j≤cap := scan_le notEol (HeadColdSpec.inputBytes input) 0 cap (by omega)
  obtain ⟨n,a,after,nlo,nhi,first,result,rx,app,saved,csr,config⟩ := HeadFutureInput.contract_routes B c ram sp input hp h2 h10 h11 h12 h13 hm ha hlen hmax bytesAt complete
  cases request : HeadFutureInput.request input with
  | bad status =>
    rw [request] at result
    obtain ⟨pc,stack,abi,encoded⟩ := result
    refine ⟨n,a,after,nlo,?_,first,pc,stack,abi,?_,rx,app,csr,config⟩
    · unfold budget;omega
    · rw [HeadColdSpec.bad input status complete request]
      exact encoded
  | ok ms me ts te minor =>
    rw [request] at result
    have ready := result.2.2
    have version : minor≤1 := (HeadRequestSuccess.shape (HeadColdSpec.inputBytes input) j ms me ts te minor request).2.2
    have body : ramRead after (sp+3668#32) .w=1024#32 := by
      have word := ViewFrame.word config 80 (by decide)
      have ptr : (sp+3588#32)+80#32=sp+3668#32 := by rw [BitVec.add_assoc];rfl
      rw [ptr] at word
      exact word.trans hbody
    obtain ⟨m,d,finalRAM,mlo,mhi,finish,pc,stack,abi,encoded,frames,csr2⟩ := HeadFieldsWhole.contract B a after sp me te j minor input.length cap c.get
      ready body (by omega) capBound (Nat.min_le_left _ _) hlen version hm ha saved clOutside teOutside
    have agree (k : Nat) (hk : k<cap) : bytes after (sp+516#32) k=HeadColdSpec.inputBytes input k :=
      (congrArg BitVec.toNat (rx ⟨k,by omega⟩)).trans (HeadByteInput.agree bytesAt k hk)
    have sameFields := HeadFieldsCongr.fields (bytes after (sp+516#32)) (HeadColdSpec.inputBytes input) cap minor (j+2) Fields.empty agree
    change HeadFinalResult.At finalRAM (sp+4904#32) (HeadFieldsFinish.result input.length me (me+1) te minor (fields (bytes after (sp+516#32)) cap minor 1024 (j+2) Fields.empty)) at encoded
    rw [sameFields] at encoded
    refine ⟨n+m,d,finalRAM,by omega,?_,first.trans finish,pc,stack,abi,?_,?_,?_,csr2.trans csr,?_⟩
    · dsimp only [cap] at mhi
      unfold budget;omega
    · rw [HeadColdSpec.good input ms me ts te minor complete request]
      exact encoded
    · exact HeadRegionFrame.trans rx (frames 516 2048 (by decide) (by decide) (Or.inl (by decide)))
    · exact HeadRegionFrame.trans app (frames 384 132 (by decide) (by decide) (Or.inl (by decide)))
    · exact HeadRegionFrame.trans config (frames 3588 449 (by decide) (by decide) (Or.inl (by decide)))
end E5R.Thermostat.HeadColdFutureComplete

namespace E5R.Thermostat.HeadColdFuture
open E5R E5R.Thermostat HttpRequestSpec HeadLineScanSpec

theorem contract_routes (B : Board) (c : Core) (ram : Word → BitVec 8) (sp : Word) (input : List (BitVec 8))
    (hp : c.pc=0x80002c46#32) (h2 : c.get 2=sp+384#32) (h10 : c.get 10=sp+4904#32)
    (h11 : c.get 11=sp+516#32) (h12 : c.get 12=BitVec.ofNat 32 input.length) (h13 : c.get 13=sp+3664#32)
    (hm : Memory.Block B sp 5312) (ha : sp.toNat%4=0) (hlen : input.length≤2048)
    (hmax : ramRead ram (sp+3664#32) .w=1024#32) (bytesAt : Bytes.At ram (sp+516#32) input)
    (hbody : ramRead ram (sp+3668#32) .w=1024#32)
    (clOutside : ∀ q : Fin 14, B.inRam (BitVec.ofNat 32 (0x80005de0+q.val)) 1=false)
    (teOutside : ∀ q : Fin 17, B.inRam (BitVec.ofNat 32 (0x80005dee+q.val)) 1=false) :
    ∃ steps d after, 19≤steps ∧ steps≤HeadColdFutureComplete.budget (min input.length 1024) ∧ Quiet.Steps B img steps ⟨c,ram⟩ ⟨d,after⟩ ∧
      d.pc=c.get 1 &&& ~~~1 ∧ d.get 2=sp+384#32 ∧ HeadSaved.CoreAt d c.get ∧
      HeadFinalResult.At after (sp+4904#32) (HttpRequestBytes.parse input 1024 1024) ∧
      ViewFrame.Region ram after (sp+516#32) 2048 ∧
      ViewFrame.Region ram after (sp+384#32) 132 ∧ d.sameCsr c ∧ ViewFrame.Region ram after (sp+3588#32) 449 := by
  by_cases complete : HeadByteInput.term input=0
  · exact HeadColdFutureComplete.contract_routes B c ram sp input hp h2 h10 h11 h12 h13 hm ha hlen hmax bytesAt complete hbody clOutside teOutside
  · have early : HeadByteInput.term input=1 ∨ HeadByteInput.term input=2 := (HeadPrefix.term_cases input).resolve_left complete
    obtain ⟨steps,d,lo,hi,trace,dpc,dsp,regs,result,rx,app,csr⟩ := HeadEarlyInput.contract B c ram sp input hp h2 h10 h11 h12 h13 hm ha hlen hmax bytesAt early
    have future : ViewFrame.Region ram (HeadEarlyInput.memory ram sp c.get input) (sp+3588#32) 449 :=
      HeadRegionFrame.trans (HeadStackMemory.region ram sp c.get 3588 449 (by decide) (by decide))
        (HeadEarlyFinish.region (HeadStackSave.memory ram sp c.get) sp _ 3588 449 (by decide) (Or.inl (by decide)))
    exact ⟨steps,d,_,by omega,by unfold HeadColdFutureComplete.budget;omega,trace,dpc,dsp,regs,HeadFinalResult.early result,rx,HeadRegionFrame.trans (HeadStackMemory.region ram sp c.get 384 132 (by decide) (by decide)) (HeadEarlyFinish.region (HeadStackSave.memory ram sp c.get) sp _ 384 132 (by decide) (Or.inl (by decide))),csr,future⟩

end E5R.Thermostat.HeadColdFuture

namespace E5R.Thermostat.MainHeadParser
open E5R E5R.Thermostat HttpRequestSpec HeadLineScanSpec

theorem contract_routes (B : Board) (c : Core) (ram : Word → BitVec 8) (input : List (BitVec 8))
    (hp : c.pc=0x80000a10#32) (h2 : c.get 2=0x80ffeb90#32) (h8 : c.get 8=0x80fff814#32)
    (h12 : c.get 12=BitVec.ofNat 32 input.length) (layout : MainHeadLayout.At ram)
    (bytesAt : Bytes.At ram 0x80ffec14#32 input) (length : input.length≤2048)
    (stack : Memory.Block B 0x80ffea10#32 5312)
    (clOutside : ∀ q : Fin 14, B.inRam (BitVec.ofNat 32 (0x80005de0+q.val)) 1=false)
    (teOutside : ∀ q : Fin 17, B.inRam (BitVec.ofNat 32 (0x80005dee+q.val)) 1=false) :
    ∃ n d after, 26≤n ∧ n≤7+HeadColdFutureComplete.budget (min input.length 1024) ∧
      Quiet.Steps B img n ⟨c,ram⟩ ⟨d,after⟩ ∧ d.pc=0x80000a26#32 ∧ d.get 2=0x80ffeb90#32 ∧
      HeadSaved.CoreAt d (values c) ∧ HeadFinalResult.At after 0x80fffd38#32 (HttpRequestBytes.parse input 1024 1024) ∧
      ViewFrame.Region ram after 0x80ffec14#32 2048 ∧ ViewFrame.Region ram after 0x80fff814#32 449 ∧
      MainHeadLayout.At after ∧ ViewFrame.Region ram after 0x80ffeb90#32 132 ∧ d.sameCsr c := by
  have object : Memory.Block B 0x80fff814#32 449 := by
    simpa only [show 0x80ffea10#32+3588#32=0x80fff814#32 by decide +kernel] using Memory.sub_block stack (off := 3588) (m := 449) (by decide) (by decide)
  obtain ⟨a,ta,apc,a11,a13,a10,a1,ar,ac⟩ := MainHeadCall.contract B c ram _ _ h8 h2 layout.rx layout.config object hp
  have asp := (ar 2 (by decide) (by decide) (by decide) (by decide)).trans h2
  have alen := (ar 12 (by decide) (by decide) (by decide) (by decide)).trans h12
  obtain ⟨n,d,after,lo,hi,trace,dpc,dsp,regs,result,rx,app,csr,future⟩ := HeadColdFuture.contract_routes B a ram 0x80ffea10#32 input
    apc asp a10 a11 alen a13 stack (by decide +kernel) length layout.headLimit bytesAt layout.bodyLimit clOutside teOutside
  have returnPC : d.pc=0x80000a26#32 := by rw [dpc,a1];decide +kernel
  have mainFuture : ViewFrame.Region ram after 0x80fff814#32 449 := future
  have saved : HeadSaved.CoreAt d (values c) := by
    constructor
    · simpa only [values,ite_true] using regs.x1.trans a1
    · simpa only [values,show ¬((8 : Reg)=1) by decide,ite_false] using regs.x8.trans (ar 8 (by decide) (by decide) (by decide) (by decide))
    · simpa only [values,show ¬((9 : Reg)=1) by decide,ite_false] using regs.x9.trans (ar 9 (by decide) (by decide) (by decide) (by decide))
    · simpa only [values,show ¬((18 : Reg)=1) by decide,ite_false] using regs.x18.trans (ar 18 (by decide) (by decide) (by decide) (by decide))
    · simpa only [values,show ¬((19 : Reg)=1) by decide,ite_false] using regs.x19.trans (ar 19 (by decide) (by decide) (by decide) (by decide))
    · simpa only [values,show ¬((20 : Reg)=1) by decide,ite_false] using regs.x20.trans (ar 20 (by decide) (by decide) (by decide) (by decide))
    · simpa only [values,show ¬((21 : Reg)=1) by decide,ite_false] using regs.x21.trans (ar 21 (by decide) (by decide) (by decide) (by decide))
    · simpa only [values,show ¬((22 : Reg)=1) by decide,ite_false] using regs.x22.trans (ar 22 (by decide) (by decide) (by decide) (by decide))
    · simpa only [values,show ¬((23 : Reg)=1) by decide,ite_false] using regs.x23.trans (ar 23 (by decide) (by decide) (by decide) (by decide))
    · simpa only [values,show ¬((24 : Reg)=1) by decide,ite_false] using regs.x24.trans (ar 24 (by decide) (by decide) (by decide) (by decide))
    · simpa only [values,show ¬((25 : Reg)=1) by decide,ite_false] using regs.x25.trans (ar 25 (by decide) (by decide) (by decide) (by decide))
    · simpa only [values,show ¬((26 : Reg)=1) by decide,ite_false] using regs.x26.trans (ar 26 (by decide) (by decide) (by decide) (by decide))
    · simpa only [values,show ¬((27 : Reg)=1) by decide,ite_false] using regs.x27.trans (ar 27 (by decide) (by decide) (by decide) (by decide))
  exact ⟨7+n,d,after,by omega,by omega,ta.trans trace,returnPC,dsp,saved,result,rx,mainFuture,
    MainHeadLayout.preserve layout mainFuture,(by simpa only [show 0x80ffea10#32+384#32=0x80ffeb90#32 by decide +kernel] using app),csr.trans ac⟩
end E5R.Thermostat.MainHeadParser
