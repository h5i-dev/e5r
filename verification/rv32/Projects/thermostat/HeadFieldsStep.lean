import Projects.thermostat.HeadFieldLineReady
import Projects.thermostat.HeadFieldsStepSpec
import Projects.thermostat.HeadFieldsStepFrame
namespace E5R.Thermostat.HeadFieldsStep
open E5R E5R.Thermostat HttpRequestSpec HeadLineScanSpec

def lineWrites : List Reg := [10,11,21,13,25,14,30,15,26,1,20,12,31,19]
def writes : List Reg := lineWrites++HeadHeaderAdd.writes

def At (c : Core) (ram : Word → BitVec 8) (sp : Word) (length minor : Nat) : HeadFieldsStepSpec.Next → Prop
  | .more => c.pc=0x800033ea#32
  | .bad status => c.pc=0x8000342c#32 ∧ c.get 1=BitVec.ofNat 32 status
  | .done f len => c.pc=0x80003456#32 ∧ c.get 24=BitVec.ofNat 32 (len-2) ∧
      HeadFieldsView.At ram sp f ∧ c.get 23=(if f.te then 1#32 else 0#32)
  | .again index f => HeadFieldsRegs.At c sp index length minor f ∧ HeadFieldsView.At ram sp f

theorem line_ne : ∀ r : Reg, r∉lineWrites → r≠10 ∧ r≠11 ∧ r≠21 ∧ r≠13 ∧ r≠25 ∧ r≠14 ∧ r≠30 ∧
    r≠15 ∧ r≠26 ∧ r≠1 ∧ r≠20 ∧ r≠12 ∧ r≠31 ∧ r≠19 := by decide +kernel

theorem constants_safe : ∀ r : Reg, r∈HeadFieldsConstants.protectedRegs → r∉lineWrites ∧ r∉HeadHeaderAdd.writes := by decide +kernel

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (sp : Word) (i cap length minor : Nat) (f : Fields)
    (regs : HeadFieldsRegs.At c sp i length minor f) (metadata : HeadFieldsMeta.At ram sp length cap)
    (fields : HeadFieldsView.At ram sp f) (inside : i<cap) (upper : cap≤length) (bound : length≤2048) (version : minor≤1)
    (stack : Memory.Block B sp 5312) (aligned : sp.toNat%4=0)
    (clOutside : ∀ q : Fin 14, B.inRam (BitVec.ofNat 32 (0x80005de0+q.val)) 1=false)
    (teOutside : ∀ q : Fin 17, B.inRam (BitVec.ofNat 32 (0x80005dee+q.val)) 1=false) :
    let g := bytes ram (sp+516#32)
    ∃ n d after, 10≤n ∧ n≤662+108*(cap-i) ∧ Quiet.Steps B img n ⟨c,ram⟩ ⟨d,after⟩ ∧
      At d after sp length minor (HeadFieldsStepSpec.one g i cap minor f) ∧
      HeadFieldsMeta.At after sp length cap ∧ HeadFieldsConstants.At d sp length minor ∧
      HeadFieldsStepFrame.At ram after sp ∧ HeadRegisterFrame.At c d writes ∧ d.sameCsr c := by
  let g := bytes ram (sp+516#32)
  change ∃ n d after, 10≤n ∧ n≤662+108*(cap-i) ∧ Quiet.Steps B img n ⟨c,ram⟩ ⟨d,after⟩ ∧
    At d after sp length minor (HeadFieldsStepSpec.one g i cap minor f) ∧
    HeadFieldsMeta.At after sp length cap ∧ HeadFieldsConstants.At d sp length minor ∧
    HeadFieldsStepFrame.At ram after sp ∧ HeadRegisterFrame.At c d writes ∧ d.sameCsr c
  obtain ⟨n,a,mid,lo,hi,line,lineResult,lineMemory,metadataMid,rawFrame,csr,successStatus⟩ := HeadFieldLineReady.contract B c ram sp i cap length minor f regs metadata inside upper bound stack aligned
  change HeadFieldLineSpec.At a mid sp i (HeadFieldLineSpec.next g i cap) at lineResult
  have lineFrame : HeadRegisterFrame.At c a lineWrites := by
    intro r safe
    obtain ⟨h10,h11,h21,h13,h25,h14,h30,h15,h26,h1,h20,h12,h31,h19⟩ := line_ne r safe
    exact rawFrame r h10 h11 h21 h13 h25 h14 h30 h15 h26 h1 h20 h12 h31 h19
  have constantsMid : HeadFieldsConstants.At a sp length minor :=
    HeadFieldsConstants.preserve (HeadFieldsConstants.of_regs regs) (fun r h => lineFrame r (constants_safe r h).1)
  have fieldsMid : HeadFieldsView.At mid sp f :=
    HeadFieldsView.preserve fields (HeadRegionFrame.offset lineMemory 56 271 (by decide) (by decide))
  have baseFrame : HeadRegisterFrame.At c a writes := HeadRegisterFrame.mono lineFrame (by decide +kernel)
  cases lineCase : HeadFieldLineSpec.next g i cap with
  | more =>
    have pc : a.pc=0x800033ea#32 := by simpa only [HeadFieldLineSpec.At,lineCase] using lineResult
    rw [HeadFieldsStepSpec.one,lineCase]
    dsimp only
    exact ⟨n,a,mid,lo,by omega,line,pc,metadataMid,constantsMid,HeadFieldsStepFrame.of_line lineMemory,baseFrame,csr⟩
  | bad status =>
    have post : a.pc=0x8000342c#32 ∧ a.get 1=BitVec.ofNat 32 status := by simpa only [HeadFieldLineSpec.At,lineCase] using lineResult
    rw [HeadFieldsStepSpec.one,lineCase]
    dsimp only
    exact ⟨n,a,mid,lo,by omega,line,post,metadataMid,constantsMid,HeadFieldsStepFrame.of_line lineMemory,baseFrame,csr⟩
  | done len =>
    have post : a.pc=0x80003456#32 ∧ a.get 24=BitVec.ofNat 32 (len-2) := by simpa only [HeadFieldLineSpec.At,lineCase] using lineResult
    rw [HeadFieldsStepSpec.one,lineCase]
    dsimp only
    exact ⟨n,a,mid,lo,by omega,line,⟨post.1,post.2,fieldsMid,(lineFrame 23 (by decide)).trans regs.te⟩,
      metadataMid,constantsMid,HeadFieldsStepFrame.of_line lineMemory,baseFrame,csr⟩
  | header le parsed =>
    have parsedAt : HeadHeaderLineView.At a mid sp (sp+516#32) i le parsed ∧ a.get 11=BitVec.ofNat 32 le ∧
        a.get 21=BitVec.ofNat 32 (le-i) ∧ a.get 24=BitVec.ofNat 32 i ∧ a.get 26=BitVec.ofNat 32 le := by
      simpa only [HeadFieldLineSpec.At,lineCase] using lineResult
    obtain ⟨leLower,leUpper⟩ := HeadFieldsStepSpec.header_bound g i cap le parsed inside lineCase
    cases parsed with
    | bad status =>
      rw [HeadFieldsStepSpec.one,lineCase]
      dsimp only
      exact ⟨n,a,mid,lo,by omega,line,parsedAt.1,metadataMid,constantsMid,HeadFieldsStepFrame.of_line lineMemory,baseFrame,csr⟩
    | ok ne vs ve =>
      obtain ⟨pc,nameWord,nameLength,valueStart,valueEnd,namePointer,nameLower,valueLower,valueOrder,valueUpper⟩ := parsedAt.1
      obtain ⟨m,d,after,mlo,mhi,add,post,view,metadataAfter,addMemory,addFrame,csr2⟩ := HeadHeaderAdd.contract B a mid sp f i ne vs ve le length cap minor pc constantsMid (successStatus pc)
        ((lineFrame 9 (by decide)).trans regs.count) ((lineFrame 23 (by decide)).trans regs.te)
        parsedAt.2.2.2.1 valueEnd parsedAt.2.2.1 nameLength namePointer valueStart parsedAt.2.2.2.2 parsedAt.2.1 nameWord
        metadataMid fieldsMid ⟨nameLower,valueLower,valueOrder,valueUpper,leUpper⟩ upper bound version stack aligned clOutside teOutside
      have agree (k : Nat) (hk : k<2048) : bytes mid (sp+516#32) k=g k :=
        congrArg BitVec.toNat (HeadRegionFrame.offset lineMemory 516 2048 (by decide) (by decide) ⟨k,hk⟩)
      have addSpec : addHeader (bytes mid (sp+516#32)) f i ne vs ve le minor 1024=addHeader g f i ne vs ve le minor 1024 := by
        rw [HeadActionSpec.factor,HeadActionSpec.factor,
          HeadActionCongr.action_congr (bytes mid (sp+516#32)) g f i ne vs ve le minor 1024 2048 (by omega) (by omega) agree]
      rw [addSpec] at post view
      have constantsAfter : HeadFieldsConstants.At d sp length minor :=
        HeadFieldsConstants.preserve constantsMid (fun r h => addFrame r (constants_safe r h).2)
      have finalFrame : HeadRegisterFrame.At c d writes := HeadRegisterFrame.trans lineFrame addFrame
      rw [HeadFieldsStepSpec.one,lineCase]
      dsimp only
      cases selected : addHeader g f i ne vs ve le minor 1024 with
      | bad status =>
        have got : d.pc=0x8000342c#32 ∧ d.get 1=BitVec.ofNat 32 status := by simpa only [HeadHeaderAdd.Post,selected] using post
        exact ⟨n+m,d,after,by omega,by omega,line.trans add,got,metadataAfter,constantsAfter,
          HeadFieldsStepFrame.after_add lineMemory addMemory,finalFrame,csr2.trans csr⟩
      | ok nextFields =>
        dsimp only
        have got : if le+2<cap then HeadFieldsRegs.At d sp (le+2) length minor nextFields else d.pc=0x800033ea#32 := by
          simpa only [HeadHeaderAdd.Post,selected] using post
        have newView : HeadFieldsView.At after sp nextFields := by simpa only [HeadHeaderActionView.stored,selected] using view
        by_cases again : le+2<cap
        · rw [ite_eq_left again]
          have nextRegs : HeadFieldsRegs.At d sp (le+2) length minor nextFields := by simpa only [again,ite_true] using got
          exact ⟨n+m,d,after,by omega,by omega,line.trans add,⟨nextRegs,newView⟩,metadataAfter,constantsAfter,
            HeadFieldsStepFrame.after_add lineMemory addMemory,finalFrame,csr2.trans csr⟩
        · rw [ite_eq_right again]
          have nextPC : d.pc=0x800033ea#32 := by simpa only [again,ite_false] using got
          exact ⟨n+m,d,after,by omega,by omega,line.trans add,nextPC,metadataAfter,constantsAfter,
            HeadFieldsStepFrame.after_add lineMemory addMemory,finalFrame,csr2.trans csr⟩
end E5R.Thermostat.HeadFieldsStep
