import Projects.thermostat.HeadReject400
import Projects.thermostat.HeadReject414
import Projects.thermostat.HeadResultFrame
import Projects.thermostat.HeadReturn
namespace E5R.Thermostat.HeadEarlyFinish
open E5R E5R.Thermostat HttpRequestSpec

inductive Kind where
  | incomplete | bad | tooLong
  deriving DecidableEq

def out : Kind → HeadR
  | .incomplete => .incomplete
  | .bad => .reject 400
  | .tooLong => .reject 414

def entry : Kind → Word
  | .incomplete => 0x80002cea#32
  | .bad => 0x80002d5a#32
  | .tooLong => 0x80002d52#32

def memory (ram : Word → BitVec 8) (sp : Word) : Kind → Word → BitVec 8
  | .incomplete => HeadIncomplete.memory ram (sp+4904#32)
  | .bad => HeadResultStore.memory ram (sp+4904#32) 4#32 400#32
  | .tooLong => HeadResultStore.memory ram (sp+4904#32) 4#32 414#32

theorem result (ram : Word → BitVec 8) (sp : Word) (kind : Kind) :
    HeadResultView.At (memory ram sp kind) (sp+4904#32) (out kind) := by
  cases kind with
  | incomplete => exact HeadResultView.incomplete _ _
  | bad => exact HeadResultView.reject _ _ 400 (by decide)
  | tooLong => exact HeadResultView.reject _ _ 414 (by decide)

theorem saved {ram sp kind values} (h : HeadSaved.At ram sp values) :
    HeadSaved.At (memory ram sp kind) sp values := by
  cases kind with
  | incomplete => exact HeadResultFrame.incomplete_saved h
  | bad => exact HeadResultFrame.reject_saved h
  | tooLong => exact HeadResultFrame.reject_saved h

theorem region (ram : Word → BitVec 8) (sp : Word) (kind : Kind) (off len : Nat)
    (hb : off+len≤4294967296) (hs : off+len≤4904 ∨ 4916≤off) :
    ViewFrame.Region ram (memory ram sp kind) (sp+BitVec.ofNat 32 off) len := by
  cases kind with
  | incomplete => exact HeadResultFrame.incomplete_region _ _ _ _ hb hs
  | bad => exact HeadResultFrame.reject_region _ _ _ _ _ _ hb hs
  | tooLong => exact HeadResultFrame.reject_region _ _ _ _ _ _ hb hs

/-- The actual early result stores and full parser epilogue, including all
    thirteen saved ABI words and the caller's SP/return address. -/
theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (sp : Word) (values : Reg → Word) (kind : Kind)
    (hp : c.pc=entry kind) (h2 : c.get 2=sp) (h10 : c.get 10=sp+4904#32)
    (hm : Memory.Block B sp 5312) (ha : sp.toNat%4=0) (savedValues : HeadSaved.At ram sp values) :
    ∃ n d, 19≤n ∧ n≤21 ∧ Quiet.Steps B img n ⟨c,ram⟩ ⟨d,memory ram sp kind⟩ ∧
      d.pc=values 1 &&& ~~~1 ∧ d.get 2=sp+384#32 ∧ HeadSaved.CoreAt d values ∧ d.sameCsr c := by
  have dstBlock : Memory.Block B (sp+4904#32) 12 := Memory.sub_block hm (off := 4904) (by decide) (by decide)
  have dstAlign : (sp+4904#32).toNat%4=0 := Memory.word_aligned sp 1226 ha
  have stack : Memory.Block B sp 384 := by
    simpa only [BitVec.add_zero] using Memory.sub_block hm (off := 0) (m := 384) (by decide) (by decide)
  cases kind with
  | incomplete =>
    obtain ⟨a,emit,pc,tag,frame,csr⟩ := HeadIncomplete.contract B c ram (sp+4904#32) h10 dstBlock dstAlign hp
    obtain ⟨d,ret,endPC,endSP,abi,rest,csr2⟩ := HeadReturn.contract B a (memory ram sp .incomplete) sp values pc
      ((frame 2 (by decide)).trans h2) stack ha (saved savedValues)
    exact ⟨19,d,by decide,by decide,emit.trans ret,endPC,endSP,abi,csr2.trans csr⟩
  | bad =>
    obtain ⟨a,setup,pc,tag,status,frame,csr⟩ := HeadReject400.contract B c ram hp
    obtain ⟨b,emit,pc2,frame2,csr2⟩ := HeadResultStore.contract B a ram (sp+4904#32) 4#32 400#32
      ((frame 10 (by decide) (by decide)).trans h10) tag status dstBlock dstAlign pc
    obtain ⟨d,ret,endPC,endSP,abi,rest,csr3⟩ := HeadReturn.contract B b (memory ram sp .bad) sp values pc2
      ((frame2 2).trans ((frame 2 (by decide) (by decide)).trans h2)) stack ha (saved savedValues)
    exact ⟨20,d,by decide,by decide,(setup.trans emit).trans ret,endPC,endSP,abi,csr3.trans (csr2.trans csr)⟩
  | tooLong =>
    obtain ⟨a,setup,pc,tag,status,frame,csr⟩ := HeadReject414.contract B c ram hp
    obtain ⟨b,emit,pc2,frame2,csr2⟩ := HeadResultStore.contract B a ram (sp+4904#32) 4#32 414#32
      ((frame 10 (by decide) (by decide)).trans h10) tag status dstBlock dstAlign pc
    obtain ⟨d,ret,endPC,endSP,abi,rest,csr3⟩ := HeadReturn.contract B b (memory ram sp .tooLong) sp values pc2
      ((frame2 2).trans ((frame 2 (by decide) (by decide)).trans h2)) stack ha (saved savedValues)
    exact ⟨21,d,by decide,by decide,(setup.trans emit).trans ret,endPC,endSP,abi,csr3.trans (csr2.trans csr)⟩

theorem app (ram : Word → BitVec 8) (kind : Kind) (state : Spec.Snapshot) (h : AppState.At ram state) :
    AppState.At (memory ram 0x80ffea10#32 kind) state := by
  apply AppState.preserve ram _ state h
  have frame := region ram 0x80ffea10#32 kind 428 25 (by decide) (by decide)
  have base : 0x80ffea10#32+428#32=0x80ffebbc#32 := by decide +kernel
  simpa only [ViewFrame.Region,base] using frame
end E5R.Thermostat.HeadEarlyFinish
