import Projects.thermostat.MainHeadCopy304
import Projects.thermostat.MainBodyHeadLoad
import Projects.thermostat.MainHeaderLayoutParts
namespace E5R.Thermostat.MainBodyHeadMemory
open E5R E5R.Thermostat

def memory (ram : Word → BitVec 8) (sp : Word) (head : HttpRequestSpec.Head) :=
  MainBodyHeadLoad.memory (MainHeadCopy304.memory ram sp) (sp+3204#32) (BitVec.ofNat 32 head.len) (HeadCompletedView.framingTag head.framing)

theorem frame (ram : Word → BitVec 8) (sp : Word) (head : HttpRequestSpec.Head) (off len : Nat)
    (bound : off+len≤4928) (copyApart : off+len≤3320 ∨ 3624≤off) (storeApart : off+len≤3648 ∨ 3652≤off) :
    ViewFrame.Region ram (memory ram sp head) (sp+BitVec.ofNat 32 off) len := by
  have copy := MainHeadCopy304.frame ram sp off len bound copyApart
  intro i
  have store : memory ram sp head (sp+BitVec.ofNat 32 off+BitVec.ofNat 32 i.val)=
      MainHeadCopy304.memory ram sp (sp+BitVec.ofNat 32 off+BitVec.ofNat 32 i.val) := by
    unfold memory MainBodyHeadLoad.memory
    rw [BitVec.add_assoc,show 3204#32+444#32=3648#32 by decide +kernel]
    apply StoreBytes.frame
    intro j
    exact FrameOffsets.ne sp off 3648 i.val j.val (by have := i.isLt;omega)
      (by have := j.isLt;change j.val<4 at this;omega)
      (by have := i.isLt;have := j.isLt;change j.val<4 at this;rcases storeApart with h|h <;> omega)
  exact store.trans (copy i)

theorem head (ram : Word → BitVec 8) (sp : Word) (head : HttpRequestSpec.Head)
    (stack : Memory.Block B sp 4928) (view : HeadCompletedView.At ram (sp+4520#32) head) :
    HeadCompletedView.At (memory ram sp head) (sp+3320#32) head := by
  have copied := MainHeadCopy304.head ram sp head stack view
  apply MainCopyView.head (value := head) (view := copied)
  intro i
  unfold memory MainBodyHeadLoad.memory
  rw [BitVec.add_assoc,show 3204#32+444#32=3648#32 by decide +kernel]
  apply StoreBytes.frame
  intro j
  exact FrameOffsets.ne sp 3320 3648 i.val j.val (by have := i.isLt;omega)
    (by have := j.isLt;change j.val<4 at this;omega)
    (by have := i.isLt;have := j.isLt;change j.val<4 at this;omega)

theorem layout (ram : Word → BitVec 8) (head : HttpRequestSpec.Head) (filled : Nat) (h : MainHeaderLayout.At ram filled) :
    MainHeaderLayout.At (memory ram 0x80ffeb90#32 head) filled := by
  apply MainHeaderLayoutParts.preserve h
  · simpa only [show 0x80ffeb90#32+3204#32=0x80fff814#32 by decide +kernel] using frame ram 0x80ffeb90#32 head 3204 116 (by decide) (Or.inl (by decide)) (Or.inl (by decide))
  · simpa only [show 0x80ffeb90#32+3636#32=0x80fff814#32+432#32 by decide +kernel] using frame ram 0x80ffeb90#32 head 3636 12 (by decide) (Or.inr (by decide)) (Or.inl (by decide))

theorem consumed (ram : Word → BitVec 8) (sp : Word) (head : HttpRequestSpec.Head) :
    ramRead (memory ram sp head) ((sp+3204#32)+444#32) .w=BitVec.ofNat 32 head.len := ramRead_ramWrite_w _ _ _
end E5R.Thermostat.MainBodyHeadMemory
