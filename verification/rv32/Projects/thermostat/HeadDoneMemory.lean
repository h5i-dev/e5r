import Projects.thermostat.HeadDoneStore
import Projects.thermostat.FrameOffsets
import Projects.thermostat.ViewFrame
namespace E5R.Thermostat.HeadDoneMemory
open E5R E5R.Thermostat

theorem region (ram : Word → BitVec 8) (sp tag low high method targetStart targetEnd count length minor : Word) (off len : Nat) (bound : off+len≤5312)
    (beforeWords : off+len≤4904 ∨ 4936≤off) (afterWords : off+len≤5192 ∨ 5201≤off) :
    ViewFrame.Region ram (HeadDoneStore.memory ram sp tag low high method targetStart targetEnd count length minor) (sp+BitVec.ofNat 32 off) len := by
  intro i
  have hi := i.isLt
  unfold HeadDoneStore.memory
  simp only [BitVec.add_assoc,show 4904#32+0#32=4904#32 by decide +kernel,show 4904#32+4#32=4908#32 by decide +kernel,show 4904#32+8#32=4912#32 by decide +kernel,show 4904#32+12#32=4916#32 by decide +kernel,show 4904#32+16#32=4920#32 by decide +kernel,show 4904#32+20#32=4924#32 by decide +kernel,show 4904#32+24#32=4928#32 by decide +kernel,show 4904#32+28#32=4932#32 by decide +kernel,show 4904#32+288#32=5192#32 by decide +kernel,show 4904#32+292#32=5196#32 by decide +kernel,show 4904#32+296#32=5200#32 by decide +kernel]
  rw [←BitVec.add_assoc sp (BitVec.ofNat 32 off) (BitVec.ofNat 32 i.val)]
  rw [StoreBytes.frame _ _ _ _ .b (fun j => FrameOffsets.ne sp off 5200 i.val j.val
    (by omega) (by have hj : j.val<1 := j.isLt;omega) (by have hj : j.val<1 := j.isLt;rcases afterWords with h|h <;> omega))]
  rw [StoreBytes.frame _ _ _ _ .w (fun j => FrameOffsets.ne sp off 5196 i.val j.val
    (by omega) (by have hj : j.val<4 := j.isLt;omega) (by have hj : j.val<4 := j.isLt;rcases afterWords with h|h <;> omega))]
  rw [StoreBytes.frame _ _ _ _ .w (fun j => FrameOffsets.ne sp off 5192 i.val j.val
    (by omega) (by have hj : j.val<4 := j.isLt;omega) (by have hj : j.val<4 := j.isLt;rcases afterWords with h|h <;> omega))]
  rw [StoreBytes.frame _ _ _ _ .w (fun j => FrameOffsets.ne sp off 4932 i.val j.val
    (by omega) (by have hj : j.val<4 := j.isLt;omega) (by have hj : j.val<4 := j.isLt;rcases beforeWords with h|h <;> omega))]
  rw [StoreBytes.frame _ _ _ _ .w (fun j => FrameOffsets.ne sp off 4928 i.val j.val
    (by omega) (by have hj : j.val<4 := j.isLt;omega) (by have hj : j.val<4 := j.isLt;rcases beforeWords with h|h <;> omega))]
  rw [StoreBytes.frame _ _ _ _ .w (fun j => FrameOffsets.ne sp off 4924 i.val j.val
    (by omega) (by have hj : j.val<4 := j.isLt;omega) (by have hj : j.val<4 := j.isLt;rcases beforeWords with h|h <;> omega))]
  rw [StoreBytes.frame _ _ _ _ .w (fun j => FrameOffsets.ne sp off 4920 i.val j.val
    (by omega) (by have hj : j.val<4 := j.isLt;omega) (by have hj : j.val<4 := j.isLt;rcases beforeWords with h|h <;> omega))]
  rw [StoreBytes.frame _ _ _ _ .w (fun j => FrameOffsets.ne sp off 4916 i.val j.val
    (by omega) (by have hj : j.val<4 := j.isLt;omega) (by have hj : j.val<4 := j.isLt;rcases beforeWords with h|h <;> omega))]
  rw [StoreBytes.frame _ _ _ _ .w (fun j => FrameOffsets.ne sp off 4912 i.val j.val
    (by omega) (by have hj : j.val<4 := j.isLt;omega) (by have hj : j.val<4 := j.isLt;rcases beforeWords with h|h <;> omega))]
  rw [StoreBytes.frame _ _ _ _ .w (fun j => FrameOffsets.ne sp off 4908 i.val j.val
    (by omega) (by have hj : j.val<4 := j.isLt;omega) (by have hj : j.val<4 := j.isLt;rcases beforeWords with h|h <;> omega))]
  exact StoreBytes.frame _ _ _ _ .w (fun j => FrameOffsets.ne sp off 4904 i.val j.val
    (by omega) (by have hj : j.val<4 := j.isLt;omega) (by have hj : j.val<4 := j.isLt;rcases beforeWords with h|h <;> omega))

theorem tag_word (ram : Word → BitVec 8) (sp tag low high method targetStart targetEnd count length minor : Word) :
    ramRead (HeadDoneStore.memory ram sp tag low high method targetStart targetEnd count length minor) (sp+4904#32) .w=tag := by
  unfold HeadDoneStore.memory
  simp only [BitVec.add_assoc,show 4904#32+0#32=4904#32 by decide +kernel,show 4904#32+4#32=4908#32 by decide +kernel,show 4904#32+8#32=4912#32 by decide +kernel,show 4904#32+12#32=4916#32 by decide +kernel,show 4904#32+16#32=4920#32 by decide +kernel,show 4904#32+20#32=4924#32 by decide +kernel,show 4904#32+24#32=4928#32 by decide +kernel,show 4904#32+28#32=4932#32 by decide +kernel,show 4904#32+288#32=5192#32 by decide +kernel,show 4904#32+292#32=5196#32 by decide +kernel,show 4904#32+296#32=5200#32 by decide +kernel]
  rw [FrameOffsets.word _ sp (minor) 4904 5200 .b (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp (length) 4904 5196 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp (count) 4904 5192 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp (targetEnd) 4904 4932 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp (targetStart) 4904 4928 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp (method) 4904 4924 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp (0#32) 4904 4920 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp (high) 4904 4916 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp (low) 4904 4912 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp (0#32) 4904 4908 .w (by decide) (by decide) (by decide)]
  exact ramRead_ramWrite_w _ _ _

theorem pad_word (ram : Word → BitVec 8) (sp tag low high method targetStart targetEnd count length minor : Word) :
    ramRead (HeadDoneStore.memory ram sp tag low high method targetStart targetEnd count length minor) (sp+4908#32) .w=0#32 := by
  unfold HeadDoneStore.memory
  simp only [BitVec.add_assoc,show 4904#32+0#32=4904#32 by decide +kernel,show 4904#32+4#32=4908#32 by decide +kernel,show 4904#32+8#32=4912#32 by decide +kernel,show 4904#32+12#32=4916#32 by decide +kernel,show 4904#32+16#32=4920#32 by decide +kernel,show 4904#32+20#32=4924#32 by decide +kernel,show 4904#32+24#32=4928#32 by decide +kernel,show 4904#32+28#32=4932#32 by decide +kernel,show 4904#32+288#32=5192#32 by decide +kernel,show 4904#32+292#32=5196#32 by decide +kernel,show 4904#32+296#32=5200#32 by decide +kernel]
  rw [FrameOffsets.word _ sp (minor) 4908 5200 .b (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp (length) 4908 5196 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp (count) 4908 5192 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp (targetEnd) 4908 4932 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp (targetStart) 4908 4928 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp (method) 4908 4924 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp (0#32) 4908 4920 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp (high) 4908 4916 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp (low) 4908 4912 .w (by decide) (by decide) (by decide)]
  exact ramRead_ramWrite_w _ _ _

theorem low_word (ram : Word → BitVec 8) (sp tag low high method targetStart targetEnd count length minor : Word) :
    ramRead (HeadDoneStore.memory ram sp tag low high method targetStart targetEnd count length minor) (sp+4912#32) .w=low := by
  unfold HeadDoneStore.memory
  simp only [BitVec.add_assoc,show 4904#32+0#32=4904#32 by decide +kernel,show 4904#32+4#32=4908#32 by decide +kernel,show 4904#32+8#32=4912#32 by decide +kernel,show 4904#32+12#32=4916#32 by decide +kernel,show 4904#32+16#32=4920#32 by decide +kernel,show 4904#32+20#32=4924#32 by decide +kernel,show 4904#32+24#32=4928#32 by decide +kernel,show 4904#32+28#32=4932#32 by decide +kernel,show 4904#32+288#32=5192#32 by decide +kernel,show 4904#32+292#32=5196#32 by decide +kernel,show 4904#32+296#32=5200#32 by decide +kernel]
  rw [FrameOffsets.word _ sp (minor) 4912 5200 .b (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp (length) 4912 5196 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp (count) 4912 5192 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp (targetEnd) 4912 4932 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp (targetStart) 4912 4928 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp (method) 4912 4924 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp (0#32) 4912 4920 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp (high) 4912 4916 .w (by decide) (by decide) (by decide)]
  exact ramRead_ramWrite_w _ _ _

theorem high_word (ram : Word → BitVec 8) (sp tag low high method targetStart targetEnd count length minor : Word) :
    ramRead (HeadDoneStore.memory ram sp tag low high method targetStart targetEnd count length minor) (sp+4916#32) .w=high := by
  unfold HeadDoneStore.memory
  simp only [BitVec.add_assoc,show 4904#32+0#32=4904#32 by decide +kernel,show 4904#32+4#32=4908#32 by decide +kernel,show 4904#32+8#32=4912#32 by decide +kernel,show 4904#32+12#32=4916#32 by decide +kernel,show 4904#32+16#32=4920#32 by decide +kernel,show 4904#32+20#32=4924#32 by decide +kernel,show 4904#32+24#32=4928#32 by decide +kernel,show 4904#32+28#32=4932#32 by decide +kernel,show 4904#32+288#32=5192#32 by decide +kernel,show 4904#32+292#32=5196#32 by decide +kernel,show 4904#32+296#32=5200#32 by decide +kernel]
  rw [FrameOffsets.word _ sp (minor) 4916 5200 .b (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp (length) 4916 5196 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp (count) 4916 5192 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp (targetEnd) 4916 4932 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp (targetStart) 4916 4928 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp (method) 4916 4924 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp (0#32) 4916 4920 .w (by decide) (by decide) (by decide)]
  exact ramRead_ramWrite_w _ _ _

theorem methodStart_word (ram : Word → BitVec 8) (sp tag low high method targetStart targetEnd count length minor : Word) :
    ramRead (HeadDoneStore.memory ram sp tag low high method targetStart targetEnd count length minor) (sp+4920#32) .w=0#32 := by
  unfold HeadDoneStore.memory
  simp only [BitVec.add_assoc,show 4904#32+0#32=4904#32 by decide +kernel,show 4904#32+4#32=4908#32 by decide +kernel,show 4904#32+8#32=4912#32 by decide +kernel,show 4904#32+12#32=4916#32 by decide +kernel,show 4904#32+16#32=4920#32 by decide +kernel,show 4904#32+20#32=4924#32 by decide +kernel,show 4904#32+24#32=4928#32 by decide +kernel,show 4904#32+28#32=4932#32 by decide +kernel,show 4904#32+288#32=5192#32 by decide +kernel,show 4904#32+292#32=5196#32 by decide +kernel,show 4904#32+296#32=5200#32 by decide +kernel]
  rw [FrameOffsets.word _ sp (minor) 4920 5200 .b (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp (length) 4920 5196 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp (count) 4920 5192 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp (targetEnd) 4920 4932 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp (targetStart) 4920 4928 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp (method) 4920 4924 .w (by decide) (by decide) (by decide)]
  exact ramRead_ramWrite_w _ _ _

theorem methodEnd_word (ram : Word → BitVec 8) (sp tag low high method targetStart targetEnd count length minor : Word) :
    ramRead (HeadDoneStore.memory ram sp tag low high method targetStart targetEnd count length minor) (sp+4924#32) .w=method := by
  unfold HeadDoneStore.memory
  simp only [BitVec.add_assoc,show 4904#32+0#32=4904#32 by decide +kernel,show 4904#32+4#32=4908#32 by decide +kernel,show 4904#32+8#32=4912#32 by decide +kernel,show 4904#32+12#32=4916#32 by decide +kernel,show 4904#32+16#32=4920#32 by decide +kernel,show 4904#32+20#32=4924#32 by decide +kernel,show 4904#32+24#32=4928#32 by decide +kernel,show 4904#32+28#32=4932#32 by decide +kernel,show 4904#32+288#32=5192#32 by decide +kernel,show 4904#32+292#32=5196#32 by decide +kernel,show 4904#32+296#32=5200#32 by decide +kernel]
  rw [FrameOffsets.word _ sp (minor) 4924 5200 .b (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp (length) 4924 5196 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp (count) 4924 5192 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp (targetEnd) 4924 4932 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp (targetStart) 4924 4928 .w (by decide) (by decide) (by decide)]
  exact ramRead_ramWrite_w _ _ _

theorem targetStart_word (ram : Word → BitVec 8) (sp tag low high method targetStart targetEnd count length minor : Word) :
    ramRead (HeadDoneStore.memory ram sp tag low high method targetStart targetEnd count length minor) (sp+4928#32) .w=targetStart := by
  unfold HeadDoneStore.memory
  simp only [BitVec.add_assoc,show 4904#32+0#32=4904#32 by decide +kernel,show 4904#32+4#32=4908#32 by decide +kernel,show 4904#32+8#32=4912#32 by decide +kernel,show 4904#32+12#32=4916#32 by decide +kernel,show 4904#32+16#32=4920#32 by decide +kernel,show 4904#32+20#32=4924#32 by decide +kernel,show 4904#32+24#32=4928#32 by decide +kernel,show 4904#32+28#32=4932#32 by decide +kernel,show 4904#32+288#32=5192#32 by decide +kernel,show 4904#32+292#32=5196#32 by decide +kernel,show 4904#32+296#32=5200#32 by decide +kernel]
  rw [FrameOffsets.word _ sp (minor) 4928 5200 .b (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp (length) 4928 5196 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp (count) 4928 5192 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp (targetEnd) 4928 4932 .w (by decide) (by decide) (by decide)]
  exact ramRead_ramWrite_w _ _ _

theorem targetEnd_word (ram : Word → BitVec 8) (sp tag low high method targetStart targetEnd count length minor : Word) :
    ramRead (HeadDoneStore.memory ram sp tag low high method targetStart targetEnd count length minor) (sp+4932#32) .w=targetEnd := by
  unfold HeadDoneStore.memory
  simp only [BitVec.add_assoc,show 4904#32+0#32=4904#32 by decide +kernel,show 4904#32+4#32=4908#32 by decide +kernel,show 4904#32+8#32=4912#32 by decide +kernel,show 4904#32+12#32=4916#32 by decide +kernel,show 4904#32+16#32=4920#32 by decide +kernel,show 4904#32+20#32=4924#32 by decide +kernel,show 4904#32+24#32=4928#32 by decide +kernel,show 4904#32+28#32=4932#32 by decide +kernel,show 4904#32+288#32=5192#32 by decide +kernel,show 4904#32+292#32=5196#32 by decide +kernel,show 4904#32+296#32=5200#32 by decide +kernel]
  rw [FrameOffsets.word _ sp (minor) 4932 5200 .b (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp (length) 4932 5196 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp (count) 4932 5192 .w (by decide) (by decide) (by decide)]
  exact ramRead_ramWrite_w _ _ _

theorem count_word (ram : Word → BitVec 8) (sp tag low high method targetStart targetEnd count length minor : Word) :
    ramRead (HeadDoneStore.memory ram sp tag low high method targetStart targetEnd count length minor) (sp+5192#32) .w=count := by
  unfold HeadDoneStore.memory
  simp only [BitVec.add_assoc,show 4904#32+0#32=4904#32 by decide +kernel,show 4904#32+4#32=4908#32 by decide +kernel,show 4904#32+8#32=4912#32 by decide +kernel,show 4904#32+12#32=4916#32 by decide +kernel,show 4904#32+16#32=4920#32 by decide +kernel,show 4904#32+20#32=4924#32 by decide +kernel,show 4904#32+24#32=4928#32 by decide +kernel,show 4904#32+28#32=4932#32 by decide +kernel,show 4904#32+288#32=5192#32 by decide +kernel,show 4904#32+292#32=5196#32 by decide +kernel,show 4904#32+296#32=5200#32 by decide +kernel]
  rw [FrameOffsets.word _ sp (minor) 5192 5200 .b (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp (length) 5192 5196 .w (by decide) (by decide) (by decide)]
  exact ramRead_ramWrite_w _ _ _

theorem length_word (ram : Word → BitVec 8) (sp tag low high method targetStart targetEnd count length minor : Word) :
    ramRead (HeadDoneStore.memory ram sp tag low high method targetStart targetEnd count length minor) (sp+5196#32) .w=length := by
  unfold HeadDoneStore.memory
  simp only [BitVec.add_assoc,show 4904#32+0#32=4904#32 by decide +kernel,show 4904#32+4#32=4908#32 by decide +kernel,show 4904#32+8#32=4912#32 by decide +kernel,show 4904#32+12#32=4916#32 by decide +kernel,show 4904#32+16#32=4920#32 by decide +kernel,show 4904#32+20#32=4924#32 by decide +kernel,show 4904#32+24#32=4928#32 by decide +kernel,show 4904#32+28#32=4932#32 by decide +kernel,show 4904#32+288#32=5192#32 by decide +kernel,show 4904#32+292#32=5196#32 by decide +kernel,show 4904#32+296#32=5200#32 by decide +kernel]
  rw [FrameOffsets.word _ sp (minor) 5196 5200 .b (by decide) (by decide) (by decide)]
  exact ramRead_ramWrite_w _ _ _

theorem minor_byte (ram : Word → BitVec 8) (sp tag low high method targetStart targetEnd count length minor : Word) :
    HeadDoneStore.memory ram sp tag low high method targetStart targetEnd count length minor (sp+5200#32)=byteOf minor 0 := by
  unfold HeadDoneStore.memory
  simp only [BitVec.add_assoc,show 4904#32+0#32=4904#32 by decide +kernel,show 4904#32+4#32=4908#32 by decide +kernel,show 4904#32+8#32=4912#32 by decide +kernel,show 4904#32+12#32=4916#32 by decide +kernel,show 4904#32+16#32=4920#32 by decide +kernel,show 4904#32+20#32=4924#32 by decide +kernel,show 4904#32+24#32=4928#32 by decide +kernel,show 4904#32+28#32=4932#32 by decide +kernel,show 4904#32+288#32=5192#32 by decide +kernel,show 4904#32+292#32=5196#32 by decide +kernel,show 4904#32+296#32=5200#32 by decide +kernel,ramWrite,ramPut,ite_true]
end E5R.Thermostat.HeadDoneMemory
