import Projects.thermostat.ChunkNextStores
import Projects.thermostat.MainCopyView
namespace E5R.Thermostat.ChunkNextStoreMemory
open E5R E5R.Thermostat

/-- Live App/RX/future objects lie between the local span stores and packed
    Next payload stores, so all their bytes are preserved. -/
theorem region (ram : Word → BitVec 8) (sp ms me ts te high0 high1 high2 : Word) (off size : Nat)
    (lo : 40≤off) (hi : off+size≤5168) :
    ViewFrame.Region ram (ChunkNextStores.memory ram sp ms me ts te high0 high1 high2) (sp+BitVec.ofNat 32 off) size := by
  intro i
  unfold ChunkNextStores.memory
  rw [StoreBytes.frame _ _ _ _ .h (fun j => by
    have hj : j.val<2 := j.isLt
    exact FrameOffsets.ne sp off 5172 i.val j.val (by have := i.isLt;omega) (by omega) (by have := i.isLt;omega))]
  rw [StoreBytes.frame _ _ _ _ .w (fun j => by
    have hj : j.val<4 := j.isLt
    exact FrameOffsets.ne sp off 5168 i.val j.val (by have := i.isLt;omega) (by omega) (by have := i.isLt;omega))]
  rw [StoreBytes.frame _ _ _ _ .w (fun j => by
    have hj : j.val<4 := j.isLt
    exact FrameOffsets.ne sp off 32 i.val j.val (by have := i.isLt;omega) (by omega) (by have := i.isLt;omega))]
  rw [StoreBytes.frame _ _ _ _ .w (fun j => by
    have hj : j.val<4 := j.isLt
    exact FrameOffsets.ne sp off 36 i.val j.val (by have := i.isLt;omega) (by omega) (by have := i.isLt;omega))]
  rw [StoreBytes.frame _ _ _ _ .w (fun j => by
    have hj : j.val<4 := j.isLt
    exact FrameOffsets.ne sp off 24 i.val j.val (by have := i.isLt;omega) (by omega) (by have := i.isLt;omega))]
  rw [StoreBytes.frame _ _ _ _ .w (fun j => by
    have hj : j.val<4 := j.isLt
    exact FrameOffsets.ne sp off 28 i.val j.val (by have := i.isLt;omega) (by omega) (by have := i.isLt;omega))]

theorem low (ram : Word → BitVec 8) (sp ms me ts te high0 high1 high2 : Word) (off size : Nat)
    (hi : off+size≤24) :
    ViewFrame.Region ram (ChunkNextStores.memory ram sp ms me ts te high0 high1 high2) (sp+BitVec.ofNat 32 off) size := by
  intro i
  unfold ChunkNextStores.memory
  rw [StoreBytes.frame _ _ _ _ .h (fun j => by
    have hj : j.val<2 := j.isLt
    exact FrameOffsets.ne sp off 5172 i.val j.val (by have := i.isLt;omega) (by omega) (by have := i.isLt;omega))]
  rw [StoreBytes.frame _ _ _ _ .w (fun j => by
    have hj : j.val<4 := j.isLt
    exact FrameOffsets.ne sp off 5168 i.val j.val (by have := i.isLt;omega) (by omega) (by have := i.isLt;omega))]
  rw [StoreBytes.frame _ _ _ _ .w (fun j => by
    have hj : j.val<4 := j.isLt
    exact FrameOffsets.ne sp off 32 i.val j.val (by have := i.isLt;omega) (by omega) (by have := i.isLt;omega))]
  rw [StoreBytes.frame _ _ _ _ .w (fun j => by
    have hj : j.val<4 := j.isLt
    exact FrameOffsets.ne sp off 36 i.val j.val (by have := i.isLt;omega) (by omega) (by have := i.isLt;omega))]
  rw [StoreBytes.frame _ _ _ _ .w (fun j => by
    have hj : j.val<4 := j.isLt
    exact FrameOffsets.ne sp off 24 i.val j.val (by have := i.isLt;omega) (by omega) (by have := i.isLt;omega))]
  rw [StoreBytes.frame _ _ _ _ .w (fun j => by
    have hj : j.val<4 := j.isLt
    exact FrameOffsets.ne sp off 28 i.val j.val (by have := i.isLt;omega) (by omega) (by have := i.isLt;omega))]

theorem head (ram : Word → BitVec 8) (sp ms me ts te high0 high1 high2 : Word) (value : HttpRequestSpec.Head)
    (view : HeadCompletedView.At ram (sp+3320#32) value) :
    HeadCompletedView.At (ChunkNextStores.memory ram sp ms me ts te high0 high1 high2) (sp+3320#32) value :=
  MainCopyView.head (region ram sp ms me ts te high0 high1 high2 3320 304 (by decide) (by decide)) value view
theorem methodStart (ram : Word → BitVec 8) (sp ms me ts te high0 high1 high2 : Word) :
    ramRead (ChunkNextStores.memory ram sp ms me ts te high0 high1 high2) (sp+28#32) .w=ms := by
  unfold ChunkNextStores.memory
  rw [FrameOffsets.word _ sp (high2) 28 5172 .h (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp (alu .or high0 (alu .sll high1 16#32)) 28 5168 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp (te) 28 32 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp (ts) 28 36 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp (me) 28 24 .w (by decide) (by decide) (by decide)]
  exact ramRead_ramWrite_w _ _ _

theorem methodEnd (ram : Word → BitVec 8) (sp ms me ts te high0 high1 high2 : Word) :
    ramRead (ChunkNextStores.memory ram sp ms me ts te high0 high1 high2) (sp+24#32) .w=me := by
  unfold ChunkNextStores.memory
  rw [FrameOffsets.word _ sp (high2) 24 5172 .h (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp (alu .or high0 (alu .sll high1 16#32)) 24 5168 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp (te) 24 32 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp (ts) 24 36 .w (by decide) (by decide) (by decide)]
  exact ramRead_ramWrite_w _ _ _

theorem targetStart (ram : Word → BitVec 8) (sp ms me ts te high0 high1 high2 : Word) :
    ramRead (ChunkNextStores.memory ram sp ms me ts te high0 high1 high2) (sp+36#32) .w=ts := by
  unfold ChunkNextStores.memory
  rw [FrameOffsets.word _ sp (high2) 36 5172 .h (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp (alu .or high0 (alu .sll high1 16#32)) 36 5168 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp (te) 36 32 .w (by decide) (by decide) (by decide)]
  exact ramRead_ramWrite_w _ _ _

theorem targetEnd (ram : Word → BitVec 8) (sp ms me ts te high0 high1 high2 : Word) :
    ramRead (ChunkNextStores.memory ram sp ms me ts te high0 high1 high2) (sp+32#32) .w=te := by
  unfold ChunkNextStores.memory
  rw [FrameOffsets.word _ sp (high2) 32 5172 .h (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp (alu .or high0 (alu .sll high1 16#32)) 32 5168 .w (by decide) (by decide) (by decide)]
  exact ramRead_ramWrite_w _ _ _

end E5R.Thermostat.ChunkNextStoreMemory
