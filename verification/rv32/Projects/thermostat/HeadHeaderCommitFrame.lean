import Projects.thermostat.HeadHeaderCommitMemory
import Projects.thermostat.HeadFieldsMetaFrame
import Projects.thermostat.HeadSavedTail
namespace E5R.Thermostat.HeadHeaderCommitFrame
open E5R E5R.Thermostat HttpRequestSpec

theorem values_region (ram : Word → BitVec 8) (sp : Word) (n : Nat) (h : Field) (off len : Nat) (hn : n<16)
    (hb : off+len≤4294967296) (hs : off+len≤64+16*n ∨ 72+16*n≤off) :
    ViewFrame.Region ram (HeadHeaderCommitMemory.values ram sp n h) (sp+BitVec.ofNat 32 off) len := by
  intro i
  have hi := i.isLt
  unfold HeadHeaderCommitMemory.values 
  rw [StoreBytes.frame _ _ _ _ .w (fun j => FrameOffsets.ne sp off (68+16*n) i.val j.val
    (by omega) (by have hj : j.val<4 := j.isLt;omega) (by have hj : j.val<4 := j.isLt;omega))]
  exact StoreBytes.frame _ _ _ _ .w (fun j => FrameOffsets.ne sp off (64+16*n) i.val j.val
    (by omega) (by have hj : j.val<4 := j.isLt;omega) (by have hj : j.val<4 := j.isLt;omega))

theorem values_word (ram : Word → BitVec 8) (sp : Word) (n : Nat) (h : Field) (off : Nat) (hn : n<16)
    (hb : off+4≤4294967296) (hs : off+4≤64+16*n ∨ 72+16*n≤off) :
    ramRead (HeadHeaderCommitMemory.values ram sp n h) (sp+BitVec.ofNat 32 off) .w=ramRead ram (sp+BitVec.ofNat 32 off) .w := by
  simpa only [BitVec.add_zero] using ViewFrame.word (values_region ram sp n h off 4 hn hb hs) 0 (by decide)

theorem names_region (ram : Word → BitVec 8) (sp : Word) (n : Nat) (h : Field) (off len : Nat) (hn : n<16)
    (hb : off+len≤4294967296) (hs : off+len≤56+16*n ∨ 72+16*n≤off) :
    ViewFrame.Region ram (HeadHeaderCommitMemory.names ram sp n h) (sp+BitVec.ofNat 32 off) len := by
  intro i
  have hi := i.isLt
  unfold HeadHeaderCommitMemory.names HeadHeaderCommitMemory.values
  rw [StoreBytes.frame _ _ _ _ .w (fun j => FrameOffsets.ne sp off (56+16*n) i.val j.val
    (by omega) (by have hj : j.val<4 := j.isLt;omega) (by have hj : j.val<4 := j.isLt;omega))]
  rw [StoreBytes.frame _ _ _ _ .w (fun j => FrameOffsets.ne sp off (68+16*n) i.val j.val
    (by omega) (by have hj : j.val<4 := j.isLt;omega) (by have hj : j.val<4 := j.isLt;omega))]
  exact StoreBytes.frame _ _ _ _ .w (fun j => FrameOffsets.ne sp off (64+16*n) i.val j.val
    (by omega) (by have hj : j.val<4 := j.isLt;omega) (by have hj : j.val<4 := j.isLt;omega))

theorem names_word (ram : Word → BitVec 8) (sp : Word) (n : Nat) (h : Field) (off : Nat) (hn : n<16)
    (hb : off+4≤4294967296) (hs : off+4≤56+16*n ∨ 72+16*n≤off) :
    ramRead (HeadHeaderCommitMemory.names ram sp n h) (sp+BitVec.ofNat 32 off) .w=ramRead ram (sp+BitVec.ofNat 32 off) .w := by
  simpa only [BitVec.add_zero] using ViewFrame.word (names_region ram sp n h off 4 hn hb hs) 0 (by decide)

theorem metadata {ram sp n h length cap} (room : n<16) (m : HeadFieldsMeta.At ram sp length cap) :
    HeadFieldsMeta.At (HeadHeaderCommitMemory.memory ram sp n h) sp length cap :=
  HeadFieldsMetaFrame.preserve m (HeadHeaderCommitMemory.region ram sp n h 8 48 room (by decide) (by omega) (by decide))

theorem saved {ram sp n h values} (room : n<16) (stored : HeadSaved.At ram sp values) :
    HeadSaved.At (HeadHeaderCommitMemory.memory ram sp n h) sp values :=
  HeadSavedTail.preserve stored (HeadHeaderCommitMemory.region ram sp n h 332 52 room (by decide) (by omega) (by decide))
end E5R.Thermostat.HeadHeaderCommitFrame
