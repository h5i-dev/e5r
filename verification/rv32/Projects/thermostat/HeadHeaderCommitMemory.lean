import Projects.thermostat.HeadFieldsView
import Projects.thermostat.HeaderSetup
namespace E5R.Thermostat.HeadHeaderCommitMemory
open E5R E5R.Thermostat HttpRequestSpec

def values (ram : Word → BitVec 8) (sp : Word) (n : Nat) (h : Field) :=
  ramWrite (ramWrite ram (sp+BitVec.ofNat 32 (64+16*n)) (BitVec.ofNat 32 h.vs) .w)
    (sp+BitVec.ofNat 32 (68+16*n)) (BitVec.ofNat 32 h.ve) .w

def names (ram : Word → BitVec 8) (sp : Word) (n : Nat) (h : Field) :=
  ramWrite (values ram sp n h) (sp+BitVec.ofNat 32 (56+16*n)) (BitVec.ofNat 32 h.ns) .w

/-- The five real stores at 33BC,33BE,33CC,33D2,33D4, in execution order. -/
def memory (ram : Word → BitVec 8) (sp : Word) (n : Nat) (h : Field) :=
  ramWrite (ramWrite (names ram sp n h) (sp+BitVec.ofNat 32 (60+16*n)) (BitVec.ofNat 32 h.ne) .w)
    (sp+320#32) (BitVec.ofNat 32 (n+1)) .w

theorem region (ram : Word → BitVec 8) (sp : Word) (n : Nat) (h : Field) (off len : Nat) (hn : n<16)
    (hb : off+len≤4294967296) (hs : off+len≤56+16*n ∨ 72+16*n≤off) (hc : off+len≤320 ∨ 324≤off) :
    ViewFrame.Region ram (memory ram sp n h) (sp+BitVec.ofNat 32 off) len := by
  intro i
  have hi := i.isLt
  have hbytes : Width.w.bytes=4 := rfl
  unfold memory names values
  rw [StoreBytes.frame _ _ _ _ .w (fun j => FrameOffsets.ne sp off (320) i.val j.val
    (by omega) (by have hj : j.val<4 := j.isLt;omega) (by have hj : j.val<4 := j.isLt;omega))]
  rw [StoreBytes.frame _ _ _ _ .w (fun j => FrameOffsets.ne sp off (60+16*n) i.val j.val
    (by omega) (by have hj : j.val<4 := j.isLt;omega) (by have hj : j.val<4 := j.isLt;omega))]
  rw [StoreBytes.frame _ _ _ _ .w (fun j => FrameOffsets.ne sp off (56+16*n) i.val j.val
    (by omega) (by have hj : j.val<4 := j.isLt;omega) (by have hj : j.val<4 := j.isLt;omega))]
  rw [StoreBytes.frame _ _ _ _ .w (fun j => FrameOffsets.ne sp off (68+16*n) i.val j.val
    (by omega) (by have hj : j.val<4 := j.isLt;omega) (by have hj : j.val<4 := j.isLt;omega))]
  exact StoreBytes.frame _ _ _ _ .w (fun j => FrameOffsets.ne sp off (64+16*n) i.val j.val
    (by omega) (by have hj : j.val<4 := j.isLt;omega) (by have hj : j.val<4 := j.isLt;omega))

theorem count_word (ram : Word → BitVec 8) (sp : Word) (n : Nat) (h : Field) :
    ramRead (memory ram sp n h) (sp+320#32) .w=BitVec.ofNat 32 (n+1) := ramRead_ramWrite_w _ _ _

theorem new_ns (ram : Word → BitVec 8) (sp : Word) (n : Nat) (h : Field) (hn : n<16) :
    ramRead (memory ram sp n h) (sp+BitVec.ofNat 32 (56+16*n)) .w=BitVec.ofNat 32 (h.ns) := by
  have hbytes : Width.w.bytes=4 := rfl
  unfold memory names values
  rw [FrameOffsets.word _ sp (BitVec.ofNat 32 (n+1)) (56+16*n) (320) .w (by omega) (by omega) (by omega)]
  rw [FrameOffsets.word _ sp (BitVec.ofNat 32 (h.ne)) (56+16*n) (60+16*n) .w (by omega) (by omega) (by omega)]
  exact ramRead_ramWrite_w _ _ _

theorem new_ne (ram : Word → BitVec 8) (sp : Word) (n : Nat) (h : Field) (hn : n<16) :
    ramRead (memory ram sp n h) (sp+BitVec.ofNat 32 (60+16*n)) .w=BitVec.ofNat 32 (h.ne) := by
  have hbytes : Width.w.bytes=4 := rfl
  unfold memory names values
  rw [FrameOffsets.word _ sp (BitVec.ofNat 32 (n+1)) (60+16*n) (320) .w (by omega) (by omega) (by omega)]
  exact ramRead_ramWrite_w _ _ _

theorem new_vs (ram : Word → BitVec 8) (sp : Word) (n : Nat) (h : Field) (hn : n<16) :
    ramRead (memory ram sp n h) (sp+BitVec.ofNat 32 (64+16*n)) .w=BitVec.ofNat 32 (h.vs) := by
  have hbytes : Width.w.bytes=4 := rfl
  unfold memory names values
  rw [FrameOffsets.word _ sp (BitVec.ofNat 32 (n+1)) (64+16*n) (320) .w (by omega) (by omega) (by omega)]
  rw [FrameOffsets.word _ sp (BitVec.ofNat 32 (h.ne)) (64+16*n) (60+16*n) .w (by omega) (by omega) (by omega)]
  rw [FrameOffsets.word _ sp (BitVec.ofNat 32 (h.ns)) (64+16*n) (56+16*n) .w (by omega) (by omega) (by omega)]
  rw [FrameOffsets.word _ sp (BitVec.ofNat 32 (h.ve)) (64+16*n) (68+16*n) .w (by omega) (by omega) (by omega)]
  exact ramRead_ramWrite_w _ _ _

theorem new_ve (ram : Word → BitVec 8) (sp : Word) (n : Nat) (h : Field) (hn : n<16) :
    ramRead (memory ram sp n h) (sp+BitVec.ofNat 32 (68+16*n)) .w=BitVec.ofNat 32 (h.ve) := by
  have hbytes : Width.w.bytes=4 := rfl
  unfold memory names values
  rw [FrameOffsets.word _ sp (BitVec.ofNat 32 (n+1)) (68+16*n) (320) .w (by omega) (by omega) (by omega)]
  rw [FrameOffsets.word _ sp (BitVec.ofNat 32 (h.ne)) (68+16*n) (60+16*n) .w (by omega) (by omega) (by omega)]
  rw [FrameOffsets.word _ sp (BitVec.ofNat 32 (h.ns)) (68+16*n) (56+16*n) .w (by omega) (by omega) (by omega)]
  exact ramRead_ramWrite_w _ _ _
end E5R.Thermostat.HeadHeaderCommitMemory
