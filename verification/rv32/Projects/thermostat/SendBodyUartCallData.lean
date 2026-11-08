import Projects.thermostat.SendBodyUartCall
import Projects.thermostat.StoreRead
set_option maxRecDepth 5000
set_option maxHeartbeats 2000000
namespace E5R.Thermostat.SendBodyUartCallData
open E5R E5R.Thermostat

theorem slot48 (ram : Word → BitVec 8) (obj io src : Word) (len : Nat) :
    ramRead (SendBodyUartCall.memory ram obj io src len) (obj+48#32) .w=io := by
  unfold SendBodyUartCall.memory
  rw [StoreRead.other _ (obj+48#32) (obj+88#32) (0#32) .w .b (StoreWords.offsets obj 48 4 88 1 (by decide) (by decide) (by decide))]
  rw [StoreRead.other _ (obj+48#32) (obj+56#32) (BitVec.ofNat 32 len) .w .w (StoreWords.offsets obj 48 4 56 4 (by decide) (by decide) (by decide))]
  rw [StoreRead.other _ (obj+48#32) (obj+52#32) (src) .w .w (StoreWords.offsets obj 48 4 52 4 (by decide) (by decide) (by decide))]
  exact ramRead_ramWrite_w _ _ _

theorem slot52 (ram : Word → BitVec 8) (obj io src : Word) (len : Nat) :
    ramRead (SendBodyUartCall.memory ram obj io src len) (obj+52#32) .w=src := by
  unfold SendBodyUartCall.memory
  rw [StoreRead.other _ (obj+52#32) (obj+88#32) (0#32) .w .b (StoreWords.offsets obj 52 4 88 1 (by decide) (by decide) (by decide))]
  rw [StoreRead.other _ (obj+52#32) (obj+56#32) (BitVec.ofNat 32 len) .w .w (StoreWords.offsets obj 52 4 56 4 (by decide) (by decide) (by decide))]
  exact ramRead_ramWrite_w _ _ _

theorem slot56 (ram : Word → BitVec 8) (obj io src : Word) (len : Nat) :
    ramRead (SendBodyUartCall.memory ram obj io src len) (obj+56#32) .w=BitVec.ofNat 32 len := by
  unfold SendBodyUartCall.memory
  rw [StoreRead.other _ (obj+56#32) (obj+88#32) (0#32) .w .b (StoreWords.offsets obj 56 4 88 1 (by decide) (by decide) (by decide))]
  exact ramRead_ramWrite_w _ _ _

theorem slot88 (ram : Word → BitVec 8) (obj io src : Word) (len : Nat) :
    SendBodyUartCall.memory ram obj io src len (obj+88#32)=byteOf (0#32) 0 := by
  unfold SendBodyUartCall.memory
  change ramPut _ _ _ _ = _
  exact ramPut_eq _ _ _

theorem frame (ram : Word → BitVec 8) (obj io src : Word) (len : Nat) (x : Word)
    (hx : ∀ i : Fin 89, x≠obj+BitVec.ofNat 32 i.val) : SendBodyUartCall.memory ram obj io src len x=ram x := by
  unfold SendBodyUartCall.memory
  rw [StoreBytes.frame _ (obj+88#32) (0#32) x .b (by intro i;have hi : i.val<1 := i.isLt;rw [BitVec.add_assoc,←BitVec.ofNat_add];exact hx ⟨88+i.val,by omega⟩)]
  rw [StoreBytes.frame _ (obj+56#32) (BitVec.ofNat 32 len) x .w (by intro i;have hi : i.val<4 := i.isLt;rw [BitVec.add_assoc,←BitVec.ofNat_add];exact hx ⟨56+i.val,by omega⟩)]
  rw [StoreBytes.frame _ (obj+52#32) (src) x .w (by intro i;have hi : i.val<4 := i.isLt;rw [BitVec.add_assoc,←BitVec.ofNat_add];exact hx ⟨52+i.val,by omega⟩)]
  rw [StoreBytes.frame _ (obj+48#32) (io) x .w (by intro i;have hi : i.val<4 := i.isLt;rw [BitVec.add_assoc,←BitVec.ofNat_add];exact hx ⟨48+i.val,by omega⟩)]

theorem prefixRegion (ram : Word → BitVec 8) (obj io src : Word) (len : Nat) :
    ViewFrame.Region ram (SendBodyUartCall.memory ram obj io src len) obj 48 := by
  intro i
  unfold SendBodyUartCall.memory
  rw [StoreBytes.frame _ (obj+88#32) (0#32) (obj+BitVec.ofNat 32 i.val) .b (by
    have hh := StoreWords.offsets obj 0 48 88 1 (by decide) (by decide) (by decide) i
    simpa only [Width.bytes,BitVec.add_zero] using hh)]
  rw [StoreBytes.frame _ (obj+56#32) (BitVec.ofNat 32 len) (obj+BitVec.ofNat 32 i.val) .w (by
    have hh := StoreWords.offsets obj 0 48 56 4 (by decide) (by decide) (by decide) i
    simpa only [Width.bytes,BitVec.add_zero] using hh)]
  rw [StoreBytes.frame _ (obj+52#32) (src) (obj+BitVec.ofNat 32 i.val) .w (by
    have hh := StoreWords.offsets obj 0 48 52 4 (by decide) (by decide) (by decide) i
    simpa only [Width.bytes,BitVec.add_zero] using hh)]
  rw [StoreBytes.frame _ (obj+48#32) (io) (obj+BitVec.ofNat 32 i.val) .w (by
    have hh := StoreWords.offsets obj 0 48 48 4 (by decide) (by decide) (by decide) i
    simpa only [Width.bytes,BitVec.add_zero] using hh)]
end E5R.Thermostat.SendBodyUartCallData
