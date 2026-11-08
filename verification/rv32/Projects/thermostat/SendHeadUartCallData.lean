import Projects.thermostat.SendHeadUartCall
import Projects.thermostat.StoreRead
set_option maxRecDepth 5000
set_option maxHeartbeats 2000000
namespace E5R.Thermostat.SendHeadUartCallData
open E5R E5R.Thermostat

theorem slot20 (ram : Word → BitVec 8) (obj io src body flag : Word) (len : Nat) :
    ramRead (SendHeadUartCall.memory ram obj io src body flag len) (obj+20#32) .w=body := by
  unfold SendHeadUartCall.memory
  rw [StoreRead.other _ (obj+20#32) (obj+88#32) (0#32) .w .b (StoreWords.offsets obj 20 4 88 1 (by decide) (by decide) (by decide))]
  rw [StoreRead.other _ (obj+20#32) (obj+56#32) (BitVec.ofNat 32 len) .w .w (StoreWords.offsets obj 20 4 56 4 (by decide) (by decide) (by decide))]
  rw [StoreRead.other _ (obj+20#32) (obj+52#32) (src) .w .w (StoreWords.offsets obj 20 4 52 4 (by decide) (by decide) (by decide))]
  rw [StoreRead.other _ (obj+20#32) (obj+48#32) (io) .w .w (StoreWords.offsets obj 20 4 48 4 (by decide) (by decide) (by decide))]
  rw [StoreRead.other _ (obj+20#32) (obj+44#32) (flag) .w .b (StoreWords.offsets obj 20 4 44 1 (by decide) (by decide) (by decide))]
  exact ramRead_ramWrite_w _ _ _

theorem slot44 (ram : Word → BitVec 8) (obj io src body flag : Word) (len : Nat) :
    SendHeadUartCall.memory ram obj io src body flag len (obj+44#32)=byteOf (flag) 0 := by
  unfold SendHeadUartCall.memory
  rw [StoreBytes.frame _ (obj+88#32) (0#32) (obj+44#32) .b (by
    intro i
    have hh := StoreWords.offsets obj 44 1 88 1 (by decide) (by decide) (by decide) ⟨0,by decide⟩ i
    simpa only [Width.bytes,BitVec.add_zero] using hh)]
  rw [StoreBytes.frame _ (obj+56#32) (BitVec.ofNat 32 len) (obj+44#32) .w (by
    intro i
    have hh := StoreWords.offsets obj 44 1 56 4 (by decide) (by decide) (by decide) ⟨0,by decide⟩ i
    simpa only [Width.bytes,BitVec.add_zero] using hh)]
  rw [StoreBytes.frame _ (obj+52#32) (src) (obj+44#32) .w (by
    intro i
    have hh := StoreWords.offsets obj 44 1 52 4 (by decide) (by decide) (by decide) ⟨0,by decide⟩ i
    simpa only [Width.bytes,BitVec.add_zero] using hh)]
  rw [StoreBytes.frame _ (obj+48#32) (io) (obj+44#32) .w (by
    intro i
    have hh := StoreWords.offsets obj 44 1 48 4 (by decide) (by decide) (by decide) ⟨0,by decide⟩ i
    simpa only [Width.bytes,BitVec.add_zero] using hh)]
  change ramPut _ _ _ _ = _
  exact ramPut_eq _ _ _

theorem slot48 (ram : Word → BitVec 8) (obj io src body flag : Word) (len : Nat) :
    ramRead (SendHeadUartCall.memory ram obj io src body flag len) (obj+48#32) .w=io := by
  unfold SendHeadUartCall.memory
  rw [StoreRead.other _ (obj+48#32) (obj+88#32) (0#32) .w .b (StoreWords.offsets obj 48 4 88 1 (by decide) (by decide) (by decide))]
  rw [StoreRead.other _ (obj+48#32) (obj+56#32) (BitVec.ofNat 32 len) .w .w (StoreWords.offsets obj 48 4 56 4 (by decide) (by decide) (by decide))]
  rw [StoreRead.other _ (obj+48#32) (obj+52#32) (src) .w .w (StoreWords.offsets obj 48 4 52 4 (by decide) (by decide) (by decide))]
  exact ramRead_ramWrite_w _ _ _

theorem slot52 (ram : Word → BitVec 8) (obj io src body flag : Word) (len : Nat) :
    ramRead (SendHeadUartCall.memory ram obj io src body flag len) (obj+52#32) .w=src := by
  unfold SendHeadUartCall.memory
  rw [StoreRead.other _ (obj+52#32) (obj+88#32) (0#32) .w .b (StoreWords.offsets obj 52 4 88 1 (by decide) (by decide) (by decide))]
  rw [StoreRead.other _ (obj+52#32) (obj+56#32) (BitVec.ofNat 32 len) .w .w (StoreWords.offsets obj 52 4 56 4 (by decide) (by decide) (by decide))]
  exact ramRead_ramWrite_w _ _ _

theorem slot56 (ram : Word → BitVec 8) (obj io src body flag : Word) (len : Nat) :
    ramRead (SendHeadUartCall.memory ram obj io src body flag len) (obj+56#32) .w=BitVec.ofNat 32 len := by
  unfold SendHeadUartCall.memory
  rw [StoreRead.other _ (obj+56#32) (obj+88#32) (0#32) .w .b (StoreWords.offsets obj 56 4 88 1 (by decide) (by decide) (by decide))]
  exact ramRead_ramWrite_w _ _ _

theorem slot88 (ram : Word → BitVec 8) (obj io src body flag : Word) (len : Nat) :
    SendHeadUartCall.memory ram obj io src body flag len (obj+88#32)=byteOf (0#32) 0 := by
  unfold SendHeadUartCall.memory
  change ramPut _ _ _ _ = _
  exact ramPut_eq _ _ _

theorem frame (ram : Word → BitVec 8) (obj io src body flag : Word) (len : Nat) (x : Word)
    (hx : ∀ i : Fin 89, x≠obj+BitVec.ofNat 32 i.val) : SendHeadUartCall.memory ram obj io src body flag len x=ram x := by
  unfold SendHeadUartCall.memory
  rw [StoreBytes.frame _ (obj+88#32) (0#32) x .b (by intro i;have hi : i.val<1 := i.isLt;rw [BitVec.add_assoc,←BitVec.ofNat_add];exact hx ⟨88+i.val,by omega⟩)]
  rw [StoreBytes.frame _ (obj+56#32) (BitVec.ofNat 32 len) x .w (by intro i;have hi : i.val<4 := i.isLt;rw [BitVec.add_assoc,←BitVec.ofNat_add];exact hx ⟨56+i.val,by omega⟩)]
  rw [StoreBytes.frame _ (obj+52#32) (src) x .w (by intro i;have hi : i.val<4 := i.isLt;rw [BitVec.add_assoc,←BitVec.ofNat_add];exact hx ⟨52+i.val,by omega⟩)]
  rw [StoreBytes.frame _ (obj+48#32) (io) x .w (by intro i;have hi : i.val<4 := i.isLt;rw [BitVec.add_assoc,←BitVec.ofNat_add];exact hx ⟨48+i.val,by omega⟩)]
  rw [StoreBytes.frame _ (obj+44#32) (flag) x .b (by intro i;have hi : i.val<1 := i.isLt;rw [BitVec.add_assoc,←BitVec.ofNat_add];exact hx ⟨44+i.val,by omega⟩)]
  rw [StoreBytes.frame _ (obj+20#32) (body) x .w (by intro i;have hi : i.val<4 := i.isLt;rw [BitVec.add_assoc,←BitVec.ofNat_add];exact hx ⟨20+i.val,by omega⟩)]

theorem prefixRegion (ram : Word → BitVec 8) (obj io src body flag : Word) (len : Nat) :
    ViewFrame.Region ram (SendHeadUartCall.memory ram obj io src body flag len) obj 20 := by
  intro i
  unfold SendHeadUartCall.memory
  rw [StoreBytes.frame _ (obj+88#32) (0#32) (obj+BitVec.ofNat 32 i.val) .b (by
    have hh := StoreWords.offsets obj 0 20 88 1 (by decide) (by decide) (by decide) i
    simpa only [Width.bytes,BitVec.add_zero] using hh)]
  rw [StoreBytes.frame _ (obj+56#32) (BitVec.ofNat 32 len) (obj+BitVec.ofNat 32 i.val) .w (by
    have hh := StoreWords.offsets obj 0 20 56 4 (by decide) (by decide) (by decide) i
    simpa only [Width.bytes,BitVec.add_zero] using hh)]
  rw [StoreBytes.frame _ (obj+52#32) (src) (obj+BitVec.ofNat 32 i.val) .w (by
    have hh := StoreWords.offsets obj 0 20 52 4 (by decide) (by decide) (by decide) i
    simpa only [Width.bytes,BitVec.add_zero] using hh)]
  rw [StoreBytes.frame _ (obj+48#32) (io) (obj+BitVec.ofNat 32 i.val) .w (by
    have hh := StoreWords.offsets obj 0 20 48 4 (by decide) (by decide) (by decide) i
    simpa only [Width.bytes,BitVec.add_zero] using hh)]
  rw [StoreBytes.frame _ (obj+44#32) (flag) (obj+BitVec.ofNat 32 i.val) .b (by
    have hh := StoreWords.offsets obj 0 20 44 1 (by decide) (by decide) (by decide) i
    simpa only [Width.bytes,BitVec.add_zero] using hh)]
  rw [StoreBytes.frame _ (obj+20#32) (body) (obj+BitVec.ofNat 32 i.val) .w (by
    have hh := StoreWords.offsets obj 0 20 20 4 (by decide) (by decide) (by decide) i
    simpa only [Width.bytes,BitVec.add_zero] using hh)]
end E5R.Thermostat.SendHeadUartCallData
