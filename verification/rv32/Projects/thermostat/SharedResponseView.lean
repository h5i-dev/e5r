import Projects.thermostat.SharedResponseMemory
import Projects.thermostat.Send
import Projects.thermostat.ResponseWordBytes
namespace E5R.Thermostat.SharedResponseView
open E5R E5R.Thermostat

structure Descriptor (ram : Word → BitVec 8) (obj tx io ctptr : Word)
    (used status : Nat) (ct : List (BitVec 8)) (close head : Bool) : Prop where
  fresh : ram (obj+45#32)=0#8
  txWord : ramRead ram (obj+8#32) .w=tx
  capacity : ramRead ram (obj+12#32) .w=1024#32
  ioWord : ramRead ram (obj+24#32) .w=io
  ctWord : ramRead ram (obj+28#32) .w=ctptr
  ctLength : ramRead ram (obj+32#32) .w=BitVec.ofNat 32 ct.length
  bodyLength : ramRead ram (obj+36#32) .w=BitVec.ofNat 32 used
  statusWord : extend .h false (ramRead ram (obj+40#32) .h)=BitVec.ofNat 32 status
  closeWord : extend .b false (ramRead ram (obj+42#32) .b)=ResponseHeadBodyMath.boolWord close
  headWord : extend .b false (ramRead ram (obj+46#32) .b)=ResponseHeadBodyMath.boolWord head

/-- Byte view of the object actually written by the common response builder. -/
theorem cell {ram fp io0 io1 io2 saved status mimeLength mime close methodMinus used}
    (h : SharedResponseMemory.At ram fp io0 io1 io2 saved status mimeLength mime close methodMinus used)
    (off : Fin 40) (v : BitVec 8) (hv : SharedResponseMemory.liveByte io0 io1 io2 saved status mimeLength mime close methodMinus used off=some v) :
    ram ((fp+100#32)+BitVec.ofNat 32 (8+off.val))=v := by
  have hh := h off v hv
  have he : (fp+100#32)+BitVec.ofNat 32 (8+off.val)=(fp+108#32)+BitVec.ofNat 32 off.val := by
    simp only [BitVec.add_assoc,←BitVec.ofNat_add]
    congr 1
    congr 1
    omega
  rw [he]
  exact hh

/-- The real common-handler stores establish every fresh send descriptor
    field, including IO/buffer metadata, canonical flags and the initial tag. -/
theorem descriptor {ram fp tx io saved ctptr methodMinus} (used status : Nat) (ct : List (BitVec 8)) (close head : Bool)
    (hstatus : status≤599) (hhead : alu .sltu methodMinus 1#32=ResponseHeadBodyMath.boolWord head)
    (h : SharedResponseMemory.At ram fp tx 1024#32 io saved (BitVec.ofNat 32 status) (BitVec.ofNat 32 ct.length) ctptr
      (ResponseHeadBodyMath.boolWord close) methodMinus (BitVec.ofNat 32 used)) :
    Descriptor ram (fp+100#32) tx io ctptr used status ct close head := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · exact cell h ⟨37,by decide⟩ 0#8 (by rfl)
  · apply ResponseWordBytes.word
    intro i
    have hi := i.isLt
    have hh := cell h ⟨0+i.val,by omega⟩ (byteOf (tx) i.val) (by
      have hc : i.val=0 ∨ i.val=1 ∨ i.val=2 ∨ i.val=3 := by omega
      rcases hc with e|e|e|e <;> simp [SharedResponseMemory.liveByte,e])
    have he : ((fp+100#32)+8#32)+BitVec.ofNat 32 i.val=(fp+100#32)+BitVec.ofNat 32 (8+(0+i.val)) := by
      simp only [BitVec.add_assoc,←BitVec.ofNat_add]
      congr 1
      congr 1
      omega
    rw [he]
    exact hh
  · apply ResponseWordBytes.word
    intro i
    have hi := i.isLt
    have hh := cell h ⟨4+i.val,by omega⟩ (byteOf (1024#32) i.val) (by
      have hc : i.val=0 ∨ i.val=1 ∨ i.val=2 ∨ i.val=3 := by omega
      rcases hc with e|e|e|e <;> simp [SharedResponseMemory.liveByte,e])
    have he : ((fp+100#32)+12#32)+BitVec.ofNat 32 i.val=(fp+100#32)+BitVec.ofNat 32 (8+(4+i.val)) := by
      simp only [BitVec.add_assoc,←BitVec.ofNat_add]
      congr 1
      congr 1
      omega
    rw [he]
    exact hh
  · apply ResponseWordBytes.word
    intro i
    have hi := i.isLt
    have hh := cell h ⟨16+i.val,by omega⟩ (byteOf (io) i.val) (by
      have hc : i.val=0 ∨ i.val=1 ∨ i.val=2 ∨ i.val=3 := by omega
      rcases hc with e|e|e|e <;> simp [SharedResponseMemory.liveByte,e])
    have he : ((fp+100#32)+24#32)+BitVec.ofNat 32 i.val=(fp+100#32)+BitVec.ofNat 32 (8+(16+i.val)) := by
      simp only [BitVec.add_assoc,←BitVec.ofNat_add]
      congr 1
      congr 1
      omega
    rw [he]
    exact hh
  · apply ResponseWordBytes.word
    intro i
    have hi := i.isLt
    have hh := cell h ⟨20+i.val,by omega⟩ (byteOf (ctptr) i.val) (by
      have hc : i.val=0 ∨ i.val=1 ∨ i.val=2 ∨ i.val=3 := by omega
      rcases hc with e|e|e|e <;> simp [SharedResponseMemory.liveByte,e])
    have he : ((fp+100#32)+28#32)+BitVec.ofNat 32 i.val=(fp+100#32)+BitVec.ofNat 32 (8+(20+i.val)) := by
      simp only [BitVec.add_assoc,←BitVec.ofNat_add]
      congr 1
      congr 1
      omega
    rw [he]
    exact hh
  · apply ResponseWordBytes.word
    intro i
    have hi := i.isLt
    have hh := cell h ⟨24+i.val,by omega⟩ (byteOf (BitVec.ofNat 32 ct.length) i.val) (by
      have hc : i.val=0 ∨ i.val=1 ∨ i.val=2 ∨ i.val=3 := by omega
      rcases hc with e|e|e|e <;> simp [SharedResponseMemory.liveByte,e])
    have he : ((fp+100#32)+32#32)+BitVec.ofNat 32 i.val=(fp+100#32)+BitVec.ofNat 32 (8+(24+i.val)) := by
      simp only [BitVec.add_assoc,←BitVec.ofNat_add]
      congr 1
      congr 1
      omega
    rw [he]
    exact hh
  · apply ResponseWordBytes.word
    intro i
    have hi := i.isLt
    have hh := cell h ⟨28+i.val,by omega⟩ (byteOf (BitVec.ofNat 32 used) i.val) (by
      have hc : i.val=0 ∨ i.val=1 ∨ i.val=2 ∨ i.val=3 := by omega
      rcases hc with e|e|e|e <;> simp [SharedResponseMemory.liveByte,e])
    have he : ((fp+100#32)+36#32)+BitVec.ofNat 32 i.val=(fp+100#32)+BitVec.ofNat 32 (8+(28+i.val)) := by
      simp only [BitVec.add_assoc,←BitVec.ofNat_add]
      congr 1
      congr 1
      omega
    rw [he]
    exact hh
  · apply ResponseWordBytes.half
    · rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega : status<2^32)]
      omega
    · intro i
      have hi := i.isLt
      have hh := cell h ⟨32+i.val,by omega⟩ (byteOf (BitVec.ofNat 32 status) i.val) (by
        have hc : i.val=0 ∨ i.val=1 := by omega
        rcases hc with e|e <;> simp [SharedResponseMemory.liveByte,e])
      have he : ((fp+100#32)+40#32)+BitVec.ofNat 32 i.val=(fp+100#32)+BitVec.ofNat 32 (8+(32+i.val)) := by
        simp only [BitVec.add_assoc,←BitVec.ofNat_add]
        congr 1
        congr 1
        omega
      rw [he]
      exact hh
  · rw [Memory.load_byte]
    have hh := cell h ⟨34,by decide⟩ (byteOf (ResponseHeadBodyMath.boolWord close) 0) (by rfl)
    change ram ((fp+100#32)+42#32)=_ at hh
    rw [hh]
    cases close <;> rfl
  · rw [Memory.load_byte]
    have hh := cell h ⟨38,by decide⟩ (byteOf (alu .sltu methodMinus 1#32) 0) (by rfl)
    change ram ((fp+100#32)+46#32)=_ at hh
    rw [hh,hhead]
    cases head <;> rfl
end E5R.Thermostat.SharedResponseView
