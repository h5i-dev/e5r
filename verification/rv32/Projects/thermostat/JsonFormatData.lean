import Projects.thermostat.JsonProgram
import Projects.thermostat.RomSpan
import Projects.thermostat.UartPlatform
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
namespace E5R.Thermostat.JsonFormatData
open E5R E5R.Thermostat

def literalPointer (i : Fin 9) : Word := match i.val with
  | 0 => 0x8000574c#32
  | 1 => 0x8000575d#32
  | 2 => 0x8000576a#32
  | 3 => 0x80005776#32
  | 4 => 0x80005783#32
  | 5 => 0x80005786#32
  | 6 => 0x80005789#32
  | 7 => 0x8000578c#32
  | _ => 0x80005798#32

def tagPointer (i : Fin 18) : Word := match i.val with
  | 0 => 0x8000574b#32
  | 1 => 0x8000575b#32
  | 2 => 0x8000575c#32
  | 3 => 0x80005768#32
  | 4 => 0x80005769#32
  | 5 => 0x80005774#32
  | 6 => 0x80005775#32
  | 7 => 0x80005781#32
  | 8 => 0x80005782#32
  | 9 => 0x80005784#32
  | 10 => 0x80005785#32
  | 11 => 0x80005787#32
  | 12 => 0x80005788#32
  | 13 => 0x8000578a#32
  | 14 => 0x8000578b#32
  | 15 => 0x80005796#32
  | 16 => 0x80005797#32
  | _ => 0x8000579a#32

def tagByte (i : Fin 18) : BitVec 8 :=
  if i.val = 17 then 0#8 else if i.val%2 = 0 then
    BitVec.ofNat 8 (JsonProgram.literal ⟨i.val/2,by have := i.isLt;omega⟩).length else 192#8

theorem literal_data : ∀ i : Fin 9, ∀ j : Fin (JsonProgram.literal i).length,
    BitVec.ofNat 32 (PackedData.dataByte (literalPointer i+BitVec.ofNat 32 j.val).toNat) =
      BitVec.ofNat 32 (JsonProgram.literal i)[j.val].toNat := by decide +kernel

theorem literal_layout : ∀ i : Fin 9,
    (JsonProgram.literal i).length < 2^32 ∧ (literalPointer i).toNat+(JsonProgram.literal i).length ≤ 2^32 ∧
    ∀ j : Fin (JsonProgram.literal i).length,
      (0x800056a8 ≤ (literalPointer i+BitVec.ofNat 32 j.val).toNat ∧
       (literalPointer i+BitVec.ofNat 32 j.val).toNat < 0x80005f18) ∧
      UartPlatform.board.inRam (literalPointer i+BitVec.ofNat 32 j.val) 1 = false := by
  unfold UartPlatform.board
  rw [ThermostatImage.image_rwBase]
  decide +kernel

theorem literal_span (i : Fin 9) (ram : Word → BitVec 8) :
    ReadBytes.Span UartPlatform.board img ram (literalPointer i) (JsonProgram.literal i) :=
  ReadBytes.of_data _ _ _ _ (literal_layout i).1 (literal_layout i).2.1
    (fun j => ((literal_layout i).2.2 j).1) (fun j => ((literal_layout i).2.2 j).2) (literal_data i)

theorem descriptor_data : ∀ i : Fin JsonProgram.descriptor.length,
    BitVec.ofNat 32 (PackedData.dataByte (0x8000574b#32+BitVec.ofNat 32 i.val).toNat) =
      BitVec.ofNat 32 JsonProgram.descriptor[i.val].toNat := by decide +kernel

theorem descriptor_outside : ∀ i : Fin JsonProgram.descriptor.length,
    UartPlatform.board.inRam (0x8000574b#32+BitVec.ofNat 32 i.val) 1 = false := by
  unfold UartPlatform.board;rw [ThermostatImage.image_rwBase];decide +kernel

theorem descriptor_span (ram : Word → BitVec 8) : ReadBytes.Span UartPlatform.board img ram 0x8000574b#32 JsonProgram.descriptor := by
  apply ReadBytes.of_data
  · rw [JsonProgram.descriptor_length];decide
  · rw [JsonProgram.descriptor_length];decide +kernel
  · intro i
    have hi := i.isLt
    have hlen := JsonProgram.descriptor_length
    simp only [BitVec.toNat_add,BitVec.toNat_ofNat]
    omega
  · exact descriptor_outside
  · exact descriptor_data

theorem tag_data : ∀ i : Fin 18,
    BitVec.ofNat 32 (PackedData.dataByte (tagPointer i).toNat) = BitVec.ofNat 32 (tagByte i).toNat := by decide +kernel

theorem tag_layout : ∀ i : Fin 18, 0x800056a8 ≤ (tagPointer i).toNat ∧ (tagPointer i).toNat < 0x80005f18 ∧
    UartPlatform.board.inRam (tagPointer i) 1 = false := by
  unfold UartPlatform.board;rw [ThermostatImage.image_rwBase];decide +kernel

theorem tag (i : Fin 18) (ram : Word → BitVec 8) : ReadBytes.Byte UartPlatform.board img ram (tagPointer i) (tagByte i) := by
  apply ReadBytes.Byte.rom (tag_layout i).2.2
  rw [PackedData.read_byte _ (tag_layout i).1 (tag_layout i).2.1]
  exact congrArg some (tag_data i)

theorem literal_start : ∀ i : Fin 9, literalPointer i = tagPointer ⟨2*i.val,by have := i.isLt;omega⟩+1#32 := by decide +kernel

theorem literal_end : ∀ i : Fin 9, literalPointer i+BitVec.ofNat 32 (JsonProgram.literal i).length =
    tagPointer ⟨2*i.val+1,by have := i.isLt;omega⟩ := by decide +kernel

theorem argument_end : ∀ i : Fin 8, tagPointer ⟨2*i.val+1,by have := i.isLt;omega⟩+1#32 =
    tagPointer ⟨2*(i.val+1),by have := i.isLt;omega⟩ := by decide +kernel
end E5R.Thermostat.JsonFormatData
