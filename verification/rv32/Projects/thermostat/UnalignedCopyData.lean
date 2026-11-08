import Projects.thermostat.UnalignedCopyLoop
import Projects.thermostat.WordBytes
import Projects.thermostat.RomSpan
import Projects.thermostat.ReplyJson
import Projects.thermostat.UartPlatform
set_option maxRecDepth 3000
namespace E5R.Thermostat.UnalignedCopyData
open E5R E5R.Thermostat

def wordAt (addr : Nat) : Word := BitVec.ofNat 32 (PackedFetch.rd PackedData.dataByte addr 4)
def byteAt (addr : Nat) : Word := BitVec.ofNat 32 (PackedData.dataByte addr)
def error (wide : Bool) : Spec.Error := if wide then .setpointOutOfRange else .noSuchRelay

def src (wide : Bool) : Word := if wide then 0x80005ba6#32 else 0x80005bc7#32
def base (wide : Bool) : Word := if wide then 0x80005ba4#32 else 0x80005bc4#32
def initial (wide : Bool) : Word := if wide then 0x227b0000#32 else 0x7b000000#32
def shift (wide : Bool) : Word := if wide then 16#32 else 24#32
def comp (wide : Bool) : Word := if wide then 16#32 else 8#32

def nexts (wide : Bool) : List Word := if wide then
  [wordAt 0x80005ba8,wordAt 0x80005bac,wordAt 0x80005bb0,wordAt 0x80005bb4,wordAt 0x80005bb8,wordAt 0x80005bbc,wordAt 0x80005bc0]
  else [wordAt 0x80005bc8,wordAt 0x80005bcc,wordAt 0x80005bd0,wordAt 0x80005bd4,wordAt 0x80005bd8]

def endSource (wide : Bool) : Word := if wide then 0x80005bc0#32 else 0x80005bd8#32

def lastPayload (wide : Bool) : Word :=
  let previous := UnalignedCopyLoop.lastWord (initial wide) (nexts wide)
  let a := byteAt (if wide then 0x80005bc4 else 0x80005bdc)
  let b := alu .sll (byteAt (if wide then 0x80005bc5 else 0x80005bdd)) 8#32
  let top := if wide then b else alu .or (alu .sll (byteAt 0x80005bde) 16#32) b
  alu .or (alu .sll (alu .add top a) (comp wide)) (alu .srl previous (shift wide))

theorem source_data (wide : Bool) : ∀ i : Fin (nexts wide).length,
    wordAt ((base wide+4#32)+BitVec.ofNat 32 (4*i.val)).toNat = (nexts wide)[i.val] := by cases wide <;> decide +kernel

theorem outside (wide : Bool) : ∀ i : Fin (nexts wide).length,
    UartPlatform.board.inRam ((base wide+4#32)+BitVec.ofNat 32 (4*i.val)) 4=false := by
  cases wide <;> (unfold UartPlatform.board;rw [ThermostatImage.image_rwBase];decide +kernel)

theorem source (wide : Bool) : AlignedSource.Source UartPlatform.board (base wide+4#32) (nexts wide) := by
  refine ⟨by cases wide <;> decide,outside wide,?_⟩
  intro i
  have hi := i.isLt
  have bounds : 0x800056a8 ≤ ((base wide+4#32)+BitVec.ofNat 32 (4*i.val)).toNat ∧
      ((base wide+4#32)+BitVec.ofNat 32 (4*i.val)).toNat+4 ≤ 0x80005f18 := by
    cases wide with
    | false =>
      change i.val<5 at hi
      change 0x800056a8 ≤ ((0x80005bc4#32+4#32)+BitVec.ofNat 32 (4*i.val)).toNat ∧
        ((0x80005bc4#32+4#32)+BitVec.ofNat 32 (4*i.val)).toNat+4 ≤ 0x80005f18
      simp only [BitVec.toNat_add,BitVec.toNat_ofNat];omega
    | true =>
      change i.val<7 at hi
      change 0x800056a8 ≤ ((0x80005ba4#32+4#32)+BitVec.ofNat 32 (4*i.val)).toNat ∧
        ((0x80005ba4#32+4#32)+BitVec.ofNat 32 (4*i.val)).toNat+4 ≤ 0x80005f18
      simp only [BitVec.toNat_add,BitVec.toNat_ofNat];omega
  rw [PackedData.read_data _ 4 bounds.1 bounds.2]
  exact congrArg some (source_data wide i)

theorem end_source (wide : Bool) : base wide+BitVec.ofNat 32 (4*(nexts wide).length)=endSource wide := by cases wide <;> decide +kernel

theorem bytes (wide : Bool) :
    AlignedCopyLoop.bytes (UnalignedCopyLoop.mixes (initial wide) (nexts wide) (shift wide) (comp wide)) ++
      WordBytes.bytes (lastPayload wide) ++ [125#8] = ReplyJson.errorBody (error wide) := by cases wide <;> decide +kernel
end E5R.Thermostat.UnalignedCopyData
