import Projects.thermostat.HttpDecLeading
import Projects.thermostat.HttpDecDigits
import Projects.thermostat.StoreBytes
namespace E5R.Thermostat.HttpDecMemory
open E5R E5R.Thermostat

def source (ram : Word → BitVec 8) (sp : Word) (n : Nat) :=
  ByteWrite.write (HttpDecLeading.memory ram sp) (sp+4#32) (ReplyJson.decimal n)

def memory (ram : Word → BitVec 8) (sp dst : Word) (pos n : Nat) :=
  ByteWrite.write (source ram sp n) (dst+BitVec.ofNat 32 pos) (ReplyJson.decimal n)

theorem source_span (B : Board) (ram : Word → BitVec 8) (sp : Word) (n : Nat)
    (hn : n≤832) (hm : Memory.Block B sp 16) : ReadBytes.Span B img (source ram sp n) (sp+4#32) (ReplyJson.decimal n) := by
  have hb := HttpDecDigitsSpec.bounds n hn
  apply ReadBytes.of_ram
  exact ByteWrite.span (Memory.sub_block hm hb.1 (by omega)) (by omega)

theorem destination (B : Board) (dst : Word) (pos n : Nat) (hp : pos≤94) (hn : n≤832)
    (hm : Memory.Block B dst 192) : Memory.Block B (dst+BitVec.ofNat 32 pos) (ReplyJson.decimal n).length := by
  have hb := HttpDecDigitsSpec.bounds n hn
  exact Memory.sub_block hm hb.1 (by omega)

theorem separated (sp dst : Word) (pos n : Nat) (hp : pos≤94) (hn : n≤832)
    (hs : WordRegions.Disjoint sp 16 dst 192) :
    WordRegions.Disjoint (sp+4#32) (ReplyJson.decimal n).length (dst+BitVec.ofNat 32 pos) (ReplyJson.decimal n).length := by
  have hb := HttpDecDigitsSpec.bounds n hn
  intro i j
  have hi := i.isLt
  have hj := j.isLt
  have he := hs ⟨4+i.val,by omega⟩ ⟨pos+j.val,by omega⟩
  simpa only [BitVec.add_assoc,←BitVec.ofNat_add] using he

theorem leading_frame (ram : Word → BitVec 8) (sp x : Word)
    (hx : ∀ i : Fin 16, x≠sp+BitVec.ofNat 32 i.val) : HttpDecLeading.memory ram sp x=ram x := by
  unfold HttpDecLeading.memory HttpDecLeading0.memory
  rw [StoreBytes.frame _ _ _ _ .h (by
    intro i
    have hi : i.val<2 := i.isLt
    have he := hx ⟨12+i.val,by omega⟩
    simpa only [BitVec.add_assoc,←BitVec.ofNat_add] using he)]
  rw [StoreBytes.frame _ _ _ _ .w (by
    intro i
    have hi : i.val<4 := i.isLt
    have he := hx ⟨8+i.val,by omega⟩
    simpa only [BitVec.add_assoc,←BitVec.ofNat_add] using he)]
  apply StoreBytes.frame
  intro i
  have hi : i.val<4 := i.isLt
  have he := hx ⟨4+i.val,by omega⟩
  simpa only [BitVec.add_assoc,←BitVec.ofNat_add] using he

theorem frame (ram : Word → BitVec 8) (sp dst x : Word) (pos n : Nat) (hn : n≤832)
    (hstack : ∀ i : Fin 16, x≠sp+BitVec.ofNat 32 i.val)
    (hout : ∀ i : Fin (ReplyJson.decimal n).length, x≠(dst+BitVec.ofNat 32 pos)+BitVec.ofNat 32 i.val) :
    memory ram sp dst pos n x=ram x := by
  have hb := HttpDecDigitsSpec.bounds n hn
  unfold memory source
  rw [ByteWrite.frame _ _ _ _ hout,ByteWrite.frame _ _ _ _ (by
    intro i
    have hi := i.isLt
    have he := hstack ⟨4+i.val,by omega⟩
    simpa only [BitVec.add_assoc,←BitVec.ofNat_add] using he)]
  exact leading_frame ram sp x hstack

theorem bytes (B : Board) (ram : Word → BitVec 8) (sp dst : Word) (pos n : Nat)
    (hp : pos≤94) (hn : n≤832) (hm : Memory.Block B dst 192) :
    Bytes.Span B (memory ram sp dst pos n) (dst+BitVec.ofNat 32 pos) (ReplyJson.decimal n) := by
  exact ByteWrite.span (destination B dst pos n hp hn hm) (by have hb := HttpDecDigitsSpec.bounds n hn;omega)
end E5R.Thermostat.HttpDecMemory
