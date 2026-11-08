import Projects.thermostat.FormatValue
import Projects.thermostat.I16Input
import Projects.thermostat.FormatInput
namespace E5R.Thermostat.FormatCallbackData
open E5R E5R.Thermostat

/-- Source values, checked allocations and initialized actual Formatter words.
    Each constructor states only a concrete callback's proved input contract. -/
inductive Data (B : Board) (ram : Word → BitVec 8) (p fmt obj dst : Word) (cap pos : Nat) : FormatValue.Value → Prop
  | signed (ptr : Word) (v : BitVec 16)
      (data : I16Input.Data B ram p ptr fmt obj dst cap pos v) : Data B ram p fmt obj dst cap pos (.signed ptr v)
  | boolean (ptr : Word) (v : Bool)
      (source : ReadBytes.Byte B img ram ptr (Encoding.boolByte v))
      (data : FormatInput.Data B ram (p+96#32) fmt obj (FormatLiterals.boolPointer v) dst 0x60000020#32 cap pos (ReplyJson.boolean v)) :
      Data B ram p fmt obj dst cap pos (.boolean ptr v)
  | mode (ptr : Word) (v : Spec.Mode)
      (object : Memory.Block B ptr 8) (aligned : ptr.toNat%4 = 0)
      (pointer : ramRead ram ptr .w = ModeLiterals.pointer v)
      (length : ramRead ram (ptr+4#32) .w = BitVec.ofNat 32 (ReplyJson.mode v).length)
      (data : FormatInput.Data B ram (p+96#32) fmt obj (ModeLiterals.pointer v) dst 0x60000020#32 cap pos (ReplyJson.mode v)) :
      Data B ram p fmt obj dst cap pos (.mode ptr v)
end E5R.Thermostat.FormatCallbackData
