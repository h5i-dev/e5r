import Theories.Logic
namespace E5R.Thermostat.FormatEngineReady
open E5R

/-- The actual compact-format loop registers, before examining the loaded tag. -/
structure Ready (c : Core) (sp obj args desc : Word) (idx : Nat) (tag : BitVec 8) : Prop where
  pc : c.pc = 0x800049e8#32
  spReg : c.get 2 = sp
  arguments : c.get 9 = args
  descriptor : c.get 12 = desc
  vtable : c.get 18 = 0x80005c04#32
  writer : c.get 19 = obj
  tagWord : c.get 21 = BitVec.ofNat 32 tag.toNat
  writeStr : c.get 22 = 0x800022a0#32
  longTag : c.get 23 = 128#32
  index : c.get 24 = BitVec.ofNat 32 idx
  argumentTag : c.get 25 = 192#32
  flags : c.get 26 = 0x60000020#32
end E5R.Thermostat.FormatEngineReady
