import Projects.thermostat.SignedMagnitudeExtra
namespace E5R.Thermostat.I16Ready
open E5R E5R.Thermostat

structure Ready (c d : Core) (sp fmt : Word) (v : BitVec 16) (off len : Nat) : Prop where
  pc : d.pc = 0x80004514#32
  spReg : d.get 2 = sp
  x1 : d.get 1 = 0x80004f88#32
  x10 : d.get 10 = fmt
  x11 : d.get 11 = SignedMagnitude.positive v
  x12 : d.get 12 = 1#32
  x13 : d.get 13 = 0#32
  x14 : d.get 14 = sp+BitVec.ofNat 32 off
  x15 : d.get 15 = BitVec.ofNat 32 len
  csr : d.sameCsr c
  saved : ∀ r : Reg, r = 9 ∨ 18 ≤ r.val → d.get r = c.get r

def offset (n : Nat) : Nat :=
  if n < 10 then 7 else if n < 100 then 6 else if n < 1000 then 5 else if n < 10000 then 4 else 3

def length (n : Nat) : Nat := 8-offset n
end E5R.Thermostat.I16Ready
