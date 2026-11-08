import Projects.thermostat.HttpRequestSpec
import Theories.Logic
namespace E5R.Thermostat.HeadNameFlow
open E5R E5R.Thermostat HttpRequestSpec

def high (v : Word) (last : Bool) : Word :=
  if taken .ltu v 58#32 then (if last then 0x8000342c#32 else 0x80002fe0#32)
  else if taken .ltu v (alu .add (0 : Word) 65#32) then 0x80003056#32
  else if taken .ltu v 91#32 then (if last then 0x8000342c#32 else 0x80002fe0#32)
  else if taken .ltu v (alu .add (0 : Word) 94#32) then 0x8000342c#32
  else if last then 0x8000342c#32
  else
    let mask := alu .add (alu .and v 253#32) 0xffffff84#32
    let flag := alu .and (alu .xor (alu .sltu v 123#32) 0xffffffff#32) (alu .sltu (0 : Word) mask)
    if taken .eq flag (0 : Word) then 0x80002fe0#32 else 0x8000342c#32

def low (v : Word) (last : Bool) : Word :=
  let shift := alu .add v 0xffffffde#32
  if taken .geu (alu .and shift 255#32) 14#32 then (if last then 0x8000342c#32 else 0x80002fe0#32)
  else if last then 0x8000342c#32
  else if taken .eq (alu .and (alu .srl 9409#32 shift) 1#32) (0 : Word) then 0x80002fe0#32
  else 0x8000342c#32

def flow (b : BitVec 8) (last : Bool) : Word :=
  let v := BitVec.ofNat 32 b.toNat
  if taken .ltu v 33#32 then 0x8000342c#32
  else if taken .geu v 48#32 then high v last else low v last

theorem byte_classes : ∀ (b : BitVec 8) (last : Bool),
    flow b last=(if 58≤b.toNat ∧ b.toNat<65 then 0x80003056#32
      else if isTchar b.toNat ∧ last=false then 0x80002fe0#32 else 0x8000342c#32) := by
  decide +kernel
end E5R.Thermostat.HeadNameFlow
