import Projects.thermostat.HttpRequestSpec
import Theories.Logic
namespace E5R.Thermostat.HeadMethodFlow
open E5R E5R.Thermostat HttpRequestSpec

/-- The literal branch/ALU expression at 0x80002d06..2d50. Its connection to
    actual steps is a separate obligation; this module checks byte classes. -/
def high (v : Word) : Word :=
  if taken .ltu v 58#32 then 0x80002cf4#32
  else if taken .ltu v 65#32 then 0x80002efc#32
  else if taken .ltu v 91#32 then 0x80002cf4#32
  else if taken .ltu v 94#32 then 0x80002efc#32
  else
    let mask := alu .add (alu .and v 253#32) 0xffffff84#32
    let flag := alu .or (alu .sltu v 123#32) (alu .sltu mask 1#32)
    if taken .ne flag (0 : Word) then 0x80002cf4#32 else 0x80002efc#32

def low (v : Word) : Word :=
  let shift := alu .add v 0xffffffde#32
  if taken .geu (alu .and shift 255#32) 14#32 then 0x80002cf4#32
  else if taken .eq (alu .and (alu .srl 9409#32 shift) 1#32) (0 : Word) then 0x80002cf4#32
  else 0x80002efc#32

def flow (b : BitVec 8) : Word :=
  let v := BitVec.ofNat 32 b.toNat
  if taken .ltu v 33#32 then 0x80002da2#32
  else if taken .geu v 48#32 then high v else low v

theorem byte_classes : ∀ b : BitVec 8,
    flow b=(if b.toNat<33 then 0x80002da2#32 else if isTchar b.toNat then 0x80002cf4#32 else 0x80002efc#32) := by
  decide +kernel

theorem lt33 : ∀ b : BitVec 8, taken .ltu (BitVec.ofNat 32 b.toNat) 33#32=decide (b.toNat<33) := by decide +kernel
end E5R.Thermostat.HeadMethodFlow
