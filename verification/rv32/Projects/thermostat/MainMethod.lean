import Projects.thermostat.Send
namespace E5R.Thermostat.MainMethod
open E5R E5R.Thermostat

def head (b : BitVec 8) : Bool := decide (b.toNat=1)

theorem head_value (b : BitVec 8) :
    alu .sltu (BitVec.ofNat 32 b.toNat+0xffffffff#32) 1#32=ResponseHeadBodyMath.boolWord (head b) := by
  have h : ∀ n : Fin 256, alu .sltu (BitVec.ofNat 32 n.val+0xffffffff#32) 1#32=
      ResponseHeadBodyMath.boolWord (decide (n.val=1)) := by decide +kernel
  exact h ⟨b.toNat,b.isLt⟩
end E5R.Thermostat.MainMethod
