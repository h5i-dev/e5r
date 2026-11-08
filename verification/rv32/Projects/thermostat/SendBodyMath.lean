import Projects.thermostat.ResponseHeadBodyMath
namespace E5R.Thermostat.SendBodyMath
open E5R E5R.Thermostat

def flags (status : Nat) := ResponseHeadBodyMath.not204 status &&& ResponseHeadBodyMath.not304 status

theorem flags_value (status : Nat) (hs : status≤599) (hlo : 200≤status) :
    flags status=ResponseHeadBodyMath.boolWord (ResponseHeadSpec.hasBody status) := by
  have h : ∀ n : Fin 600, 200≤n.val → flags n.val=ResponseHeadBodyMath.boolWord (ResponseHeadSpec.hasBody n.val) := by decide +kernel
  exact h ⟨status,by omega⟩ hlo

def mask (status : Nat) := alu .sra ((flags status) <<< 31) 31#32

theorem mask_value (status : Nat) (hs : status≤599) (hlo : 200≤status) :
    mask status=(if ResponseHeadSpec.hasBody status then 0xffffffff#32 else 0#32) := by
  unfold mask
  rw [flags_value status hs hlo]
  cases hh : ResponseHeadSpec.hasBody status <;> decide +kernel

theorem length_value (status : Nat) (body : Word) (hs : status≤599) (hlo : 200≤status) :
    mask status &&& body=(if ResponseHeadSpec.hasBody status then body else 0#32) := by
  rw [mask_value status hs hlo]
  cases hh : ResponseHeadSpec.hasBody status
  · exact BitVec.zero_and
  · exact BitVec.allOnes_and
end E5R.Thermostat.SendBodyMath
