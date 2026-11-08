import Projects.thermostat.Decimal
import Projects.thermostat.UartPlatform
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
namespace E5R.Thermostat.DecimalWitness
open E5R E5R.Thermostat

def input (last : BitVec 8) : List (BitVec 8) := [45#8,51#8,50#8,55#8,54#8,last]
def ram (last : BitVec 8) (a : Word) : BitVec 8 := (input last).getD (a.toNat-0x80010000) 255#8
def core : Core :=
  ⟨0x80001dae#32,(fun r => if r = 1 then 0x80000eee#32 else if r = 2 then 0x80fff800#32
    else if r = 10 then 0x80010000#32 else if r = 11 then 6#32 else 0#32),
    false,false,3,0,0,0,0,0,false⟩

theorem readable (last : BitVec 8) : Bytes.Span UartPlatform.board (ram last) 0x80010000#32 (input last) := by
  apply Bytes.of_block
  · unfold Memory.Block UartPlatform.board
    rw [ThermostatImage.image_rwBase]
    simp only [input,List.length_cons,List.length_nil]
    decide +kernel
  · simp only [input,List.length_cons,List.length_nil]
    decide +kernel
  · intro i
    have hi : i.val < 6 := i.isLt
    have hc : i.val = 0 ∨ i.val = 1 ∨ i.val = 2 ∨ i.val = 3 ∨ i.val = 4 ∨ i.val = 5 := by omega
    change ram last (0x80010000#32+BitVec.ofNat 32 i.val) = (input last)[i.val]
    rcases hc with h|h|h|h|h|h
    all_goals simp [ram,input,h]

/-- A satisfiable actual-byte caller returns the signed i16 lower endpoint. -/
theorem accepts_low :
    ∃ d k, k ≤ 102 ∧ DetSteps UartPlatform.board img k ⟨core,ram 56#8⟩ ⟨d,ram 56#8⟩ ∧
      d.pc = 0x80000eee#32 ∧ d.get 10 = 1#32 ∧ (d.get 11).setWidth 16 = 32768#16 ∧ d.get 2 = core.get 2 := by
  obtain ⟨d,k,hk,ht,hpc,hresult,hframe,hcsr⟩ := Decimal.contract UartPlatform.board core (ram 56#8)
    0x80010000#32 (input 56#8) (readable _) rfl rfl rfl
  have hp : DecimalSpec.parse (input 56#8) = some (32768#16) := by decide +kernel
  rw [hp] at hresult
  exact ⟨d,k,hk,ht,hpc,hresult.1,hresult.2,hframe 2 (by decide)⟩

/-- One more negative magnitude is rejected by the ELF, not merely by the spec. -/
theorem rejects_overflow :
    ∃ d k, k ≤ 102 ∧ DetSteps UartPlatform.board img k ⟨core,ram 57#8⟩ ⟨d,ram 57#8⟩ ∧
      d.pc = 0x80000eee#32 ∧ d.get 10 = 0#32 ∧ d.get 2 = core.get 2 := by
  obtain ⟨d,k,hk,ht,hpc,hresult,hframe,hcsr⟩ := Decimal.contract UartPlatform.board core (ram 57#8)
    0x80010000#32 (input 57#8) (readable _) rfl rfl rfl
  have hp : DecimalSpec.parse (input 57#8) = none := by decide +kernel
  rw [hp] at hresult
  exact ⟨d,k,hk,ht,hpc,hresult,hframe 2 (by decide)⟩
end E5R.Thermostat.DecimalWitness
