import Projects.thermostat.Trim
import Projects.thermostat.UartPlatform
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
namespace E5R.Thermostat.TrimWitness
open E5R E5R.Thermostat

def input (edge : BitVec 8) : List (BitVec 8) := [edge,49#8,edge]
def ram (edge : BitVec 8) (a : Word) : BitVec 8 := (input edge).getD (a.toNat-0x80010000) 255#8
def core : Core :=
  ⟨0x80001f7e#32,(fun r => if r = 2 then 0x80fff800#32 else if r = 10 then 0x80ffeb90#32
    else if r = 11 then 0x80010000#32 else if r = 12 then 3#32 else 0#32),
    false,false,3,0,0,0,0,0,false⟩

theorem readable (edge : BitVec 8) : Bytes.Span UartPlatform.board (ram edge) 0x80010000#32 (input edge) := by
  apply Bytes.of_block
  · unfold Memory.Block UartPlatform.board
    rw [ThermostatImage.image_rwBase]
    simp only [input,List.length_cons,List.length_nil]
    decide +kernel
  · simp only [input,List.length_cons,List.length_nil]
    decide +kernel
  · intro i
    have hi : i.val < 3 := i.isLt
    have hc : i.val = 0 ∨ i.val = 1 ∨ i.val = 2 := by omega
    change ram edge (0x80010000#32+BitVec.ofNat 32 i.val) = (input edge)[i.val]
    rcases hc with h|h|h <;> simp [ram,input,h]

theorem ff_removed :
    ∃ d k, k ≤ 79 ∧ DetSteps UartPlatform.board img k ⟨core,ram 12#8⟩ ⟨d,ram 12#8⟩ ∧
      d.pc = 0x80001fb4#32 ∧ d.get 8 = 0x80010001#32 ∧ d.get 9 = 1#32 ∧
      ram 12#8 (d.get 8) = 49#8 ∧ d.get 2 = core.get 2 := by
  obtain ⟨d,k,hk,ht,hpc,h8,h9,hspan,hframe,hcsr⟩ := Trim.contract UartPlatform.board core (ram 12#8)
    0x80010000#32 (input 12#8) (readable _) rfl rfl rfl
  have hp : 0x80010000#32+BitVec.ofNat 32 ((input 12#8).length-(TrimMath.left (input 12#8)).length) = 0x80010001#32 := by decide +kernel
  have hl : BitVec.ofNat 32 (TrimMath.trim (input 12#8)).length = 1#32 := by decide +kernel
  rw [hp] at h8;rw [hl] at h9
  refine ⟨d,k,hk,ht,hpc,h8,h9,?_,hframe 2 (by decide)⟩
  rw [h8];decide +kernel

theorem vt_retained :
    ∃ d k, k ≤ 79 ∧ DetSteps UartPlatform.board img k ⟨core,ram 11#8⟩ ⟨d,ram 11#8⟩ ∧
      d.pc = 0x80001fb4#32 ∧ d.get 8 = 0x80010000#32 ∧ d.get 9 = 3#32 ∧
      ram 11#8 (d.get 8) = 11#8 ∧ d.get 2 = core.get 2 := by
  obtain ⟨d,k,hk,ht,hpc,h8,h9,hspan,hframe,hcsr⟩ := Trim.contract UartPlatform.board core (ram 11#8)
    0x80010000#32 (input 11#8) (readable _) rfl rfl rfl
  have hp : 0x80010000#32+BitVec.ofNat 32 ((input 11#8).length-(TrimMath.left (input 11#8)).length) = 0x80010000#32 := by decide +kernel
  have hl : BitVec.ofNat 32 (TrimMath.trim (input 11#8)).length = 3#32 := by decide +kernel
  rw [hp] at h8;rw [hl] at h9
  refine ⟨d,k,hk,ht,hpc,h8,h9,?_,hframe 2 (by decide)⟩
  rw [h8];decide +kernel
end E5R.Thermostat.TrimWitness
