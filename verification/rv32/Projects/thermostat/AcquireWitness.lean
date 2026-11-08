import Projects.thermostat.Acquire
import Projects.thermostat.EngineWitness
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
namespace E5R.Thermostat.AcquireWitness
open E5R E5R.Thermostat

def core := ShellWitness.core.goto 0x80000614

theorem valid_caller : Acquire.Pre Witness.board core ShellWitness.ram 0x80020000
    true Spec.initial (.relay 3 true) := by
  have hb : Witness.board = (⟨2147507992,0x81000000-2147507992,[]⟩ : Board) := by
    unfold Witness.board;rw [ThermostatImage.image_rwBase]
  refine ⟨rfl,?_,?_,?_,?_,?_⟩
  · exact ShellWitness.valid_caller
  · rw [hb];unfold Memory.Block
    decide +kernel
  · decide +kernel
  · unfold Engine.Separate
    decide +kernel
  · decide +kernel

/-- Satisfiable free-borrow input runs the actual acquisition and transaction. -/
theorem persisted_relay :
    ∃ n d r, n ≤ 175 ∧ DetSteps Witness.board img n ⟨core,ShellWitness.ram⟩ ⟨d,r⟩ ∧
      d.pc = 0x80000736 ∧ r 0x80010007 = 1#8 ∧ ramRead r 0x80010000 .w = 0#32 ∧
      Engine.InvariantAt r 0x80010000 := by
  obtain ⟨n,d,r,hn,hr,hpost,hinv⟩ := Acquire.contract_inv Witness.board core ShellWitness.ram
    0x80020000 true Spec.initial (.relay 3 true) valid_caller Spec.initial_inv
  have hs := hpost.state ⟨3,by decide⟩
  have hp : ((core.get 23+4#32)+BitVec.ofNat 32 (3 : Nat)) = 0x80010007 := by decide +kernel
  have hb : Encoding.snapshotByte (Spec.commit Spec.initial (Spec.transition true Spec.initial (.relay 3 true)))
      ⟨3,by decide⟩ = 1#8 := by decide +kernel
  rw [hp,hb] at hs
  exact ⟨n,d,r,hn,hr,hpost.pc,hs,hpost.released,hinv⟩

/-- A held borrow genuinely takes the real refusal branch, retaining RAM. -/
theorem held_borrow :
    DetSteps Witness.board img 2 ⟨core,EngineWitness.ram⟩
      ⟨core.wr 10 0xffffffff#32 0x80000766,EngineWitness.ram⟩ := by
  have he : Memory.Block Witness.board (core.get 23) 14 := EngineWitness.valid_caller.engineRam
  have hr := Acquire.unavailable Witness.board core EngineWitness.ram rfl he
    (by decide +kernel) (by decide +kernel)
  have hv : ramRead EngineWitness.ram (core.get 23) .w = 0xffffffff#32 := by decide +kernel
  rw [hv] at hr
  exact hr
end E5R.Thermostat.AcquireWitness
