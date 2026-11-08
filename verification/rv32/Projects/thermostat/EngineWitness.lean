import Projects.thermostat.Engine
import Projects.thermostat.ShellWitness
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace E5R.Thermostat.EngineWitness
open E5R E5R.Thermostat

def ram (a : Word) : BitVec 8 :=
  if a = 0x80010000 ∨ a = 0x80010001 ∨ a = 0x80010002 ∨ a = 0x80010003 then 255
  else ShellWitness.ram a

theorem valid_caller : Engine.Pre Witness.board ShellWitness.core ram 0x80020000 true Spec.initial (.relay 3 true) := by
  have hboard : Witness.board = (⟨2147507992,0x81000000-2147507992,[]⟩ : Board) := by
    unfold Witness.board;rw [ThermostatImage.image_rwBase]
  have hs : ShellCall.Pre Witness.board ShellWitness.core ram 0x80020000 true Spec.initial (.relay 3 true) := by
    rw [hboard]
    constructor <;> (try simp only [Memory.Block,Encoding.SnapshotAt,Encoding.CommandAt]) <;> decide +kernel
  refine ⟨hs,?_,?_,?_,?_⟩
  · rw [hboard]
    unfold Memory.Block
    decide +kernel
  · decide +kernel
  · unfold Engine.Separate
    decide +kernel
  · decide +kernel

/-- A concrete complete engine transaction stores relay3=on, releases the
    actual RefCell borrow word, and leaves a state satisfying the invariant. -/
theorem persisted_relay :
    ∃ n d r, n ≤ 171 ∧ DetSteps Witness.board img n ⟨ShellWitness.core,ram⟩ ⟨d,r⟩ ∧
      d.pc = 0x80000736 ∧ r 0x80010007 = 1#8 ∧ ramRead r 0x80010000 .w = 0#32 ∧
      Engine.InvariantAt r 0x80010000 := by
  obtain ⟨n,d,r,hn,hr,hpost,hinv⟩ := Engine.contract_inv Witness.board ShellWitness.core ram 0x80020000 true
    Spec.initial (.relay 3 true) valid_caller Spec.initial_inv
  have hs := hpost.state ⟨3,by decide⟩
  have hp : ((ShellWitness.core.get 23+4#32)+BitVec.ofNat 32 (3 : Nat)) = 0x80010007 := by decide +kernel
  have hb : Encoding.snapshotByte (Spec.commit Spec.initial (Spec.transition true Spec.initial (.relay 3 true))) ⟨3,by decide⟩ = 1#8 := by decide +kernel
  rw [hp,hb] at hs
  exact ⟨n,d,r,hn,hr,hpost.pc,hs,hpost.released,hinv⟩
end E5R.Thermostat.EngineWitness
