import Projects.thermostat.MainInit
import Projects.thermostat.Witness
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
namespace E5R.Thermostat.MainInitWitness
open E5R E5R.Thermostat

def core : Core := Witness.core.goto 0x80000000#32
def ram (_ : Word) : BitVec 8 := 255#8

theorem stack_available : Memory.Block Witness.board 0x80ff0000#32 65536 := by
  have hb : Witness.board = (⟨2147507992,0x81000000-2147507992,[]⟩ : Board) := by
    unfold Witness.board;rw [ThermostatImage.image_rwBase]
  rw [hb]
  unfold Memory.Block
  decide +kernel

/-- Nonzero arbitrary initial bytes are actually cleared by main's memset calls. -/
theorem reset_to_loop :
    ∃ d r, Trace.Closed Witness.board img 2432 ⟨core,ram⟩ ⟨d,r⟩ ∧
      MainInit.Ready Witness.board d r ∧ Engine.InvariantAt r 0x80ffebbc#32 :=
  MainInit.closed_contract Witness.board core ram rfl (Or.inr rfl) rfl stack_available
end E5R.Thermostat.MainInitWitness
