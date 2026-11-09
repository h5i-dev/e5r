import Projects.thermostat.StackBoard
import Projects.thermostat.BoardRestriction
set_option autoImplicit false
namespace E5R.Thermostat.StackBoardSimulation
open E5R E5R.Thermostat
abbrev narrow := StackBoard.board
abbrev broad := UartPlatform.board

theorem effect {e : Eff} {o ram i evs reads c after events}
    (success : (Observed.interp narrow img o e ram i evs reads).value=.ok c after events) :
    Observed.interp broad img o e ram i evs reads=Observed.interp narrow img o e ram i evs reads :=
  BoardRestriction.effect narrow broad img (fun _ _ h => StackBoard.included h)
    (fun a w h _ => ⟨StackBoard.rom_none a w (StackBoard.broad_lower h),StackBoard.device_none a (StackBoard.broad_lower h)⟩)
    StackBoard.devices success

theorem instruction {m o c after events}
    (success : (Observed.stepInstr narrow img m o).value=.ok c after events) :
    Observed.stepInstr broad img m o=Observed.stepInstr narrow img m o :=
  BoardRestriction.instruction narrow broad img (fun _ _ h => StackBoard.included h)
    (fun a w h _ => ⟨StackBoard.rom_none a w (StackBoard.broad_lower h),StackBoard.device_none a (StackBoard.broad_lower h)⟩)
    StackBoard.devices success

theorem quiet_step {m d} (h : Quiet.Step narrow img m d) : Quiet.Step broad img m d := by
  intro o
  have agrees := instruction (m := m) (o := o) (by rw [h o])
  exact agrees.trans (h o)

theorem quiet_steps {n m d} (h : Quiet.Steps narrow img n m d) : Quiet.Steps broad img n m d := by
  induction h with
  | refl => exact .refl _
  | step first rest ih => exact .step (quiet_step first) ih
end E5R.Thermostat.StackBoardSimulation
