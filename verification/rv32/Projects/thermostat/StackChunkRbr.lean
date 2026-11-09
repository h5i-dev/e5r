import Projects.thermostat.StackUartPlatform
import Projects.thermostat.MainChunkRbr
set_option autoImplicit false
namespace E5R.Thermostat.StackChunkRbr
open E5R E5R.Thermostat
abbrev B := StackBoard.board

theorem load (c : Core) (ram : Word → BitVec 8) (o : Oracle)
    (hp : c.pc=0x80000e80#32) (hu : c.get 19=0x10000000#32) :
    Observed.stepInstr B img ⟨c,ram⟩ o =
      ⟨.ok (c.wr 11 (UartPoll.byte (o 0)) 0x80000e84#32) ram [],
        [⟨0x10000000#32,.b,UartPoll.byte (o 0),0⟩]⟩ := by
  have hk := StackUartPlatform.load ⟨c,ram⟩ o 11 19 0#32 4#32 0x10000000#32 UartPlatform.data
    (by rw [hp];decide) (by rw [hp];exact cc2147487360)
    (by rw [hu];decide +kernel) (by decide +kernel) StackUartPlatform.data_device rfl rfl
  have hv : devVal .b (o 0)=UartPoll.byte (o 0) := rfl
  simpa only [hv,hp,UartPoll.extend_byte,show 0x80000e80#32+4#32=0x80000e84#32 by decide +kernel] using hk
end E5R.Thermostat.StackChunkRbr
