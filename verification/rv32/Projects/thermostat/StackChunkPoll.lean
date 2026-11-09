import Projects.thermostat.StackUartPlatform
import Projects.thermostat.MainChunkPoll
set_option autoImplicit false
namespace E5R.Thermostat.StackChunkPoll
open E5R E5R.Thermostat
abbrev B := StackBoard.board

theorem load (c : Core) (ram : Word → BitVec 8) (o : Oracle)
    (hp : c.pc=0x80000fb0#32) (hu : c.get 19=0x10000000#32) :
    Observed.stepInstr B img ⟨c,ram⟩ o =
      ⟨.ok (c.wr 11 (UartPoll.byte (o 0)) 0x80000fb4#32) ram [],[⟨0x10000005#32,.b,UartPoll.byte (o 0),0⟩]⟩ := by
  have hk := StackUartPlatform.load ⟨c,ram⟩ o 11 19 5#32 4#32 0x10000005#32 UartPlatform.lsr
    (by rw [hp];decide) (by rw [hp];exact cr2147487664)
    (by rw [hu];decide +kernel) (by decide +kernel) StackUartPlatform.lsr_device rfl rfl
  have hraw : devVal .b (o 0)=UartPoll.byte (o 0) := rfl
  rw [hraw] at hk
  simpa only [hp,UartPoll.extend_byte,show 0x80000fb0#32+4#32=0x80000fb4#32 by decide +kernel] using hk

end E5R.Thermostat.StackChunkPoll
