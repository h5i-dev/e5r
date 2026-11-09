import Projects.thermostat.UartTxPoll
import Projects.thermostat.ProtocolStreamSpec
import Projects.thermostat.StackUartPlatform
set_option autoImplicit false
set_option maxRecDepth 4000
namespace E5R.Thermostat.StackUartTxPoll
open E5R E5R.Thermostat ProtocolStreamSpec UartTxPoll
abbrev B := StackBoard.board
theorem load (c : Core) (ram : Word → BitVec 8) (o : Oracle)
    (hp : c.pc=0x800007f8#32) (hu : c.get 13=0x10000000#32) :
    Observed.stepInstr B img ⟨c,ram⟩ o =
      ⟨.ok (c.wr 17 (UartPoll.byte (o 0)) 0x800007fc#32) ram [],[⟨0x10000005#32,.b,UartPoll.byte (o 0),0⟩]⟩ := by
  have hk := StackUartPlatform.load ⟨c,ram⟩ o 17 13 5#32 4#32 0x10000005#32 UartPlatform.lsr
    (by rw [hp];decide) (by rw [hp];exact up2147485688)
    (by rw [hu];decide +kernel) (by decide +kernel) StackUartPlatform.lsr_device rfl rfl
  have hraw : devVal .b (o 0)=UartPoll.byte (o 0) := rfl
  rw [hraw] at hk
  simpa only [hp,UartPoll.extend_byte,show 0x800007f8#32+4#32=0x800007fc#32 by decide +kernel] using hk

end E5R.Thermostat.StackUartTxPoll
