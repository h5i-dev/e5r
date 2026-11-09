import Projects.thermostat.StackUartPlatform
import Projects.thermostat.MainLengthUart
set_option autoImplicit false
set_option maxRecDepth 3000
namespace E5R.Thermostat.StackLengthUart
open E5R E5R.Thermostat MainLengthUart
abbrev B := StackBoard.board
abbrev byte := MainLengthUart.byte

theorem rx_load (c : Core) (ram : Word → BitVec 8) (o : Oracle)
    (hp : c.pc = 0x80000c6c#32) (hu : c.get 19 = 0x10000000#32) :
    Observed.stepInstr B img ⟨c,ram⟩ o =
      ⟨.ok (c.wr 10 (byte (o 0)) 0x80000c70#32) ram [],[⟨0x10000005#32,.b,byte (o 0),0⟩]⟩ := by
  have hk := StackUartPlatform.load ⟨c,ram⟩ o 10 19 5#32 4#32 0x10000005#32 UartPlatform.lsr
    (by rw [hp];decide) (by rw [hp];exact ml2147486828)
    (by rw [hu];decide +kernel) (by decide +kernel) StackUartPlatform.lsr_device rfl rfl
  have hext : extend .b false (devVal .b (o 0)) = byte (o 0) := extend_byte (o 0)
  have hraw : devVal .b (o 0) = byte (o 0) := rfl
  have hpcAdd : 0x80000c6c#32+4#32 = 0x80000c70#32 := by decide +kernel
  simpa only [hp,hext,hraw,extend_byte,hpcAdd] using hk

theorem rx_data_load (c : Core) (ram : Word → BitVec 8) (o : Oracle)
    (hp : c.pc = 0x80000c74#32) (hu : c.get 19 = 0x10000000#32) :
    Observed.stepInstr B img ⟨c,ram⟩ o =
      ⟨.ok (c.wr 10 (byte (o 0)) 0x80000c78#32) ram [],[⟨0x10000000#32,.b,byte (o 0),0⟩]⟩ := by
  have hk := StackUartPlatform.load ⟨c,ram⟩ o 10 19 0#32 4#32 0x10000000#32 UartPlatform.data
    (by rw [hp];decide) (by rw [hp];exact ml2147486836)
    (by rw [hu];decide +kernel) (by decide +kernel) StackUartPlatform.data_device rfl rfl
  have hext : extend .b false (devVal .b (o 0)) = byte (o 0) := extend_byte (o 0)
  have hraw : devVal .b (o 0) = byte (o 0) := rfl
  have hpcAdd : 0x80000c74#32+4#32 = 0x80000c78#32 := by decide +kernel
  simpa only [hp,hext,hraw,extend_byte,hpcAdd] using hk

end E5R.Thermostat.StackLengthUart
