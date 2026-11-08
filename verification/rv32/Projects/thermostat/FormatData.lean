import Projects.thermostat.FormatLiterals
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
namespace E5R.Thermostat.FormatData
open E5R E5R.Thermostat

theorem cursor_char_method_word : romRead? img 0x80005c14 4 false = some 0x80002302#32 := by
  rw [PackedData.read_data 0x80005c14 4 (by decide) (by decide)]
  decide +kernel

theorem cursor_char_method_outside : UartPlatform.board.inRam 0x80005c14#32 4 = false := by
  unfold UartPlatform.board;rw [ThermostatImage.image_rwBase];decide +kernel

theorem pair_tens : ∀ i : Fin 100,
    PackedData.dataByte (0x80005e10#32+BitVec.ofNat 32 (2*i.val)).toNat = 48+i.val/10 := by decide +kernel

theorem pair_units : ∀ i : Fin 100,
    PackedData.dataByte (0x80005e10#32+BitVec.ofNat 32 (2*i.val+1)).toNat = 48+i.val%10 := by decide +kernel
end E5R.Thermostat.FormatData
