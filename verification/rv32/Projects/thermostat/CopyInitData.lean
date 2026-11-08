import Projects.thermostat.CopyUnalignedScratch
import Projects.thermostat.PackedData
import Projects.thermostat.UartPlatform
namespace E5R.Thermostat.CopyInitData
open E5R E5R.Thermostat

def halfRam (ram : Word → BitVec 8) (sp : Word) := ramWrite (CopyUnalignedScratch.memory ram sp) (sp+14#32) 0x227b#32 .h
def byteRam (ram : Word → BitVec 8) (sp : Word) := ramWrite (CopyUnalignedScratch.memory ram sp) (sp+15#32) 0x7b#32 .b

theorem half_word (ram : Word → BitVec 8) (sp : Word) : ramRead (halfRam ram sp) (sp+12#32) .w=0x227b0000#32 := by
  simp [halfRam,CopyUnalignedScratch.memory,ramRead,ramWrite,ramPut,BitVec.add_assoc,BitVec.add_right_inj,BitVec.self_eq_add_right,byteOf]

theorem byte_word (ram : Word → BitVec 8) (sp : Word) : ramRead (byteRam ram sp) (sp+12#32) .w=0x7b000000#32 := by
  simp [byteRam,CopyUnalignedScratch.memory,ramRead,ramWrite,ramPut,BitVec.add_assoc,BitVec.add_right_inj,BitVec.self_eq_add_right,byteOf]

theorem half_rom : romRead? img 0x80005ba6 2 false=some 0x227b#32 := by
  rw [PackedData.read_data _ 2 (by decide) (by decide)];decide +kernel

theorem byte_rom : romRead? img 0x80005bc7 1 false=some 0x7b#32 := by
  rw [PackedData.read_data _ 1 (by decide) (by decide)];decide +kernel

theorem half_outside : UartPlatform.board.inRam 0x80005ba6#32 2=false := by
  unfold UartPlatform.board;rw [ThermostatImage.image_rwBase];decide +kernel

theorem byte_outside : UartPlatform.board.inRam 0x80005bc7#32 1=false := by
  unfold UartPlatform.board;rw [ThermostatImage.image_rwBase];decide +kernel
end E5R.Thermostat.CopyInitData
