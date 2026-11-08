import Projects.thermostat.PackedData
import Projects.thermostat.HttpRequestSpec
import Projects.thermostat.UartPlatform
namespace E5R.Thermostat.HeadHeaderLiterals
open E5R E5R.Thermostat HttpRequestSpec

theorem content_data (k : Fin 14) :
    PackedData.dataByte (0x80005de0+k.val)=litContentLength[k.val] := by
  revert k;decide +kernel

theorem transfer_data (k : Fin 17) :
    PackedData.dataByte (0x80005dee+k.val)=litTransferEncoding[k.val] := by
  revert k;decide +kernel

theorem content_rom (k : Fin 14) :
    romRead? img (0x80005de0+k.val) 1 false=some (BitVec.ofNat 32 litContentLength[k.val]) := by
  rw [PackedData.read_byte _ (by have := k.isLt;omega) (by have := k.isLt;omega),content_data]

theorem transfer_rom (k : Fin 17) :
    romRead? img (0x80005dee+k.val) 1 false=some (BitVec.ofNat 32 litTransferEncoding[k.val]) := by
  rw [PackedData.read_byte _ (by have := k.isLt;omega) (by have := k.isLt;omega),transfer_data]

theorem content_outside (k : Fin 14) :
    UartPlatform.board.inRam (BitVec.ofNat 32 (0x80005de0+k.val)) 1=false := by
  unfold UartPlatform.board
  rw [ThermostatImage.image_rwBase]
  revert k;decide +kernel

theorem transfer_outside (k : Fin 17) :
    UartPlatform.board.inRam (BitVec.ofNat 32 (0x80005dee+k.val)) 1=false := by
  unfold UartPlatform.board
  rw [ThermostatImage.image_rwBase]
  revert k;decide +kernel
end E5R.Thermostat.HeadHeaderLiterals
