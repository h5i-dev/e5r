import Projects.thermostat.FutureSetup
import Projects.thermostat.MainChunkLayout
namespace E5R.Thermostat.FutureBodyLayout
open E5R E5R.Thermostat

/-- Additional body-decoder fields established by the already verified
    actual serve-future initialization. -/
theorem initialized (ram : Word → BitVec 8)
    (hsize : ramRead ram 0x80ffeba0#32 .w=2048#32) :
    ramRead (FutureSetup.memory ram) 0x80fff864#32 .w=1024#32 ∧
    ramRead (FutureSetup.memory ram) 0x80fff9c4#32 .w=0x80fff860#32 := by
  rw [FutureSetup.memory_initialized ram hsize]
  constructor <;> simp [FutureSetup.initialized,ramRead,ramWrite,ramPut,byteOf]

theorem full (ram : Word → BitVec 8) (hsize : ramRead ram 0x80ffeba0#32 .w=2048#32) :
    MainChunkLayout.At (FutureSetup.memory ram) 0x80ffeb90#32 := by
  have h := FutureSetup.layout ram hsize
  have body := initialized ram hsize
  constructor
  · simpa using h.rx
  · simpa using h.capacity
  · simpa using body.2
  · simpa using body.1
  · simpa using h.filledPtr

end E5R.Thermostat.FutureBodyLayout
