import Projects.thermostat.FutureSetup
namespace E5R.Thermostat.FutureHeadLayout
open E5R E5R.Thermostat

/-- The max-head premise of the parser proof comes from the real main
    initialization, rather than a guessed successful parser outcome. -/
theorem max_head (ram : Word → BitVec 8) (hsize : ramRead ram 0x80ffeba0#32 .w=2048#32) :
    ramRead (FutureSetup.memory ram) 0x80fff860#32 .w=1024#32 := by
  rw [FutureSetup.memory_initialized ram hsize]
  simp [FutureSetup.initialized,ramRead,ramWrite,ramPut,byteOf]
end E5R.Thermostat.FutureHeadLayout
