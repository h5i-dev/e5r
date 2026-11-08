import Projects.thermostat.FutureSetup
namespace E5R.Thermostat.FutureBodyLimit
open E5R E5R.Thermostat

/-- The header parser's body limit comes from real initialized main RAM. -/
theorem max_body (ram : Word → BitVec 8) (hsize : ramRead ram 0x80ffeba0#32 .w=2048#32) :
    ramRead (FutureSetup.memory ram) 0x80fff864#32 .w=1024#32 := by
  rw [FutureSetup.memory_initialized ram hsize]
  simp [FutureSetup.initialized,ramRead,ramWrite,ramPut,byteOf]
end E5R.Thermostat.FutureBodyLimit
