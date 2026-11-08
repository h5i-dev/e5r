import Projects.thermostat.HttpRequestSpec
namespace E5R.Thermostat.ChunkRejectStatus
open E5R.Thermostat HttpRequestSpec

theorem range (s : CState) (b maxBody status : Nat)
    (he : (chunkStep s b maxBody).2=.reject status) : status=400 ∨ status=413 := by
  simp only [chunkStep,sizeStep,expectStep] at he
  repeat' first | split at he
  all_goals simp_all

end E5R.Thermostat.ChunkRejectStatus
