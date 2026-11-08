import Projects.thermostat.ChunkLayout
import Projects.thermostat.ViewFrame
namespace E5R.Thermostat.ChunkStateFrame
open E5R E5R.Thermostat HttpRequestSpec

theorem preserve {before after p s} (hs : ChunkLayout.At before p s)
    (hf : ViewFrame.Region before after p 25) : ChunkLayout.At after p s := by
  constructor
  · intro i
    have hi := i.isLt
    exact (ViewFrame.word hf (4*i.val) (by omega)).trans (hs.1 i)
  · exact (hf ⟨24,by decide⟩).trans hs.2

end E5R.Thermostat.ChunkStateFrame
