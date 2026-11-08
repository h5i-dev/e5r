import Projects.thermostat.FormatLayout
import Projects.thermostat.FormatEngineSave
namespace E5R.Thermostat.FormatLayout
open E5R E5R.Thermostat

theorem saved {ram p obj args dst cap pos values} (h : Layout ram p obj args dst cap pos values) (c : Core) :
    Layout (FormatEngineSave.memory ram (p+160#32) c) p obj args dst cap pos values := by
  have region (a : Word) (n : Nat) (hn : WordRegions.Disjoint a n p 224) :
      ViewFrame.Region ram (FormatEngineSave.memory ram (p+160#32) c) a n := by
    intro i
    exact FormatEngineSave.frame ram (p+160#32) c _ (Subregion.right hn 160 64 (by decide) i)
  have ho := region obj 12 h.objectArena
  have space : FormatSpace.Space (FormatEngineSave.memory ram (p+160#32) c) p obj dst cap pos := by
    refine ⟨h.arena,h.aligned,h.object,h.objectAligned,h.capacity,h.position,?_,
      (ViewFrame.word ho 4 (by decide)).trans h.capacityWord,(ViewFrame.word ho 8 (by decide)).trans h.positionWord,
      h.output,h.nowrap,h.objectArena,h.outputArena,h.objectOutput⟩
    have hh := ViewFrame.word ho 0 (by decide)
    simpa only [BitVec.add_zero] using hh.trans (by simpa only [BitVec.add_zero] using h.pointerWord)
  exact ⟨space,FormatTable.frame h.table (region args 64 h.tableArena),h.tableArena,h.tableOutput,h.tableObject,
    fun i => FormatSource.frame (h.sources i) (region _ _ (h.sourceArena i)),h.sourceArena,h.sourceOutput,h.sourceObject⟩
end E5R.Thermostat.FormatLayout
