import Projects.thermostat.FormatLayoutSave
import Projects.thermostat.StackFormatSpace
set_option autoImplicit false
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
namespace E5R.Thermostat.StackFormatLayout
open E5R E5R.Thermostat 
structure Layout (ram : Word → BitVec 8) (p obj args dst : Word) (cap pos : Nat) (values : Fin 8 → FormatValue.Value) : Prop
    extends StackFormatSpace.Space ram p obj dst cap pos where
  table : FormatTable.At StackBoard.board ram args values
  tableArena : WordRegions.Disjoint args 64 p 224
  tableOutput : WordRegions.Disjoint args 64 dst cap
  tableObject : WordRegions.Disjoint args 64 obj 12
  sources : ∀ i : Fin 8, FormatSource.At StackBoard.board ram (values i)
  sourceArena : ∀ i : Fin 8, WordRegions.Disjoint (FormatValue.pointer (values i)) (FormatValue.size (values i)) p 224
  sourceOutput : ∀ i : Fin 8, WordRegions.Disjoint (FormatValue.pointer (values i)) (FormatValue.size (values i)) dst cap
  sourceObject : ∀ i : Fin 8, WordRegions.Disjoint (FormatValue.pointer (values i)) (FormatValue.size (values i)) obj 12

theorem after_append {ram r p obj args dst cap pos values xs} (h : Layout ram p obj args dst cap pos values)
    (he : AppendEffect.Effect StackBoard.board ram r p obj dst 224 cap pos xs)
    (hf : pos+xs.length ≤ cap) : Layout r p obj args dst cap (pos+xs.length) values := by
  refine ⟨StackFormatSpace.after_append h.toSpace he hf,
    FormatTable.frame h.table (AppendEffect.region he hf h.tableArena h.tableOutput h.tableObject),
    h.tableArena,h.tableOutput,h.tableObject,?_,h.sourceArena,h.sourceOutput,h.sourceObject⟩
  intro i
  exact FormatSource.frame (h.sources i) (AppendEffect.region he hf (h.sourceArena i) (h.sourceOutput i) (h.sourceObject i))

theorem saved {ram p obj args dst cap pos values} (h : Layout ram p obj args dst cap pos values) (c : Core) :
    Layout (FormatEngineSave.memory ram (p+160#32) c) p obj args dst cap pos values := by
  have region (a : Word) (n : Nat) (hn : WordRegions.Disjoint a n p 224) :
      ViewFrame.Region ram (FormatEngineSave.memory ram (p+160#32) c) a n := by
    intro i
    exact FormatEngineSave.frame ram (p+160#32) c _ (Subregion.right hn 160 64 (by decide) i)
  have ho := region obj 12 h.objectArena
  have space : StackFormatSpace.Space (FormatEngineSave.memory ram (p+160#32) c) p obj dst cap pos := by
    refine ⟨h.arena,h.aligned,h.object,h.objectAligned,h.capacity,h.position,?_,
      (ViewFrame.word ho 4 (by decide)).trans h.capacityWord,(ViewFrame.word ho 8 (by decide)).trans h.positionWord,
      h.output,h.nowrap,h.objectArena,h.outputArena,h.objectOutput⟩
    have hh := ViewFrame.word ho 0 (by decide)
    simpa only [BitVec.add_zero] using hh.trans (by simpa only [BitVec.add_zero] using h.pointerWord)
  exact ⟨space,FormatTable.frame h.table (region args 64 h.tableArena),h.tableArena,h.tableOutput,h.tableObject,
    fun i => FormatSource.frame (h.sources i) (region _ _ (h.sourceArena i)),h.sourceArena,h.sourceOutput,h.sourceObject⟩
end E5R.Thermostat.StackFormatLayout
