import Projects.thermostat.FormatSpace
import Projects.thermostat.FormatSource
import Projects.thermostat.FormatTable
namespace E5R.Thermostat.FormatLayout
open E5R E5R.Thermostat

structure Layout (ram : Word → BitVec 8) (p obj args dst : Word) (cap pos : Nat) (values : Fin 8 → FormatValue.Value) : Prop
    extends FormatSpace.Space ram p obj dst cap pos where
  table : FormatTable.At UartPlatform.board ram args values
  tableArena : WordRegions.Disjoint args 64 p 224
  tableOutput : WordRegions.Disjoint args 64 dst cap
  tableObject : WordRegions.Disjoint args 64 obj 12
  sources : ∀ i : Fin 8, FormatSource.At UartPlatform.board ram (values i)
  sourceArena : ∀ i : Fin 8, WordRegions.Disjoint (FormatValue.pointer (values i)) (FormatValue.size (values i)) p 224
  sourceOutput : ∀ i : Fin 8, WordRegions.Disjoint (FormatValue.pointer (values i)) (FormatValue.size (values i)) dst cap
  sourceObject : ∀ i : Fin 8, WordRegions.Disjoint (FormatValue.pointer (values i)) (FormatValue.size (values i)) obj 12

theorem after_append {ram r p obj args dst cap pos values xs} (h : Layout ram p obj args dst cap pos values)
    (he : AppendEffect.Effect UartPlatform.board ram r p obj dst 224 cap pos xs)
    (hf : pos+xs.length ≤ cap) : Layout r p obj args dst cap (pos+xs.length) values := by
  refine ⟨FormatSpace.after_append h.toSpace he hf,
    FormatTable.frame h.table (AppendEffect.region he hf h.tableArena h.tableOutput h.tableObject),
    h.tableArena,h.tableOutput,h.tableObject,?_,h.sourceArena,h.sourceOutput,h.sourceObject⟩
  intro i
  exact FormatSource.frame (h.sources i) (AppendEffect.region he hf (h.sourceArena i) (h.sourceOutput i) (h.sourceObject i))
end E5R.Thermostat.FormatLayout
