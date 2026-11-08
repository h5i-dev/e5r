import Theories.Logic
namespace E5R.Thermostat.PadFlags
open E5R

/-- The decimal path tests only force-sign and alternate-prefix here. The
    real fmt::write default also sets alignment/fill bits in 0x60000020. -/
structure Valid (flags : Word) : Prop where
  plus : (flags <<< 10) >>> 31 = 0#32
  alternate : taken .lt (flags <<< 8) (0 : Word) = false

theorem zero : Valid 0#32 := by constructor <;> decide +kernel

theorem default : Valid 0x60000020#32 := by constructor <;> decide +kernel

theorem nonnegative {flags : Word} (h : Valid flags) : taken .ge (flags <<< 8) (0 : Word) = true := by
  change !(flags <<< 8).slt (0 : Word) = true
  have ha : (flags <<< 8).slt (0 : Word) = false := h.alternate
  rw [ha];rfl
end E5R.Thermostat.PadFlags
