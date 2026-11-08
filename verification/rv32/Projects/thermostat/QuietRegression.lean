import Projects.thermostat.Quiet
import Projects.thermostat.UartPlatform
namespace E5R.Thermostat.QuietRegression
open E5R E5R.Thermostat
abbrev B := UartPlatform.board

/-- The value is ignored, while the existing device read is still real. -/
def effect (c : Core) : Eff := .load .b 0x10000000#32 false (fun _ => .done c)

theorem observed (c : Core) (ram : Word → BitVec 8) (o : Oracle) :
    Observed.interp B img o (effect c) ram 0 [] [] =
      ⟨.ok c ram [],[⟨0x10000000#32,.b,devVal .b (o 0),0⟩]⟩ := by
  unfold effect Observed.interp
  have e1 : ¬((0x10000000#32).toNat%Width.b.bytes≠0) := by decide
  have e2 : B.inRam 0x10000000#32 Width.b.bytes=false := UartPlatform.outside _ (by decide)
  have e3 : romRead? img (0x10000000#32).toNat Width.b.bytes false=none := UartPlatform.rom_none _ (by decide)
  rw [ite_eq_right e1,e2,ite_eq_right (by decide),ite_eq_right (by decide),e3]
  rfl

/-- Deterministic return values alone do not justify empty read logs. -/
theorem deterministic_result (c : Core) (ram : Word → BitVec 8) (o : Oracle) :
    E5R.interp B img o (effect c) ram 0 []=.ok c ram [] := by
  have he := Observed.erase B img o (effect c) ram 0 [] []
  rw [observed] at he
  exact he.symm

theorem not_quiet (c : Core) (ram : Word → BitVec 8) :
    ¬(∀ o, Observed.interp B img o (effect c) ram 0 [] []=⟨.ok c ram [],[]⟩) := by
  intro h
  have hh := h (fun _ => 0#32)
  rw [observed] at hh
  have hr := congrArg Observed.Result.reads hh
  cases hr
end E5R.Thermostat.QuietRegression
