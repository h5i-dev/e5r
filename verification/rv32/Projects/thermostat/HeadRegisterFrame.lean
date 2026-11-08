import Theories.Logic
namespace E5R.Thermostat.HeadRegisterFrame
open E5R

/-- A finite write allowance, proved from each actual instruction contract.
    It states no PC, memory, CSR, call or execution summary. -/
def At (before after : Core) (writes : List Reg) : Prop :=
  ∀ r : Reg, r∉writes → after.get r=before.get r

theorem refl (c : Core) (writes : List Reg) : At c c writes := fun _ _ => rfl

theorem mono {c d : Core} {small large : List Reg} (h : At c d small)
    (includes : ∀ r : Reg, r∈small → r∈large) : At c d large := by
  intro r outside
  exact h r (fun inside => outside (includes r inside))

theorem trans {c d e : Core} {first second : List Reg}
    (h : At c d first) (k : At d e second) : At c e (first++second) := by
  intro r outside
  have hfirst : r∉first := fun inside => outside (List.mem_append_left second inside)
  have hsecond : r∉second := fun inside => outside (List.mem_append_right first inside)
  exact (k r hsecond).trans (h r hfirst)

theorem wr (c : Core) (rd : Reg) (v pc : Word) : At c (c.wr rd v pc) [rd] := by
  intro r outside
  exact Core.wr_get_ne _ _ _ _ _ (fun eq => outside (by simp [eq]))

theorem goto (c : Core) (pc : Word) : At c (c.goto pc) [] := fun _ _ => rfl
end E5R.Thermostat.HeadRegisterFrame
