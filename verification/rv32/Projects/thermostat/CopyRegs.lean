import Projects.thermostat.FormatCursor
namespace E5R.Thermostat.CopyRegs
open E5R E5R.Thermostat

def Preserved (r : Reg) : Prop := r=1 ∨ r=8 ∨ r=9 ∨ (18≤r.val ∧ r.val≤27)
instance (r : Reg) : Decidable (Preserved r) := inferInstanceAs (Decidable (r=1 ∨ r=8 ∨ r=9 ∨ (18≤r.val ∧ r.val≤27)))

theorem ne_low (r q : Reg) (hr : Preserved r) (hq : q.val<18) (h1 : q≠1) (h8 : q≠8) (h9 : q≠9) : r≠q := by
  intro he
  subst r
  rcases hr with h|h|h|h
  · exact h1 h
  · exact h8 h
  · exact h9 h
  · omega

theorem returned {c d : Core} (hpc : d.pc = c.get 1 &&& ~~~1) (hsp : d.get 2 = c.get 2) (hc : d.sameCsr c)
    (hr : ∀ r : Reg, Preserved r → d.get r = c.get r) : FormatCursor.Returned c d :=
  ⟨hpc,hsp,hc,hr 1 (by decide),hr 8 (by decide),hr 9 (by decide),hr 18 (by decide),hr 19 (by decide),
    hr 20 (by decide),hr 21 (by decide),hr 22 (by decide),hr 23 (by decide),hr 24 (by decide),hr 25 (by decide),hr 26 (by decide),hr 27 (by decide)⟩
end E5R.Thermostat.CopyRegs
