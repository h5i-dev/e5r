import Projects.thermostat.FormatCursor
namespace E5R.Thermostat.Callee
open E5R E5R.Thermostat

def Saved (r : Reg) : Prop := r = 8 ∨ r = 9 ∨ (18 ≤ r.val ∧ r.val ≤ 27)
instance (r : Reg) : Decidable (Saved r) := by unfold Saved;infer_instance

def Frame (c d : Core) : Prop := ∀ r, Saved r → d.get r = c.get r

theorem of_cursor {c d : Core} (h : CursorExit.Returned c d) (hh : HighFrame.Frame c d) : Frame c d := by
  intro r hr
  rcases hr with rfl | rfl | ⟨hlo,hhi⟩
  · exact h.x8
  · exact h.x9
  · by_cases h18 : r.val = 18
    · have he : r = 18 := Fin.ext h18;subst r;exact h.x18
    · by_cases h19 : r.val = 19
      · have he : r = 19 := Fin.ext h19;subst r;exact h.x19
      · exact hh r (by omega)

theorem of_returned {c d : Core} (h : FormatCursor.Returned c d) : Frame c d := by
  intro r hr
  rcases hr with rfl | rfl | ⟨hlo,hhi⟩
  · exact h.x8
  · exact h.x9
  ·
    by_cases h18 : r.val = 18
    · have he : r = 18 := Fin.ext h18;subst r;exact h.x18
    by_cases h19 : r.val = 19
    · have he : r = 19 := Fin.ext h19;subst r;exact h.x19
    by_cases h20 : r.val = 20
    · have he : r = 20 := Fin.ext h20;subst r;exact h.x20
    by_cases h21 : r.val = 21
    · have he : r = 21 := Fin.ext h21;subst r;exact h.x21
    by_cases h22 : r.val = 22
    · have he : r = 22 := Fin.ext h22;subst r;exact h.x22
    by_cases h23 : r.val = 23
    · have he : r = 23 := Fin.ext h23;subst r;exact h.x23
    by_cases h24 : r.val = 24
    · have he : r = 24 := Fin.ext h24;subst r;exact h.x24
    by_cases h25 : r.val = 25
    · have he : r = 25 := Fin.ext h25;subst r;exact h.x25
    by_cases h26 : r.val = 26
    · have he : r = 26 := Fin.ext h26;subst r;exact h.x26
    have he : r = 27 := Fin.ext (by omega);subst r;exact h.x27

theorem ne_low (r q : Reg) (hr : Saved r) (hq : q.val < 18) (h8 : q ≠ 8) (h9 : q ≠ 9) : r ≠ q := by
  intro he
  rcases hr with hr | hr | ⟨hlo,hhi⟩
  · exact h8 (he.symm.trans hr)
  · exact h9 (he.symm.trans hr)
  · have hn := congrArg Fin.val he;omega
end E5R.Thermostat.Callee
