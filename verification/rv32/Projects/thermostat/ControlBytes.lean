import Projects.thermostat.ControlDecode
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
namespace E5R.Thermostat.Control
open E5R

/-- Exhaustive candidate addresses for SYSTEM opcodes. Every halfword boundary
    is considered, including boundaries inside a 32-bit instruction. -/
def sites : Nat → List Nat → List Nat
  | _, [] => []
  | base, b::bs =>
    if base % 2 = 0 ∧ b % 128 = 0x73 then base::sites (base+1) bs
    else sites (base+1) bs

def systemSites (img : List Segment) : List Nat :=
  img.flatMap fun s => if s.exec then sites s.base s.bytes else []

theorem site_of_byte {bs : List Nat} {base idx b : Nat}
    (h : bs[idx]? = some b) (hb : b % 128 = 0x73) (ha : (base+idx)%2 = 0) :
    base+idx ∈ sites base bs := by
  induction bs generalizing base idx with
  | nil => simp at h
  | cons first rest ih =>
    cases idx with
    | zero =>
      simp only [List.getElem?_cons_zero,Option.some.injEq] at h
      subst first
      have ha' : base%2 = 0 := by simpa using ha
      simp [sites,hb,ha']
    | succ idx =>
      simp only [List.getElem?_cons_succ] at h
      have hh := ih (base := base+1) h (by omega)
      have he : base+(idx+1) = (base+1)+idx := by omega
      rw [he]
      unfold sites
      split
      · exact List.mem_cons_of_mem _ hh
      · exact hh

theorem rom_system_site {img : List Segment} {a b : Nat}
    (h : romByte? img a true = some b) (hb : b % 128 = 0x73) (ha : a%2 = 0) :
    a ∈ systemSites img := by
  unfold romByte? at h
  simp only [Bool.not_true,Bool.false_or] at h
  cases hf : img.find? (fun s => s.base ≤ a && a < s.base+s.bytes.length && s.exec) with
  | none => simp [hf] at h
  | some s =>
    simp only [hf] at h
    have hmem := List.mem_of_find?_eq_some hf
    have hp := List.find?_some hf
    have hprops : (s.base ≤ a ∧ a < s.base+s.bytes.length) ∧ s.exec = true := by simpa using hp
    have hs : s.bytes[a-s.base]? = some b := by simpa [Segment.byte?,hprops.1.1] using h
    have he : s.base+(a-s.base) = a := by omega
    have hit := site_of_byte (base := s.base) hs hb (by simpa only [he] using ha)
    apply List.mem_flatMap.mpr
    exact ⟨s,hmem,by simpa [hprops.2,he] using hit⟩
end E5R.Thermostat.Control
