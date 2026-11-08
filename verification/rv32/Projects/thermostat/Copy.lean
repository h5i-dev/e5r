import Projects.thermostat.Memory
namespace E5R.Thermostat.Copy
open E5R E5R.Thermostat.Memory
def copy10 (ram : Word → BitVec 8) (src dst : Word) : Word → BitVec 8 :=
  let r0 := ramWrite ram (dst+0) (extend .h true (ramRead ram (src+0) .h)) .h
  let r1 := ramWrite r0 (dst+2) (extend .h true (ramRead ram (src+2) .h)) .h
  let r2 := ramWrite r1 (dst+4) (extend .h true (ramRead ram (src+4) .h)) .h
  let r3 := ramWrite r2 (dst+6) (extend .h true (ramRead ram (src+6) .h)) .h
  ramWrite r3 (dst+8) (extend .h true (ramRead ram (src+8) .h)) .h


theorem bytes (ram : Word → BitVec 8) (src dst : Word) (i : Fin 10) :
    copy10 ram src dst (dst + BitVec.ofNat 32 i.val) = ram (src + BitVec.ofNat 32 i.val) := by
  have hi := i.isLt
  have hc : i.val = 0 ∨ i.val = 1 ∨ i.val = 2 ∨ i.val = 3 ∨ i.val = 4 ∨
      i.val = 5 ∨ i.val = 6 ∨ i.val = 7 ∨ i.val = 8 ∨ i.val = 9 := by omega
  rcases hc with h|h|h|h|h|h|h|h|h|h
  all_goals simp [h, copy10, ramWrite, ramPut, BitVec.add_assoc, BitVec.self_eq_add_right,
    BitVec.add_right_inj, load_half_byte0, load_half_byte1]

theorem frame (ram : Word → BitVec 8) (src dst x : Word)
    (hx : ∀ i : Fin 10, x ≠ dst + BitVec.ofNat 32 i.val) : copy10 ram src dst x = ram x := by
  have h0 := hx ⟨0, by decide⟩
  have h1 := hx ⟨1, by decide⟩
  have h2 := hx ⟨2, by decide⟩
  have h3 := hx ⟨3, by decide⟩
  have h4 := hx ⟨4, by decide⟩
  have h5 := hx ⟨5, by decide⟩
  have h6 := hx ⟨6, by decide⟩
  have h7 := hx ⟨7, by decide⟩
  have h8 := hx ⟨8, by decide⟩
  have h9 := hx ⟨9, by decide⟩
  simp [copy10, ramWrite, ramPut, BitVec.add_assoc] at *
  simp_all

def copyFrom (readRam ram : Word → BitVec 8) (src dst : Word) : Word → BitVec 8 :=
  let r0 := ramWrite ram (dst+0) (extend .h true (ramRead readRam (src+0) .h)) .h
  let r1 := ramWrite r0 (dst+2) (extend .h true (ramRead readRam (src+2) .h)) .h
  let r2 := ramWrite r1 (dst+4) (extend .h true (ramRead readRam (src+4) .h)) .h
  let r3 := ramWrite r2 (dst+6) (extend .h true (ramRead readRam (src+6) .h)) .h
  ramWrite r3 (dst+8) (extend .h true (ramRead readRam (src+8) .h)) .h


theorem bytes_from (readRam ram : Word → BitVec 8) (src dst : Word) (i : Fin 10) :
    copyFrom readRam ram src dst (dst + BitVec.ofNat 32 i.val) = readRam (src + BitVec.ofNat 32 i.val) := by
  have hi := i.isLt
  have hc : i.val = 0 ∨ i.val = 1 ∨ i.val = 2 ∨ i.val = 3 ∨ i.val = 4 ∨
      i.val = 5 ∨ i.val = 6 ∨ i.val = 7 ∨ i.val = 8 ∨ i.val = 9 := by omega
  rcases hc with h|h|h|h|h|h|h|h|h|h
  all_goals simp [h, copyFrom, ramWrite, ramPut, BitVec.add_assoc, BitVec.self_eq_add_right,
    BitVec.add_right_inj, load_half_byte0, load_half_byte1]

theorem frame_from (readRam ram : Word → BitVec 8) (src dst x : Word)
    (hx : ∀ i : Fin 10, x ≠ dst + BitVec.ofNat 32 i.val) : copyFrom readRam ram src dst x = ram x := by
  have h0 := hx ⟨0, by decide⟩
  have h1 := hx ⟨1, by decide⟩
  have h2 := hx ⟨2, by decide⟩
  have h3 := hx ⟨3, by decide⟩
  have h4 := hx ⟨4, by decide⟩
  have h5 := hx ⟨5, by decide⟩
  have h6 := hx ⟨6, by decide⟩
  have h7 := hx ⟨7, by decide⟩
  have h8 := hx ⟨8, by decide⟩
  have h9 := hx ⟨9, by decide⟩
  simp [copyFrom, ramWrite, ramPut, BitVec.add_assoc] at *
  simp_all

end E5R.Thermostat.Copy
