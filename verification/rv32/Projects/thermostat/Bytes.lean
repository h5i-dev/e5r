import Projects.thermostat.Memory
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
namespace E5R.Thermostat.Bytes
open E5R E5R.Thermostat

def At (ram : Word → BitVec 8) (p : Word) (xs : List (BitVec 8)) : Prop :=
  ∀ i : Fin xs.length, ram (p+BitVec.ofNat 32 i.val) = xs[i]

/-- Readable RAM slice, including the empty slice and an explicit nonwrapping
    allocation bound. The length must be representable as an RV32 usize. -/
structure Span (B : Board) (ram : Word → BitVec 8) (p : Word) (xs : List (BitVec 8)) : Prop where
  length : xs.length < 2^32
  nowrap : p.toNat+xs.length ≤ 2^32
  memory : ∀ i : Fin xs.length, B.inRam (p+BitVec.ofNat 32 i.val) 1 = true
  bytes : At ram p xs

theorem empty (B : Board) (ram : Word → BitVec 8) (p : Word) : Span B ram p [] := by
  refine ⟨by decide,?_,?_,?_⟩
  · have := p.isLt;change p.toNat+0 ≤ 2^32;omega
  · intro i;have := i.isLt;simp at this
  · intro i;have := i.isLt;simp at this

theorem of_block (B : Board) (ram : Word → BitVec 8) (p : Word) (xs : List (BitVec 8))
    (hm : Memory.Block B p xs.length) (hl : xs.length < 2^32) (ha : At ram p xs) : Span B ram p xs := by
  refine ⟨hl,hm.2.2,?_,ha⟩
  intro i
  exact Memory.block_access hm (by decide) (by have := i.isLt;omega)

theorem offset_ne (p : Word) (i j : Nat) (hi : i < 2^32) (hj : j < 2^32) (hne : i ≠ j) :
    p+BitVec.ofNat 32 i ≠ p+BitVec.ofNat 32 j := by
  intro h
  have hh := congrArg BitVec.toNat ((BitVec.add_right_inj p).mp h)
  simp only [BitVec.toNat_ofNat,Nat.mod_eq_of_lt hi,Nat.mod_eq_of_lt hj] at hh
  exact hne hh

theorem head {B ram p b bs} (h : Span B ram p (b::bs)) : ram p = b ∧ B.inRam p 1 = true := by
  have hb := h.bytes ⟨0,by simp⟩
  have hm := h.memory ⟨0,by simp⟩
  exact ⟨by simpa using hb,by simpa using hm⟩

theorem tail {B ram p b bs} (h : Span B ram p (b::bs)) : Span B ram (p+1#32) bs := by
  have hl : bs.length+1 < 2^32 := by simpa using h.length
  have hn : p.toNat+(bs.length+1) ≤ 2^32 := by simpa using h.nowrap
  refine ⟨by omega,?_,?_,?_⟩
  · by_cases hz : bs.length = 0
    · have hp := (p+1#32).isLt;omega
    · have hp : (p+1#32).toNat = p.toNat+1 := by
        rw [BitVec.toNat_add]
        change (p.toNat+1)%4294967296 = p.toNat+1
        rw [Nat.mod_eq_of_lt (by omega)]
      rw [hp];omega
  · intro i
    have hi := i.isLt
    have hm := h.memory ⟨i.val+1,by simpa using Nat.succ_lt_succ hi⟩
    have ha : (p+1#32)+BitVec.ofNat 32 i.val = p+BitVec.ofNat 32 (i.val+1) := by
      rw [BitVec.add_assoc,←BitVec.ofNat_add,show 1+i.val = i.val+1 by omega]
    rw [ha]
    exact hm
  · intro i
    have hi := i.isLt
    have hb := h.bytes ⟨i.val+1,by simpa using Nat.succ_lt_succ hi⟩
    have ha : (p+1#32)+BitVec.ofNat 32 i.val = p+BitVec.ofNat 32 (i.val+1) := by
      rw [BitVec.add_assoc,←BitVec.ofNat_add,show 1+i.val = i.val+1 by omega]
    rw [ha]
    change ram (p+BitVec.ofNat 32 (i.val+1)) = bs[i]
    exact hb

/-- Append an actually received byte to a checked buffer. Existing bytes are
    preserved because the append slot is distinct from every prior index. -/
theorem append_byte (B : Board) (ram : Word → BitVec 8) (p : Word) (xs : List (BitVec 8)) (b : BitVec 8)
    (cap : Nat) (hm : Memory.Block B p cap) (hc : cap < 2^32) (hl : xs.length < cap) (ha : At ram p xs) :
    Span B (ramPut ram (p+BitVec.ofNat 32 xs.length) b) p (xs++[b]) := by
  have hlen : (xs++[b]).length = xs.length+1 := by simp
  refine ⟨by rw [hlen];omega,?_,?_,?_⟩
  · rw [hlen];have := hm.2.2;omega
  · intro i
    have hi : i.val < xs.length+1 := by simpa using i.isLt
    exact Memory.block_access hm (by decide) (by omega)
  · intro i
    have hi : i.val < xs.length+1 := by simpa using i.isLt
    by_cases ho : i.val < xs.length
    · have hn := offset_ne p i.val xs.length (by omega) (by omega) (by omega)
      rw [ramPut_ne _ hn]
      have hx := ha ⟨i.val,ho⟩
      change ram (p+BitVec.ofNat 32 i.val) = (xs++[b])[i.val]
      rw [List.getElem_append_left ho]
      exact hx
    · have he : i.val = xs.length := by omega
      change ramPut ram (p+BitVec.ofNat 32 xs.length) b (p+BitVec.ofNat 32 i.val) = (xs++[b])[i.val]
      rw [List.getElem_append_right (by omega)]
      simp [he, ramPut]
end E5R.Thermostat.Bytes
