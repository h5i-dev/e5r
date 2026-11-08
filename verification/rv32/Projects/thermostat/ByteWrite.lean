import Projects.thermostat.Bytes
import Projects.thermostat.ViewFrame
import Projects.thermostat.WordRegions
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
namespace E5R.Thermostat.ByteWrite
open E5R E5R.Thermostat

def write (ram : Word → BitVec 8) (p : Word) : List (BitVec 8) → Word → BitVec 8
  | [] => ram
  | b::bs => write (ramPut ram p b) (p+1#32) bs

theorem frame (ram : Word → BitVec 8) (p x : Word) (xs : List (BitVec 8))
    (hx : ∀ i : Fin xs.length, x ≠ p+BitVec.ofNat 32 i.val) : write ram p xs x = ram x := by
  induction xs generalizing ram p with
  | nil => rfl
  | cons b bs ih =>
    change write (ramPut ram p b) (p+1#32) bs x = _
    rw [ih (ramPut ram p b) (p+1#32) (by
      intro i
      have hh := hx ⟨i.val+1,by have := i.isLt;simp only [List.length_cons] at this ⊢;omega⟩
      simpa only [BitVec.ofNat_add,BitVec.add_assoc,show i.val+1 = 1+i.val by omega] using hh)]
    apply ramPut_ne
    simpa only [BitVec.add_zero] using hx ⟨0,by simp⟩

theorem bytes (ram : Word → BitVec 8) (p : Word) (xs : List (BitVec 8)) (hl : xs.length < 2^32) :
    Bytes.At (write ram p xs) p xs := by
  induction xs generalizing ram p with
  | nil => intro i;exact Fin.elim0 i
  | cons b bs ih =>
    have ht : bs.length < 2^32 := by simpa using Nat.lt_of_succ_lt hl
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · change write ram p (b::bs) (p+0#32) = b
      rw [BitVec.add_zero]
      change write (ramPut ram p b) (p+1#32) bs p = b
      rw [frame _ _ _ _ (by
        intro j
        have hj := j.isLt
        have hh := Bytes.offset_ne p 0 (1+j.val) (by decide) (by have := hl;change bs.length+1 < 2^32 at this;omega) (by omega)
        simpa only [BitVec.add_zero,BitVec.ofNat_add,BitVec.add_assoc] using hh),ramPut_eq]
    · have hh := ih (ramPut ram p b) (p+1#32) ht j
      have ha : (p+1#32)+BitVec.ofNat 32 j.val = p+BitVec.ofNat 32 (j.val+1) := by
        rw [BitVec.add_assoc,←BitVec.ofNat_add,show 1+j.val = j.val+1 by omega]
      change write (ramPut ram p b) (p+1#32) bs (p+BitVec.ofNat 32 (j.val+1)) = (b::bs)[j.val+1]
      rw [List.getElem_cons_succ,←ha]
      exact hh

theorem span {B ram p xs} (hm : Memory.Block B p xs.length) (hl : xs.length < 2^32) :
    Bytes.Span B (write ram p xs) p xs := Bytes.of_block B _ p xs hm hl (bytes ram p xs hl)
theorem region {obj n dst xs} (h : WordRegions.Disjoint obj n dst xs.length) (ram : Word → BitVec 8) :
    ViewFrame.Region ram (write ram dst xs) obj n := fun i => frame ram dst _ xs (h i)
end E5R.Thermostat.ByteWrite
