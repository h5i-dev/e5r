import Projects.thermostat.StoreBytes
import Projects.thermostat.WordZero
namespace E5R.Thermostat.StoreWords
open E5R E5R.Thermostat

theorem read_other (ram : Word → BitVec 8) (a b v : Word) (w : Width)
    (h : ∀ i : Fin 4, ∀ j : Fin w.bytes, a+BitVec.ofNat 32 i.val≠b+BitVec.ofNat 32 j.val) :
    ramRead (ramWrite ram b v w) a .w=ramRead ram a .w := by
  apply ramRead_w_congr
  intro i hi
  exact StoreBytes.frame ram b v _ w (h ⟨i,hi⟩)

theorem offsets (p : Word) (a n b m : Nat) (ha : a+n<2^32) (hb : b+m<2^32)
    (hs : a+n≤b ∨ b+m≤a) :
    ∀ i : Fin n, ∀ j : Fin m, (p+BitVec.ofNat 32 a)+BitVec.ofNat 32 i.val≠(p+BitVec.ofNat 32 b)+BitVec.ofNat 32 j.val := by
  intro i j
  have hi := i.isLt
  have hj := j.isLt
  rw [BitVec.add_assoc,BitVec.add_assoc,←BitVec.ofNat_add,←BitVec.ofNat_add]
  exact WordZero.offset_ne p (a+i.val) (b+j.val) (by omega) (by omega) (by rcases hs with h|h <;> omega)
end E5R.Thermostat.StoreWords
