import Projects.thermostat.StoreWords
namespace E5R.Thermostat.StoreRead
open E5R E5R.Thermostat

theorem congr (ram ram' : Word → BitVec 8) (a : Word) (w : Width)
    (h : ∀ i : Fin w.bytes, ram (a+BitVec.ofNat 32 i.val)=ram' (a+BitVec.ofNat 32 i.val)) :
    ramRead ram a w=ramRead ram' a w := by
  cases w with
  | b =>
    have h0 := h ⟨0,by decide⟩
    simp only [BitVec.add_zero] at h0
    simp only [ramRead,h0]
  | h =>
    have h0 := h ⟨0,by decide⟩
    have h1 := h ⟨1,by decide⟩
    simp only [BitVec.add_zero] at h0
    have h1' : ram (a+1)=ram' (a+1) := h1
    simp only [ramRead,h0,h1']
  | w => exact ramRead_w_congr a (fun i hi => h ⟨i,hi⟩)

theorem other (ram : Word → BitVec 8) (a b v : Word) (rd wr : Width)
    (h : ∀ i : Fin rd.bytes, ∀ j : Fin wr.bytes, a+BitVec.ofNat 32 i.val≠b+BitVec.ofNat 32 j.val) :
    ramRead (ramWrite ram b v wr) a rd=ramRead ram a rd :=
  congr _ _ _ _ (fun i => StoreBytes.frame ram b v _ wr (h i))
end E5R.Thermostat.StoreRead
