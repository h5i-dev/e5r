import Projects.thermostat.StoreWords
namespace E5R.Thermostat.HeadDoneStoreGeometry
open E5R E5R.Thermostat

theorem below (ram : Word → BitVec 8) (sp value : Word) (k off : Nat)
    (small : k+4≤4904) (large : off≤292) :
    ramRead (ramWrite ram ((sp+4904#32)+BitVec.ofNat 32 off) value .w) (sp+BitVec.ofNat 32 k) .w=
      ramRead ram (sp+BitVec.ofNat 32 k) .w := by
  apply StoreWords.read_other
  have address : (sp+4904#32)+BitVec.ofNat 32 off=sp+BitVec.ofNat 32 (4904+off) := by
    rw [BitVec.add_assoc,←BitVec.ofNat_add]
  rw [address]
  exact StoreWords.offsets sp k 4 (4904+off) 4 (by omega) (by omega) (Or.inl (by omega))
end E5R.Thermostat.HeadDoneStoreGeometry
