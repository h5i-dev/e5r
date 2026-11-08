import Projects.thermostat.StoreBytes
set_option linter.constructorNameAsVariable false
namespace E5R.Thermostat.FrameOffsets
open E5R E5R.Thermostat

/-- Cancellation also works when the allocation base wraps; each individual
    offset is bounded so that distinct offsets cannot coincide modulo 2^32. -/
theorem ne (p : Word) (a b i j : Nat) (ha : a+i<4294967296)
    (hb : b+j<4294967296) (hne : a+i≠b+j) :
    p+BitVec.ofNat 32 a+BitVec.ofNat 32 i ≠ p+BitVec.ofNat 32 b+BitVec.ofNat 32 j := by
  intro h
  simp only [BitVec.add_assoc,←BitVec.ofNat_add,BitVec.add_right_inj] at h
  have hh := congrArg BitVec.toNat h
  simp only [BitVec.toNat_ofNat,Nat.mod_eq_of_lt ha,Nat.mod_eq_of_lt hb] at hh
  exact hne hh

theorem word (ram : Word → BitVec 8) (p v : Word) (a b : Nat) (w : Width)
    (ha : a+4≤4294967296) (hb : b+w.bytes≤4294967296) (hs : a+4≤b ∨ b+w.bytes≤a) :
    ramRead (ramWrite ram (p+BitVec.ofNat 32 b) v w) (p+BitVec.ofNat 32 a) .w=
      ramRead ram (p+BitVec.ofNat 32 a) .w := by
  apply ramRead_w_congr
  intro i hi
  apply StoreBytes.frame
  intro j
  exact ne p a b i j.val (by omega) (by have := j.isLt;omega) (by have := j.isLt;omega)

theorem byte (ram : Word → BitVec 8) (p v : Word) (a b : Nat) (w : Width)
    (ha : a<4294967296) (hb : b+w.bytes≤4294967296) (hs : a<b ∨ b+w.bytes≤a) :
    ramWrite ram (p+BitVec.ofNat 32 b) v w (p+BitVec.ofNat 32 a)=ram (p+BitVec.ofNat 32 a) := by
  apply StoreBytes.frame
  intro j
  simpa only [BitVec.add_zero] using ne p a b 0 j.val ha
    (by have := j.isLt;omega) (by have := j.isLt;omega)

theorem half (ram : Word → BitVec 8) (p v : Word) (a b : Nat) (w : Width)
    (ha : a+2≤4294967296) (hb : b+w.bytes≤4294967296) (hs : a+2≤b ∨ b+w.bytes≤a) :
    ramRead (ramWrite ram (p+BitVec.ofNat 32 b) v w) (p+BitVec.ofNat 32 a) .h=
      ramRead ram (p+BitVec.ofNat 32 a) .h := by
  have h0 := byte ram p v a b w (by omega) hb (by omega)
  have h1 : ramWrite ram (p+BitVec.ofNat 32 b) v w ((p+BitVec.ofNat 32 a)+1)=
      ram ((p+BitVec.ofNat 32 a)+1) := by
    rw [show (1 : Word)=1#32 by decide +kernel]
    simpa only [BitVec.ofNat_add,BitVec.add_assoc] using
      byte ram p v (a+1) b w (by omega) hb (by omega)
  simp only [ramRead,h0,h1]

end E5R.Thermostat.FrameOffsets
