import Projects.thermostat.Memory
namespace E5R.Thermostat.ResponseWordBytes
open E5R E5R.Thermostat

theorem word (ram : Word → BitVec 8) (a v : Word)
    (h : ∀ i : Fin 4, ram (a+BitVec.ofNat 32 i.val)=byteOf v i.val) : ramRead ram a .w=v := by
  have h0 : ram a=byteOf v 0 := by simpa only [BitVec.add_zero] using h ⟨0,by decide⟩
  have h1 : ram (a+1)=byteOf v 1 := h ⟨1,by decide⟩
  have h2 : ram (a+2)=byteOf v 2 := h ⟨2,by decide⟩
  have h3 : ram (a+3)=byteOf v 3 := h ⟨3,by decide⟩
  rw [ramRead,h0,h1,h2,h3]
  apply BitVec.eq_of_toNat_eq
  simp only [byteOf,BitVec.toNat_ofNat]
  have := v.isLt
  omega

theorem half (ram : Word → BitVec 8) (a v : Word) (hv : v.toNat<65536)
    (h : ∀ i : Fin 2, ram (a+BitVec.ofNat 32 i.val)=byteOf v i.val) : extend .h false (ramRead ram a .h)=v := by
  have h0 : ram a=byteOf v 0 := by simpa only [BitVec.add_zero] using h ⟨0,by decide⟩
  have h1 : ram (a+1)=byteOf v 1 := h ⟨1,by decide⟩
  rw [ramRead,h0,h1]
  apply BitVec.eq_of_toNat_eq
  simp only [extend,BitVec.toNat_and,BitVec.toNat_ofNat,byteOf]
  change (_ &&& 65535)=_
  rw [show (65535 : Nat)=2^16-1 by decide +kernel,Nat.and_two_pow_sub_one_eq_mod]
  omega
end E5R.Thermostat.ResponseWordBytes
