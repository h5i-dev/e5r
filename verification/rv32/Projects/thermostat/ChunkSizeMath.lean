import Projects.thermostat.ChunkNumberMath
namespace E5R.Thermostat.ChunkSizeMath
open E5R E5R.Thermostat

theorem add (a b : Nat) : alu .add (BitVec.ofNat 32 a) (BitVec.ofNat 32 b)=BitVec.ofNat 32 (a+b) := by
  simp only [alu,BitVec.ofNat_add]

theorem no_carry (a b : Nat) (h : a+b<4294967296) :
    alu .sltu (alu .add (BitVec.ofNat 32 a) (BitVec.ofNat 32 b)) (BitVec.ofNat 32 b)=0#32 := by
  rw [add,ChunkNumberMath.less (a+b) b h (by omega)]
  simp only [show ¬a+b<b by omega,ite_false]

theorem masked (n : Nat) (hn : n<256) :
    alu .and (BitVec.ofNat 32 n) 255#32=BitVec.ofNat 32 n := by
  apply BitVec.eq_of_toNat_eq
  simp only [alu,BitVec.toNat_and,BitVec.toNat_ofNat]
  change ((n%4294967296) &&& 255)=n%4294967296
  rw [show (255 : Nat)=2^8-1 by decide,Nat.and_two_pow_sub_one_eq_mod]
  omega

theorem left4 (n : Nat) (hn : n<4294967296) :
    alu .sll (BitVec.ofNat 32 n) 4#32=BitVec.ofNat 32 (16*n) := by
  apply BitVec.eq_of_toNat_eq
  change ((BitVec.ofNat 32 n) <<< 4).toNat=(BitVec.ofNat 32 (16*n)).toNat
  rw [BitVec.toNat_shiftLeft,Nat.shiftLeft_eq]
  simp only [BitVec.toNat_ofNat,Nat.mod_eq_of_lt hn]
  omega

theorem right28_zero (n : Nat) (hn : n≤268435455) :
    alu .srl (BitVec.ofNat 32 n) 28#32=0#32 := by
  apply BitVec.eq_of_toNat_eq
  change ((BitVec.ofNat 32 n) >>> 28).toNat=0
  rw [BitVec.toNat_ushiftRight,Nat.shiftRight_eq_div_pow,BitVec.toNat_ofNat]
  change (n%4294967296)/268435456=0
  omega

theorem digits_guard (n : Nat) (hn : n<4294967296) :
    taken .eq (alu .and (alu .sltu 0#32 1#32)
      (alu .sltu (BitVec.ofNat 32 n) 8#32)) 0#32=decide (8≤n) := by
  rw [ChunkNumberMath.less n 8 hn (by decide)]
  by_cases h : n<8
  · simp [h,show ¬8≤n by omega,alu,taken]
  · simp [h,show 8≤n by omega,alu,taken]

theorem size_guard (n : Nat) (hn : n<4294967296) :
    taken .ne (alu .or 0#32 (alu .srl (BitVec.ofNat 32 n) 28#32)) 0#32=decide (268435455<n) := by
  apply Bool.eq_iff_iff.mpr
  simp only [taken,alu,BitVec.zero_or,bne_iff_ne,decide_eq_true_eq,ne_eq,←BitVec.toNat_inj]
  change ¬(((BitVec.ofNat 32 n) >>> 28).toNat=0) ↔ 268435455<n
  rw [BitVec.toNat_ushiftRight,Nat.shiftRight_eq_div_pow,BitVec.toNat_ofNat]
  change ¬((n%4294967296)/268435456=0) ↔ 268435455<n
  omega

end E5R.Thermostat.ChunkSizeMath
