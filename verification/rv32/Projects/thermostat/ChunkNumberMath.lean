import Projects.thermostat.ChunkMath
namespace E5R.Thermostat.ChunkNumberMath
open E5R E5R.Thermostat

theorem less (a b : Nat) (ha : a<4294967296) (hb : b<4294967296) :
    alu .sltu (BitVec.ofNat 32 a) (BitVec.ofNat 32 b) =
      if a<b then 1#32 else 0#32 := by
  simp only [alu,BitVec.ult,BitVec.toNat_ofNat,Nat.mod_eq_of_lt ha,Nat.mod_eq_of_lt hb]
  split <;> simp_all

theorem zero_size (n : Nat) (hn : n<4294967296) :
    taken .eq (alu .or (BitVec.ofNat 32 n) 0#32) 0#32=decide (n=0) := by
  simp only [alu,BitVec.or_zero]
  exact ChunkMath.eq_guard n 0 hn (by decide)

theorem small_guard (n : Nat) (hn : n<4294967296) :
    taken .eq (alu .and (alu .sltu 0#32 1#32)
      (alu .sltu (BitVec.ofNat 32 n) 2#32)) 0#32=decide (2≤n) := by
  rw [less n 2 hn (by decide)]
  by_cases h : n<2
  · simp [h,show ¬2≤n by omega,alu,taken]
  · simp [h,show 2≤n by omega,alu,taken]

theorem decrement (n : Nat) (hn : n<4294967296) (hpos : 0<n) :
    alu .add (BitVec.ofNat 32 n) 0xffffffff#32=BitVec.ofNat 32 (n-1) := by
  simp only [alu]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add,show (0xffffffff#32).toNat=4294967295 by decide +kernel]
  simp only [BitVec.toNat_ofNat]
  omega

theorem borrow_zero (n : Nat) (hn : n<4294967296) (hpos : 0<n) :
    alu .sub 0#32 (alu .sltu (BitVec.ofNat 32 n) 1#32)=0#32 := by
  rw [less n 1 hn (by decide),if_neg (by omega)]
  rfl

end E5R.Thermostat.ChunkNumberMath
