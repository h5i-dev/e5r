import Projects.thermostat.DigitMath
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
namespace E5R.Thermostat.DigitWordMath
open E5R E5R.Thermostat

theorem shifted16 (n : Nat) (hn : n < 65536) : (BitVec.ofNat 32 n <<< 16) >>> 20 = BitVec.ofNat 32 (n/16) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ushiftRight,BitVec.toNat_shiftLeft,BitVec.toNat_ofNat,Nat.shiftLeft_eq,Nat.shiftRight_eq_div_pow]
  change ((n%4294967296*65536)%4294967296)/1048576 = (n/16)%4294967296
  omega

theorem shifted4 (n : Nat) (hn : n < 65536) : (BitVec.ofNat 32 n <<< 16) >>> 18 = BitVec.ofNat 32 (n/4) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ushiftRight,BitVec.toNat_shiftLeft,BitVec.toNat_ofNat,Nat.shiftLeft_eq,Nat.shiftRight_eq_div_pow]
  change ((n%4294967296*65536)%4294967296)/262144 = (n/4)%4294967296
  omega

theorem quotient10000 (n : Nat) (hn : n ≤ 32768) :
    alu .srl (muldiv .mul (alu .srl (alu .sll (BitVec.ofNat 32 n) 16#32) 20#32) 839#32) 19#32 = BitVec.ofNat 32 (n/10000) := by
  change (((BitVec.ofNat 32 n <<< 16) >>> 20)*839#32) >>> 19 = _
  rw [shifted16 n (by omega)]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ushiftRight,BitVec.toNat_mul,BitVec.toNat_ofNat,Nat.shiftRight_eq_div_pow]
  have hd := DigitMath.div10000 n hn
  change (((n/16)%4294967296*839)%4294967296)/524288 = (n/10000)%4294967296
  have ha : n/16 < 4294967296 := by omega
  have hb : n/16*839 < 4294967296 := by omega
  have hc : n/10000 < 4294967296 := by omega
  rw [Nat.mod_eq_of_lt ha,Nat.mod_eq_of_lt hb,Nat.mod_eq_of_lt hc]
  exact hd

theorem quotient100 (n : Nat) (hn : n < 10000) :
    alu .srl (muldiv .mul (alu .srl (alu .sll (BitVec.ofNat 32 n) 16#32) 18#32) 5243#32) 17#32 = BitVec.ofNat 32 (n/100) := by
  change (((BitVec.ofNat 32 n <<< 16) >>> 18)*5243#32) >>> 17 = _
  rw [shifted4 n (by omega)]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ushiftRight,BitVec.toNat_mul,BitVec.toNat_ofNat,Nat.shiftRight_eq_div_pow]
  have hd := DigitMath.div100 n hn
  change (((n/4)%4294967296*5243)%4294967296)/131072 = (n/100)%4294967296
  have ha : n/4 < 4294967296 := by omega
  have hb : n/4*5243 < 4294967296 := by omega
  have hc : n/100 < 4294967296 := by omega
  rw [Nat.mod_eq_of_lt ha,Nat.mod_eq_of_lt hb,Nat.mod_eq_of_lt hc]
  exact hd

theorem mask2046 (n : Nat) (hn : n < 2048) : n &&& 2046 = n/2*2 := by
  have hf : ∀ n : Fin 2048, n.val &&& 2046 = n.val/2*2 := by decide +kernel
  exact hf ⟨n,hn⟩

theorem pair_index (n : Nat) (hn : n < 10000) :
    alu .and (alu .srl (muldiv .mul (alu .srl (alu .sll (BitVec.ofNat 32 n) 16#32) 18#32) 5243#32) 16#32) 2046#32 =
      BitVec.ofNat 32 (2*(n/100)) := by
  change ((((BitVec.ofNat 32 n <<< 16) >>> 18)*5243#32) >>> 16) &&& 2046#32 = _
  rw [shifted4 n (by omega)]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_and,BitVec.toNat_ushiftRight,BitVec.toNat_mul,BitVec.toNat_ofNat,Nat.shiftRight_eq_div_pow]
  change ((((n/4)%4294967296*5243)%4294967296)/65536) &&& 2046 = (2*(n/100))%4294967296
  have ha : n/4 < 4294967296 := by omega
  have hb : n/4*5243 < 4294967296 := by omega
  have hc : 2*(n/100) < 4294967296 := by omega
  rw [Nat.mod_eq_of_lt ha,Nat.mod_eq_of_lt hb,Nat.mod_eq_of_lt hc]
  rw [mask2046 _ (by omega)]
  exact DigitMath.pair_index n hn
end E5R.Thermostat.DigitWordMath
