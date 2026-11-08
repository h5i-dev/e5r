import Projects.thermostat.DigitWordMath
import Projects.thermostat.HttpPutMath
namespace E5R.Thermostat.HttpDecMath
open E5R E5R.Thermostat

/-- Word arithmetic for the actual HTTP body-length encoder. The main send
    Future clips its body window to 832 bytes; this lemma does not assume a
    decimal result from the Rust source. -/
theorem quotient100_nat (n : Nat) (hn : n≤832) : n*1374389535/137438953472=n/100 := by omega

theorem quotient10_nat (n : Nat) (hn : n≤832) : n*3435973837/34359738368=n/10 := by omega

theorem quotient100 (n : Nat) (hn : n≤832) :
    (muldiv .mulhu (BitVec.ofNat 32 n) 1374389535#32) >>> 5=BitVec.ofNat 32 (n/100) := by
  apply BitVec.eq_of_toNat_eq
  simp only [muldiv,BitVec.toNat_ofNat,BitVec.toNat_ushiftRight,Nat.shiftRight_eq_div_pow]
  change (((n%4294967296)*1374389535/4294967296)%4294967296)/32=(n/100)%4294967296
  have hn32 : n<4294967296 := by omega
  have hh : n*1374389535/4294967296<4294967296 := by omega
  rw [Nat.mod_eq_of_lt hn32,Nat.mod_eq_of_lt hh,Nat.mod_eq_of_lt (show n/100<4294967296 by omega) ]
  have hq := quotient100_nat n hn
  omega

theorem quotient10 (n : Nat) (hn : n≤832) :
    (muldiv .mulhu (BitVec.ofNat 32 n) 3435973837#32) >>> 3=BitVec.ofNat 32 (n/10) := by
  apply BitVec.eq_of_toNat_eq
  simp only [muldiv,BitVec.toNat_ofNat,BitVec.toNat_ushiftRight,Nat.shiftRight_eq_div_pow]
  change (((n%4294967296)*3435973837/4294967296)%4294967296)/8=(n/10)%4294967296
  have hn32 : n<4294967296 := by omega
  have hh : n*3435973837/4294967296<4294967296 := by omega
  rw [Nat.mod_eq_of_lt hn32,Nat.mod_eq_of_lt hh,Nat.mod_eq_of_lt (show n/10<4294967296 by omega) ]
  have hq := quotient10_nat n hn
  omega
theorem shift (n s : Nat) (hn : n<2^32) :
    (BitVec.ofNat 32 n) >>> s=BitVec.ofNat 32 (n/2^s) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ushiftRight,BitVec.toNat_ofNat,Nat.shiftRight_eq_div_pow]
  rw [Nat.mod_eq_of_lt hn,Nat.mod_eq_of_lt (show n/2^s<2^32 by have hh := Nat.div_le_self n (2^s);omega)]

theorem mulhu_shift_zero (n k s : Nat) (hn : n<2^32) (hk : k<2^32)
    (hh : n*k/4294967296<2^s) :
    (muldiv .mulhu (BitVec.ofNat 32 n) (BitVec.ofNat 32 k)) >>> s=0#32 := by
  apply BitVec.eq_of_toNat_eq
  simp only [muldiv,BitVec.toNat_ofNat,BitVec.toNat_ushiftRight,Nat.shiftRight_eq_div_pow]
  rw [Nat.mod_eq_of_lt hn,Nat.mod_eq_of_lt hk]
  change ((n*k/4294967296)%4294967296)/2^s=0
  apply Nat.div_eq_of_lt
  exact Nat.lt_of_le_of_lt (Nat.mod_le _ _) hh

theorem million_zero (n : Nat) (hn : n≤832) :
    (muldiv .mulhu ((BitVec.ofNat 32 n) >>> 5) 175921861#32) >>> 7=0#32 := by
  rw [shift n 5 (by omega)]
  exact mulhu_shift_zero (n/32) 175921861 7 (by omega) (by decide) (by change n/32*175921861/4294967296<128;omega)

theorem ten_thousand_zero (n : Nat) (hn : n≤832) :
    (muldiv .mulhu (BitVec.ofNat 32 n) 3518437209#32) >>> 13=0#32 :=
  mulhu_shift_zero n 3518437209 13 (by omega) (by decide) (by change n*3518437209/4294967296<8192;omega)

theorem thousand_zero (n : Nat) (hn : n≤832) :
    (muldiv .mulhu (BitVec.ofNat 32 n) 274877907#32) >>> 6=0#32 :=
  mulhu_shift_zero n 274877907 6 (by omega) (by decide) (by change n*274877907/4294967296<64;omega)

theorem mulhu_zero (n k : Nat) (hn : n<2^32) (hk : k<2^32) (hh : n*k<4294967296) :
    muldiv .mulhu (BitVec.ofNat 32 n) (BitVec.ofNat 32 k)=0#32 := by
  simp only [muldiv,BitVec.toNat_ofNat,Nat.mod_eq_of_lt hn,Nat.mod_eq_of_lt hk,Nat.div_eq_of_lt hh]
theorem ascii_or (n : Nat) (hn : n<10) : (BitVec.ofNat 32 n ||| 48#32)=BitVec.ofNat 32 (48+n) := by
  have h : ∀ d : Fin 10, (BitVec.ofNat 32 d.val ||| 48#32)=BitVec.ofNat 32 (48+d.val) := by decide +kernel
  exact h ⟨n,hn⟩

theorem low_tens (n : Nat) (hn : n≤832) :
    muldiv .mulhu (BitVec.ofNat 32 (n/100)) 429496730#32=0#32 :=
  mulhu_zero (n/100) 429496730 (by omega) (by decide) (by omega)

theorem tens_remainder (n : Nat) (hn : n≤832) :
    BitVec.ofNat 32 (n/10)-BitVec.ofNat 32 ((n/10)/10*10)=BitVec.ofNat 32 ((n/10)%10) := by
  have hq := Nat.mod_add_div (n/10) 10
  rw [BitVec.ofNat_sub_ofNat_of_le (n/10) ((n/10)/10*10) (by omega) (by omega)]
  congr 1
  omega
theorem branch_ltu (a b : Nat) (ha : a<2^32) (hb : b<2^32) :
    taken .ltu (BitVec.ofNat 32 a) (BitVec.ofNat 32 b)=decide (a<b) := by
  simp only [taken,BitVec.ult,BitVec.toNat_ofNat,Nat.mod_eq_of_lt ha,Nat.mod_eq_of_lt hb]

theorem branch_geu (a b : Nat) (ha : a<2^32) (hb : b<2^32) :
    taken .geu (BitVec.ofNat 32 a) (BitVec.ofNat 32 b)=decide (b≤a) := by
  change (!taken .ltu (BitVec.ofNat 32 a) (BitVec.ofNat 32 b))=_
  rw [branch_ltu a b ha hb]
  simp only [←decide_not,Nat.not_lt]
theorem exec_muldiv (c : Core) (len : Word) (op rd rs1 rs2) :
    exec c len (.muldiv op rd rs1 rs2)=.done (c.wr rd (muldiv op (c.get rs1) (c.get rs2)) (c.pc+len)) := rfl
theorem remaining_guard (pos count : Nat) (hp : pos≤94) (hc : count≤2) :
    taken .geu (BitVec.ofNat 32 count) (192#32-BitVec.ofNat 32 pos)=false := by
  have ht : (BitVec.ofNat 32 count).ult (192#32-BitVec.ofNat 32 pos)=true := by
    rw [BitVec.ult,BitVec.toNat_ofNat,HttpPutMath.remaining 192#32 pos count (by change pos+count≤192;omega)]
    change decide (count%4294967296<192-pos)=true
    exact decide_eq_true (by omega)
  change (!(BitVec.ofNat 32 count).ult (192#32-BitVec.ofNat 32 pos))=false
  rw [ht]
  rfl
end E5R.Thermostat.HttpDecMath
