import Projects.thermostat.HttpPutData
import Projects.thermostat.ParamMath
namespace E5R.Thermostat.HttpPutMath
open E5R E5R.Thermostat

theorem first_guard (cap : Word) (pos n : Nat) (h : pos+n≤cap.toNat) :
    alu .sltu cap (BitVec.ofNat 32 pos)=0#32 := by
  have hc := cap.isLt
  have hp : pos<2^32 := by omega
  have hn : cap.ult (BitVec.ofNat 32 pos)=false := by
    rw [BitVec.ult,BitVec.toNat_ofNat,Nat.mod_eq_of_lt hp]
    exact decide_eq_false (by omega)
  simp only [alu,hn,Bool.false_eq_true,ite_false]
  rfl

theorem remaining (cap : Word) (pos n : Nat) (h : pos+n≤cap.toNat) :
    (cap-BitVec.ofNat 32 pos).toNat=cap.toNat-pos := by
  have hc := cap.isLt
  have hp : pos<2^32 := by omega
  rw [BitVec.toNat_sub,BitVec.toNat_ofNat,Nat.mod_eq_of_lt hp]
  omega

theorem second_guard (cap : Word) (pos n : Nat) (h : pos+n≤cap.toNat) :
    alu .sltu (cap-BitVec.ofNat 32 pos) (BitVec.ofNat 32 n)=0#32 := by
  have hc := cap.isLt
  have hn : n<2^32 := by omega
  have hg : (cap-BitVec.ofNat 32 pos).ult (BitVec.ofNat 32 n)=false := by
    rw [BitVec.ult,remaining cap pos n h,BitVec.toNat_ofNat,Nat.mod_eq_of_lt hn]
    exact decide_eq_false (by omega)
  simp only [alu,hg,Bool.false_eq_true,ite_false]
  rfl

theorem setup_guard (cap : Word) (pos n : Nat) (hn : 0<n) (h : pos+n≤cap.toNat) :
    taken .ltu (cap-BitVec.ofNat 32 pos) (BitVec.ofNat 32 n+0xffffffff#32)=false := by
  have hc := cap.isLt
  have h32 : n<2^32 := by omega
  rw [ParamMath.decrement n hn]
  rw [taken,BitVec.ult,remaining cap pos n h,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (show n-1<2^32 by omega)]
  exact decide_eq_false (by omega)
theorem zero_guard (n : Nat) (hn : 0<n) (hb : n<2^32) :
    taken .eq (BitVec.ofNat 32 n) (0 : Word)=false := by
  have hz : BitVec.ofNat 32 n≠(0 : Word) := by
    intro he
    have hh := congrArg BitVec.toNat he
    rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt hb] at hh
    change n=0 at hh
    omega
  change BitVec.ofNat 32 n≠0#32 at hz
  simp [taken,hz]

theorem finish (src : Word) (n : Nat) (hn : 0<n) :
    (BitVec.ofNat 32 (n-1)+src)+1#32=src+BitVec.ofNat 32 n := by
  rw [BitVec.add_comm _ src,BitVec.add_assoc,←BitVec.ofNat_add,show n-1+1=n by omega]
def flag (cap : Word) (pos n : Nat) : Word :=
  (alu .sltu cap (BitVec.ofNat 32 pos)) |||
    (alu .sltu (cap-BitVec.ofNat 32 pos) (BitVec.ofNat 32 n))

theorem rejected (cap : Word) (pos n : Nat) (hp : pos<2^32) (hn : n<2^32)
    (h : ¬pos+n≤cap.toNat) : flag cap pos n=1#32 := by
  have hc := cap.isLt
  by_cases ho : cap.toNat<pos
  · have hu : cap.ult (BitVec.ofNat 32 pos)=true := by
      rw [BitVec.ult,BitVec.toNat_ofNat,Nat.mod_eq_of_lt hp]
      exact decide_eq_true ho
    simp only [flag,alu,hu,ite_true]
    cases hq : (cap-BitVec.ofNat 32 pos).ult (BitVec.ofNat 32 n) <;> simp only [hq,Bool.false_eq_true,ite_false,ite_true] <;> decide +kernel
  · have hu : cap.ult (BitVec.ofNat 32 pos)=false := by
      rw [BitVec.ult,BitVec.toNat_ofNat,Nat.mod_eq_of_lt hp]
      exact decide_eq_false ho
    have hs : (cap-BitVec.ofNat 32 pos).ult (BitVec.ofNat 32 n)=true := by
      rw [BitVec.ult,remaining cap pos 0 (by omega),BitVec.toNat_ofNat,Nat.mod_eq_of_lt hn]
      exact decide_eq_true (by omega)
    simp only [flag,alu,hu,hs,Bool.false_eq_true,ite_false,ite_true]
    decide +kernel
end E5R.Thermostat.HttpPutMath
