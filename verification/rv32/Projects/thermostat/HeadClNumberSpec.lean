import Projects.thermostat.HeadClNumberMath
import Projects.thermostat.HttpRequestSpec
namespace E5R.Thermostat.HeadClNumberSpec
open E5R E5R.Thermostat HttpRequestSpec

theorem unfoldLoop (g : Nat → Nat) (finish acc pos : Nat) (byte : BitVec 8) (inside : pos<finish) (value : g pos=byte.toNat) :
    clLoop g finish 1024 acc pos=
      (if DecimalSpec.digit byte then
        if 1024<HeadClNumberMath.next acc byte then .bad 413
        else clLoop g finish 1024 (HeadClNumberMath.next acc byte) (pos+1)
      else .bad 400) := by
  rw [clLoop]
  simp only [inside,ite_true,value]
  cases digit : DecimalSpec.digit byte with
  | false =>
    have notDigit : ¬(48≤byte.toNat ∧ byte.toNat≤57) := by simpa only [DecimalSpec.digit,decide_eq_false_iff_not] using digit
    have invalid : byte.toNat<48 ∨ 57<byte.toNat := by omega
    simp only [invalid,ite_true,digit,Bool.false_eq_true,ite_false]
  | true =>
    have numeric : 48≤byte.toNat ∧ byte.toNat≤57 := by simpa only [DecimalSpec.digit,decide_eq_true_eq] using digit
    have valid : ¬(byte.toNat<48 ∨ 57<byte.toNat) := by omega
    simp only [valid,ite_false,digit,ite_true,HeadClNumberMath.next,Nat.mul_comm acc 10]
    rfl

theorem finish (g : Nat → Nat) (pos acc : Nat) : clLoop g pos 1024 acc pos=.ok acc := by
  rw [clLoop,ite_eq_right (Nat.lt_irrefl pos)]
end E5R.Thermostat.HeadClNumberSpec
