import Projects.thermostat.SignedMagnitudeExtra
import Projects.thermostat.ReplyJson
namespace E5R.Thermostat.SignedMagnitude
open E5R E5R.Thermostat

theorem negative_iff (v : BitVec 16) : v.toInt < 0 ↔ ¬v.toNat < 32768 := by
  have hv := v.isLt
  rw [BitVec.toInt_eq_toNat_cond]
  split <;> omega

theorem signed_positive (v : BitVec 16) (h : v.toNat < 32768) :
    ReplyJson.signed v = ReplyJson.decimal v.toInt.natAbs := by
  have hn : ¬v.toInt < 0 := fun hh => (negative_iff v).mp hh h
  rw [ReplyJson.signed,ite_eq_right hn]
  rfl

theorem signed_negative (v : BitVec 16) (h : ¬v.toNat < 32768) :
    ReplyJson.signed v = 45#8::ReplyJson.decimal v.toInt.natAbs := by
  rw [ReplyJson.signed,ite_eq_left ((negative_iff v).mpr h)]
  rfl
end E5R.Thermostat.SignedMagnitude
