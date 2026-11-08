import Projects.thermostat.ReadBytes
import Projects.thermostat.Observed
namespace E5R.Thermostat.HeadObservedByte
open E5R E5R.Thermostat

/-- Both deterministic byte-read cases from the unchanged platform, including
    RAM precedence over ROM. Device reads cannot satisfy this view. -/
theorem load {B image ram a v} (h : ReadBytes.Byte B image ram a v) (o : Oracle)
    (k : Word → Eff) (i : Nat) (evs : List Event) (reads : List Observed.Read) :
    Observed.interp B image o (.load .b a false k) ram i evs reads =
      Observed.interp B image o (k (BitVec.ofNat 32 v.toNat)) ram i evs reads := by
  cases h with
  | ram inside value =>
    simp only [Observed.interp,Width.bytes,Nat.mod_one,ne_eq,not_true_eq_false,ite_false,inside,ite_true]
    change Observed.interp B image o (k (BitVec.ofNat 32 (ram a).toNat)) ram i evs reads = _
    rw [value]
  | rom outside value =>
    simp only [Observed.interp,Width.bytes,Nat.mod_one,ne_eq,not_true_eq_false,ite_false,outside,Bool.false_eq_true,value]
end E5R.Thermostat.HeadObservedByte
