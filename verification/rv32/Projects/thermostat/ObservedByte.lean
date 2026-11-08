import Projects.thermostat.Observed
import Projects.thermostat.ReadBytes
namespace E5R.Thermostat.ObservedByte
open E5R E5R.Thermostat

/-- A checked RAM/ROM byte access is quiet in the observed interpreter.
    This does not infer silence from deterministic return values alone. -/
theorem load {B img ram a v} (h : ReadBytes.Byte B img ram a v) (o : Oracle) (k : Word → Eff)
    (i : Nat) (evs : List Event) (reads : List Observed.Read) :
    Observed.interp B img o (.load .b a false k) ram i evs reads =
      Observed.interp B img o (k (BitVec.ofNat 32 v.toNat)) ram i evs reads := by
  cases h with
  | ram hi hv => simp [Observed.interp,Width.bytes,Nat.mod_one,hi,ramRead,hv]
  | rom ho hv => simp [Observed.interp,Width.bytes,Nat.mod_one,ho,hv]
end E5R.Thermostat.ObservedByte
