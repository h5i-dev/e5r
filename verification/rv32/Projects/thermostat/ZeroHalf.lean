import Projects.thermostat.Memory
namespace E5R.Thermostat.Memory
open E5R

theorem word_zero_half {ram : Word → BitVec 8} {p : Word} (h : ramRead ram p .w = 0#32) : ramRead ram p .h = 0#32 := by
  have h0 := (ram p).isLt
  have h1 := (ram (p+1)).isLt
  have h2 := (ram (p+2)).isLt
  have h3 := (ram (p+3)).isLt
  have hn := congrArg BitVec.toNat h
  change ((ram p).toNat+256*(ram (p+1)).toNat+65536*(ram (p+2)).toNat+16777216*(ram (p+3)).toNat)%4294967296 = 0 at hn
  have hs : (ram p).toNat+256*(ram (p+1)).toNat+65536*(ram (p+2)).toNat+16777216*(ram (p+3)).toNat < 4294967296 := by omega
  rw [Nat.mod_eq_of_lt hs] at hn
  apply BitVec.eq_of_toNat_eq
  change ((ram p).toNat+256*(ram (p+1)).toNat)%4294967296 = 0
  omega
end E5R.Thermostat.Memory
