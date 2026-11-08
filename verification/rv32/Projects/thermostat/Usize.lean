import Projects.thermostat.Memory
namespace E5R.Thermostat.Usize
open E5R

theorem ofNat_eq (n k : Nat) (hn : n < 2^32) (hk : k < 2^32) :
    BitVec.ofNat 32 n = BitVec.ofNat 32 k ↔ n = k := by
  constructor
  · intro h
    have hh := congrArg BitVec.toNat h
    simpa only [BitVec.toNat_ofNat,Nat.mod_eq_of_lt hn,Nat.mod_eq_of_lt hk] using hh
  · intro h;rw [h]

theorem eq (n k : Nat) (hn : n < 2^32) (hk : k < 2^32) :
    taken .eq (BitVec.ofNat 32 n) (BitVec.ofNat 32 k) = decide (n = k) := by
  change decide (BitVec.ofNat 32 n = BitVec.ofNat 32 k) = _
  simp only [ofNat_eq n k hn hk]

theorem ne (n k : Nat) (hn : n < 2^32) (hk : k < 2^32) :
    taken .ne (BitVec.ofNat 32 n) (BitVec.ofNat 32 k) = decide (n ≠ k) := by
  change decide (BitVec.ofNat 32 n ≠ BitVec.ofNat 32 k) = _
  simp only [ne_eq,ofNat_eq n k hn hk]
end E5R.Thermostat.Usize
