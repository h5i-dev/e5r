import Projects.thermostat.Quiet
namespace E5R.Thermostat.MainMethodByteMath
open E5R

theorem words (b : BitVec 8) (literal : Nat) (bound : literal≤255) :
    BitVec.ofNat 32 b.toNat=BitVec.ofNat 32 literal ↔ b.toNat=literal := by
  constructor
  · intro eq
    have h := congrArg BitVec.toNat eq
    simpa only [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by have := b.isLt;omega : b.toNat<2^32),Nat.mod_eq_of_lt (by omega : literal<2^32)] using h
  · intro eq;rw [eq]

theorem eqTest (b : BitVec 8) (literal : Nat) (bound : literal≤255) :
    taken .eq (BitVec.ofNat 32 b.toNat) (BitVec.ofNat 32 literal)=decide (b.toNat=literal) := by
  simp only [taken,Bool.beq_eq_decide_eq,words b literal bound]

theorem neTest (b : BitVec 8) (literal : Nat) (bound : literal≤255) :
    taken .ne (BitVec.ofNat 32 b.toNat) (BitVec.ofNat 32 literal)=decide (b.toNat≠literal) := by
  simp only [taken,bne_eq,Bool.beq_eq_decide_eq,words b literal bound,decide_not]
end E5R.Thermostat.MainMethodByteMath
