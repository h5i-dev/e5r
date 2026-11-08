import Projects.thermostat.ChunkSizeMath
namespace E5R.Thermostat.ChunkCapacityMath
open E5R E5R.Thermostat

theorem sub (a b : Nat) (ha : a<4294967296) (hba : b≤a) :
    alu .sub (BitVec.ofNat 32 a) (BitVec.ofNat 32 b)=BitVec.ofNat 32 (a-b) := by
  exact BitVec.ofNat_sub_ofNat_of_le a b (by omega) hba

end E5R.Thermostat.ChunkCapacityMath
