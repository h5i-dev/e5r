import Projects.thermostat.MainQuerySpec
import Projects.thermostat.HeadTargetMath
import Projects.thermostat.ChunkCapacityMath
namespace E5R.Thermostat.MainQueryMath
open E5R E5R.Thermostat

theorem question (b : BitVec 8) : taken .eq (BitVec.ofNat 32 b.toNat) 63#32=decide (b.toNat=63) := by
  simp only [taken]
  have inject : BitVec.ofNat 32 b.toNat=63#32 ↔ b.toNat=63 := by
    constructor
    · intro eq
      have h := congrArg BitVec.toNat eq
      simpa only [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by have := b.isLt;omega : b.toNat<2^32)] using h
    · intro eq;rw [eq]
  by_cases hit : b.toNat=63
  · simp [hit]
  · have ne : BitVec.ofNat 32 b.toNat≠63#32 := by intro eq;exact hit (inject.mp eq)
    simpa only [hit,decide_false,beq_eq_false_iff_ne] using ne

theorem again (start i finish : Nat) (lo : start≤i) (hi : i<finish) (bound : finish≤2048) :
    taken .ne (BitVec.ofNat 32 (finish-start)) (BitVec.ofNat 32 (i-start)+1#32)=decide (i+1<finish) := by
  rw [←BitVec.ofNat_add]
  have next : i-start+1=i+1-start := by omega
  rw [next]
  by_cases more : i+1<finish
  · have ne : BitVec.ofNat 32 (finish-start)≠BitVec.ofNat 32 (i+1-start) := by
      intro eq
      have h := congrArg BitVec.toNat eq
      simp only [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega : finish-start<2^32),Nat.mod_eq_of_lt (by omega : i+1-start<2^32)] at h
      omega
    simp [taken,more,ne]
  · have same : finish-start=i+1-start := by omega
    simp [taken,more,same]

theorem found_length (start i finish : Nat) (lo : start≤i) (hi : i<finish) (bound : finish≤2048) :
    (~~~BitVec.ofNat 32 start)+(BitVec.ofNat 32 finish-BitVec.ofNat 32 (i-start))=BitVec.ofNat 32 (finish-i-1) := by
  have sub : BitVec.ofNat 32 finish-BitVec.ofNat 32 (i-start)=BitVec.ofNat 32 (finish-(i-start)) :=
    BitVec.ofNat_sub_ofNat_of_le finish (i-start) (by omega) (by omega)
  rw [sub,HeadTargetMath.remaining start (finish-(i-start)) (by omega) (by omega)]
  congr 1
  omega

theorem offset_next (start i : Nat) (lo : start≤i) :
    BitVec.ofNat 32 (i-start)+1#32=BitVec.ofNat 32 (i+1-start) := by
  rw [←BitVec.ofNat_add]
  congr 1
  omega

def Frame (c d : Core) : Prop := ∀ r : Reg, r∉[12,13,14,15,28] → d.get r=c.get r

theorem Frame.trans {a b c : Core} (h : Frame a b) (k : Frame b c) : Frame a c :=
  fun r safe => (k r safe).trans (h r safe)
end E5R.Thermostat.MainQueryMath
