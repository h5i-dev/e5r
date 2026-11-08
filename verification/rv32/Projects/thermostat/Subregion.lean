import Projects.thermostat.WordRegions
import Projects.thermostat.Memory
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
namespace E5R.Thermostat.Subregion
open E5R E5R.Thermostat

theorem right {a n b m} (h : WordRegions.Disjoint a n b m) (k len : Nat) (hk : k+len ≤ m) :
    WordRegions.Disjoint a n (b+BitVec.ofNat 32 k) len := by
  intro i j
  have hj := j.isLt
  simpa only [BitVec.ofNat_add,BitVec.add_assoc] using h i ⟨k+j.val,by omega⟩

theorem left {a n b m} (h : WordRegions.Disjoint a n b m) (k len : Nat) (hk : k+len ≤ n) :
    WordRegions.Disjoint (a+BitVec.ofNat 32 k) len b m := WordRegions.symm (right (WordRegions.symm h) k len hk)

/-- Unlike sub_block, this also covers a valid empty one-past slice, with an
    explicit strict address-space bound to exclude wrapping to zero. -/
theorem block {B p cap} (h : Memory.Block B p cap) (_hc : cap < 2^32)
    (hw : p.toNat+cap < 2^32) (off len : Nat) (hl : off+len ≤ cap) :
    Memory.Block B (p+BitVec.ofNat 32 off) len := by
  have ho : off < 2^32 := by omega
  have hp : p.toNat+off < 2^32 := by omega
  unfold Memory.Block
  rw [BitVec.toNat_add,BitVec.toNat_ofNat,Nat.mod_eq_of_lt ho,Nat.mod_eq_of_lt hp]
  obtain ⟨hbase,hend,_⟩ := h
  exact ⟨by omega,by omega,by omega⟩

theorem nowrap {p : Word} {cap} (hw : p.toNat+cap < 2^32) (off len : Nat) (hl : off+len ≤ cap) :
    (p+BitVec.ofNat 32 off).toNat+len < 2^32 := by
  have ho : off < 2^32 := by omega
  have hp : p.toNat+off < 2^32 := by omega
  rw [BitVec.toNat_add,BitVec.toNat_ofNat,Nat.mod_eq_of_lt ho,Nat.mod_eq_of_lt hp]
  omega
end E5R.Thermostat.Subregion
