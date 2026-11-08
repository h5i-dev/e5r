import Projects.thermostat.ChunkMath
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
namespace E5R.Thermostat.ChunkByteFacts
open E5R E5R.Thermostat HttpRequestSpec

/-- Closed checks over all 256 byte values, using kernel reduction only. -/
theorem decimal_guard : ∀ b : BitVec 8,
    taken .ltu (alu .and (alu .add (BitVec.ofNat 32 b.toNat) 0xffffffd0#32) 255#32) 10#32=
      decide (48≤b.toNat ∧ b.toNat≤57) := by decide +kernel

theorem lower_guard : ∀ b : BitVec 8,
    taken .geu (alu .and (alu .add (BitVec.ofNat 32 b.toNat) 0xffffff9f#32) 255#32) 6#32=
      decide (¬(97≤b.toNat ∧ b.toNat≤102)) := by decide +kernel

theorem upper_guard : ∀ b : BitVec 8,
    taken .geu (alu .and (alu .add (BitVec.ofNat 32 b.toNat) 0xffffffbf#32) 255#32) 6#32=
      decide (¬(65≤b.toNat ∧ b.toNat≤70)) := by decide +kernel

theorem decimal_value : ∀ b : BitVec 8, 48≤b.toNat ∧ b.toNat≤57 →
    alu .add (BitVec.ofNat 32 b.toNat) 0xffffffd0#32=BitVec.ofNat 32 (hexv b.toNat) := by decide +kernel

theorem lower_value : ∀ b : BitVec 8, 97≤b.toNat ∧ b.toNat≤102 →
    alu .add (BitVec.ofNat 32 b.toNat) 0xffffffa9#32=BitVec.ofNat 32 (hexv b.toNat) := by decide +kernel

theorem upper_value : ∀ b : BitVec 8, 65≤b.toNat ∧ b.toNat≤70 →
    alu .add (BitVec.ofNat 32 b.toNat) 0xffffffc9#32=BitVec.ofNat 32 (hexv b.toNat) := by decide +kernel

theorem classes : ∀ b : BitVec 8,
    ((48≤b.toNat ∧ b.toNat≤57) ∨ (97≤b.toNat ∧ b.toNat≤102) ∨ (65≤b.toNat ∧ b.toNat≤70)) ↔ hexv b.toNat<16 := by decide +kernel

end E5R.Thermostat.ChunkByteFacts
