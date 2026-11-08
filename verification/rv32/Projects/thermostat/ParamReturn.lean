import Projects.thermostat.ParamCode
import Projects.thermostat.WireSpec
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
namespace E5R.Thermostat.ParamReturn
open E5R E5R.Thermostat

def Result (c : Core) : Option Word → Prop
  | none => c.get 10 = 0#32
  | some v => c.get 10 = 1#32 ∧ c.get 11 = v

theorem none (B : Board) (c : Core) (ram : Word → BitVec 8) (hp : c.pc = 0x800027be#32) :
    ∃ d, DetSteps B img 2 ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc = c.get 1 &&& ~~~1 ∧ Result d none ∧
      (∀ r : Reg, r ≠ 10 → d.get r = c.get r) ∧ d.sameCsr c := by
  let c1 := c.wr 10 0#32 0x800027c0#32
  let d := c1.goto (c.get 1 &&& ~~~1)
  have s0 : DetStep B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine detStep_of (by rw [hp];decide) (by rw [hp];exact pm2147493822) fun o => ?_
    rw [exec_opimm,Core.get_zero,hp];rfl
  have s1 : DetStep B img ⟨c1,ram⟩ ⟨d,ram⟩ := by
    refine detStep_of (by change (0x800027c0#32).getLsbD 0 = false;decide) pm2147493824 fun o => ?_
    have hv : c1.get 1 = c.get 1 := by simp [c1,Core.wr_get_ne]
    rw [exec_jalr,hv,BitVec.add_zero,jump_ok _ _ (clear_bit0 _)];rfl
  refine ⟨d,.step s0 (.single s1),rfl,?_,?_,by rfl⟩
  · change d.get 10 = 0#32;simp [d,c1,Core.wr_get]
  · intro r hr;simp [d,c1,Core.wr_get_ne,hr]

theorem range_flag (n : Nat) (hn : n < 10000000000) :
    alu .sltu (BitVec.ofNat 32 (n/4294967296)) 1#32 =
      (if n ≤ 4294967295 then 1#32 else 0#32) := by
  have hh : (BitVec.ofNat 32 (n/4294967296)).ult 1#32 = decide (n ≤ 4294967295) := by
    rw [BitVec.ult,BitVec.toNat_ofNat]
    change decide ((n/4294967296)%4294967296 < 1) = _
    have hi : (n/4294967296)%4294967296 < 1 ↔ n ≤ 4294967295 := by omega
    simp only [hi]
  change (if (BitVec.ofNat 32 (n/4294967296)).ult 1#32 then 1#32 else 0#32) = _
  rw [hh];simp only [decide_eq_true_eq]

theorem range (B : Board) (c : Core) (ram : Word → BitVec 8) (n : Nat)
    (hn : n < 10000000000) (hp : c.pc = 0x8000280e#32) (hv : c.get 13 = BitVec.ofNat 32 (n/4294967296)) :
    ∃ d, DetSteps B img 2 ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc = c.get 1 &&& ~~~1 ∧
      d.get 10 = (if n ≤ 4294967295 then 1#32 else 0#32) ∧
      (∀ r : Reg, r ≠ 10 → d.get r = c.get r) ∧ d.sameCsr c := by
  let c1 := c.wr 10 (if n ≤ 4294967295 then 1#32 else 0#32) 0x80002812#32
  let d := c1.goto (c.get 1 &&& ~~~1)
  have s0 : DetStep B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine detStep_of (by rw [hp];decide) (by rw [hp];exact pm2147493902) fun o => ?_
    rw [exec_opimm,hv,range_flag n hn,hp];rfl
  have s1 : DetStep B img ⟨c1,ram⟩ ⟨d,ram⟩ := by
    refine detStep_of (by change (0x80002812#32).getLsbD 0 = false;decide) pm2147493906 fun o => ?_
    have hv : c1.get 1 = c.get 1 := by simp [c1,Core.wr_get_ne]
    rw [exec_jalr,hv,BitVec.add_zero,jump_ok _ _ (clear_bit0 _)];rfl
  refine ⟨d,.step s0 (.single s1),rfl,?_,?_,by rfl⟩
  · simp [d,c1,Core.wr_get]
  · intro r hr;simp [d,c1,Core.wr_get_ne,hr]
end E5R.Thermostat.ParamReturn
