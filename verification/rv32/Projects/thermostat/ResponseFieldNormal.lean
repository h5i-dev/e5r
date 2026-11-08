import Projects.thermostat.ResponseHeadCode
import Projects.thermostat.QuietRam
import Projects.thermostat.ResponseFieldMath
import Projects.thermostat.Memory
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.ResponseFieldNormal
open E5R E5R.Thermostat

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (src : Word) (v : BitVec 8) (h29 : c.get 29=src) (h6 : c.get 6=9#32) (hs : ReadBytes.Byte B img ram src v) (h7 : c.get 7=32#32) (h28 : c.get 28=127#32) (hf : ResponseHeadSpec.fieldByte v) (h9 : v.toNat≠9)
    (hp : c.pc=0x80003eb0#32) :
    ∃ d, Quiet.Steps B img 4 ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc=0x80003ea8#32 ∧
      d.get 31=ResponseFieldMath.word v ∧ (∀ r : Reg, r≠31 → d.get r=c.get r) ∧ d.sameCsr c := by
  let c1 := c.wr 31 (ResponseFieldMath.word v) 0x80003eb4#32
  let c2 := c1.goto 0x80003eb8#32
  let c3 := c2.goto 0x80003ebc#32
  let c4 := c3.goto 0x80003ea8#32
  have t0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine Quiet.step_of (by rw [hp];decide) (by rw [hp];exact rh2147499696) fun o => ?_
    change Observed.interp B img o (exec c _ _) ram 0 [] [] = ⟨.ok c1 ram [],[]⟩
    rw [exec_load,h29,BitVec.add_zero,ObservedByte.load hs o _ 0 [] [],ReadBytes.extend_byte,hp];first | rfl | (rw [hp];rfl)
  have t1 : Quiet.Step B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    refine Quiet.step_of (by change (0x80003eb4#32).getLsbD 0=false;decide) rh2147499700 fun o => ?_
    change Observed.interp B img o (exec c1 _ _) ram 0 [] [] = ⟨.ok c2 ram [],[]⟩
    have v31 : c1.get 31=ResponseFieldMath.word v := by simp [c1,Core.wr_get_ne,Core.wr_get,h29,h6,h7,h28]
    have v6 : c1.get 6=9#32 := by simp [c1,Core.wr_get_ne,Core.wr_get,h29,h6,h7,h28]
    rw [exec_branch,v31,v6,ResponseFieldMath.equal v 9 (by decide),decide_eq_false h9]
    simp only [Bool.false_eq_true,ite_false];first | rfl | (rw [hp];rfl)
  have t2 : Quiet.Step B img ⟨c2,ram⟩ ⟨c3,ram⟩ := by
    refine Quiet.step_of (by change (0x80003eb8#32).getLsbD 0=false;decide) rh2147499704 fun o => ?_
    change Observed.interp B img o (exec c2 _ _) ram 0 [] [] = ⟨.ok c3 ram [],[]⟩
    have v31 : c2.get 31=ResponseFieldMath.word v := by simp [c2,c1,Core.wr_get_ne,Core.wr_get,h29,h6,h7,h28]
    have v7 : c2.get 7=32#32 := by simp [c2,c1,Core.wr_get_ne,Core.wr_get,h29,h6,h7,h28]
    rw [exec_branch,v31,v7,ResponseFieldMath.less v 32 (by decide),decide_eq_false (show ¬v.toNat<32 by have hh := ResponseFieldMath.normal hf h9;omega)]
    simp only [Bool.false_eq_true,ite_false];first | rfl | (rw [hp];rfl)
  have t3 : Quiet.Step B img ⟨c3,ram⟩ ⟨c4,ram⟩ := by
    refine Quiet.step_of (by change (0x80003ebc#32).getLsbD 0=false;decide) rh2147499708 fun o => ?_
    change Observed.interp B img o (exec c3 _ _) ram 0 [] [] = ⟨.ok c4 ram [],[]⟩
    have v31 : c3.get 31=ResponseFieldMath.word v := by simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,h29,h6,h7,h28]
    have v28 : c3.get 28=127#32 := by simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,h29,h6,h7,h28]
    rw [exec_branch,v31,v28,ResponseFieldMath.not_equal v 127 (by decide),decide_eq_true (ResponseFieldMath.normal hf h9).2]
    simp only [ite_true]
    rw [show c3.pc=0x80003ebc#32 by rfl,show 0x80003ebc#32+0xffffffec#32=0x80003ea8#32 by decide +kernel,jump_ok _ _ (by decide)];first | rfl | (rw [hp];rfl)
  refine ⟨c4,.step t0 (.step t1 (.step t2 (.single t3))),rfl,?_ ,?_ ,by rfl⟩
  · simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h29,h6,h7,h28]
  · intro reg h31;simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h29,h6,h7,h28,h31]
end E5R.Thermostat.ResponseFieldNormal
