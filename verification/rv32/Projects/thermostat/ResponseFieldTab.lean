import Projects.thermostat.ResponseHeadCode
import Projects.thermostat.QuietRam
import Projects.thermostat.ResponseFieldMath
import Projects.thermostat.Memory
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.ResponseFieldTab
open E5R E5R.Thermostat

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (src : Word) (v : BitVec 8) (h29 : c.get 29=src) (h6 : c.get 6=9#32) (hs : ReadBytes.Byte B img ram src v) (h9 : v.toNat=9)
    (hp : c.pc=0x80003eb0#32) :
    ∃ d, Quiet.Steps B img 2 ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc=0x80003ea8#32 ∧
      d.get 31=ResponseFieldMath.word v ∧ (∀ r : Reg, r≠31 → d.get r=c.get r) ∧ d.sameCsr c := by
  let c1 := c.wr 31 (ResponseFieldMath.word v) 0x80003eb4#32
  let c2 := c1.goto 0x80003ea8#32
  have t0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine Quiet.step_of (by rw [hp];decide) (by rw [hp];exact rh2147499696) fun o => ?_
    change Observed.interp B img o (exec c _ _) ram 0 [] [] = ⟨.ok c1 ram [],[]⟩
    rw [exec_load,h29,BitVec.add_zero,ObservedByte.load hs o _ 0 [] [],ReadBytes.extend_byte,hp];first | rfl | (rw [hp];rfl)
  have t1 : Quiet.Step B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    refine Quiet.step_of (by change (0x80003eb4#32).getLsbD 0=false;decide) rh2147499700 fun o => ?_
    change Observed.interp B img o (exec c1 _ _) ram 0 [] [] = ⟨.ok c2 ram [],[]⟩
    have v31 : c1.get 31=ResponseFieldMath.word v := by simp [c1,Core.wr_get_ne,Core.wr_get,h29,h6]
    have v6 : c1.get 6=9#32 := by simp [c1,Core.wr_get_ne,Core.wr_get,h29,h6]
    rw [exec_branch,v31,v6,ResponseFieldMath.equal v 9 (by decide),decide_eq_true h9]
    simp only [ite_true]
    rw [show c1.pc=0x80003eb4#32 by rfl,show 0x80003eb4#32+0xfffffff4#32=0x80003ea8#32 by decide +kernel,jump_ok _ _ (by decide)];first | rfl | (rw [hp];rfl)
  refine ⟨c2,.step t0 (.single t1),rfl,?_ ,?_ ,by rfl⟩
  · simp [c2,c1,Core.wr_get_ne,Core.wr_get,h29,h6]
  · intro reg h31;simp [c2,c1,Core.wr_get_ne,Core.wr_get,h29,h6,h31]
end E5R.Thermostat.ResponseFieldTab
