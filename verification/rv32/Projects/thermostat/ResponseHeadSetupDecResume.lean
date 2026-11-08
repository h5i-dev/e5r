import Projects.thermostat.ResponseHeadCode
import Projects.thermostat.QuietRam
import Projects.thermostat.Memory
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.ResponseHeadSetupDecResume
open E5R E5R.Thermostat

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (frame dst pos src count : Word) (h2 : c.get 2=frame+16#32) (h11 : c.get 11=pos) (h23 : c.get 23=dst) (hm : Memory.Block B frame 96) (ha : frame.toNat%4=0) (hc : ramRead ram (frame+40#32) .w=192#32) (h10 : c.get 10=1#32)
    (hp : c.pc=0x800040a4#32) :
    ∃ d, Quiet.Steps B img 3 ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc=0x800040ac#32 ∧
      d.get 13=1#32 ∧ d.get 12=pos ∧ (∀ r : Reg, r≠13 → r≠12 → d.get r=c.get r) ∧ d.sameCsr c := by
  let c1 := c.wr 13 (1#32) 0x800040a6#32
  let c2 := c1.goto 0x800040aa#32
  let c3 := c2.wr 12 (pos) 0x800040ac#32
  have t0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine Quiet.step_of (by rw [hp];decide) (by rw [hp];exact rh2147500196) fun o => ?_
    change Observed.interp B img o (exec c _ _) ram 0 [] [] = ⟨.ok c1 ram [],[]⟩
    rw [exec_opimm,Core.get_zero];first | rfl | (rw [hp];rfl)
  have t1 : Quiet.Step B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    refine Quiet.step_of (by change (0x800040a6#32).getLsbD 0=false;decide) rh2147500198 fun o => ?_
    change Observed.interp B img o (exec c1 _ _) ram 0 [] [] = ⟨.ok c2 ram [],[]⟩
    have v10 : c1.get 10=1#32 := by simp [c1,Core.wr_get_ne,Core.wr_get,h2,h11,h23,h10]
    have v13 : c1.get 13=1#32 := by simp [c1,Core.wr_get_ne,Core.wr_get,h2,h11,h23,h10]
    rw [exec_branch,v10,v13,show taken .ne 1#32 1#32=false by decide]
    simp only [Bool.false_eq_true,ite_false];first | rfl | (rw [hp]; rfl)
  have t2 : Quiet.Step B img ⟨c2,ram⟩ ⟨c3,ram⟩ := by
    refine Quiet.step_of (by change (0x800040aa#32).getLsbD 0=false;decide) rh2147500202 fun o => ?_
    change Observed.interp B img o (exec c2 _ _) ram 0 [] [] = ⟨.ok c3 ram [],[]⟩
    have v11 : c2.get 11=pos := by simp [c2,c1,Core.wr_get_ne,Core.wr_get,h2,h11,h23,h10]
    rw [exec_op,Core.get_zero,v11,(show alu .add (0 : Word) (pos)=pos from BitVec.zero_add _)];first | rfl | (rw [hp];rfl)
  refine ⟨c3,.step t0 (.step t1 (.single t2)),rfl,?_ ,?_ ,?_ ,by rfl⟩
  · simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h11,h23,h10]
  · simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h11,h23,h10]
  · intro reg h13 h12;simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h11,h23,h10,h13,h12]
end E5R.Thermostat.ResponseHeadSetupDecResume
