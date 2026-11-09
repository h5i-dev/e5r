import Projects.thermostat.MainRouterCode
import Projects.thermostat.QuietRam
import Projects.thermostat.Memory
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.RouteLiteralCall
open E5R E5R.Thermostat

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (path start pattern : Word) (h20 : c.get 20=path) (h10 : c.get 10=start) (h13 : c.get 13=pattern)
    (hp : c.pc=0x80002902#32) :
    ∃ d, Quiet.Steps B img 4 ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc=0x80005162#32 ∧
      d.get 11=path+start ∧ d.get 10=pattern ∧ d.get 1=0x80002910#32 ∧ (∀ r : Reg, r≠11 → r≠10 → r≠1 → d.get r=c.get r) ∧ d.sameCsr c := by
  let c1 := c.wr 11 (path+start) 0x80002906#32
  let c2 := c1.wr 10 (pattern) 0x80002908#32
  let c3 := c2.wr 1 (0x80005908#32) 0x8000290c#32
  let c4 := c3.wr 1 (0x80002910#32) 0x80005162#32
  have t0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine Quiet.step_of (by rw [hp];decide) (by rw [hp];exact rt2147494146) fun o => ?_
    change Observed.interp B img o (exec c _ _) ram 0 [] [] = ⟨.ok c1 ram [],[]⟩
    have p : c.get 20=path := by simp [Core.wr_get_ne,Core.wr_get,h20,h10,h13]
    have s : c.get 10=start := by simp [Core.wr_get_ne,Core.wr_get,h20,h10,h13]
    rw [exec_op,p,s];first | rfl | (rw [hp];rfl)
  have t1 : Quiet.Step B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    refine Quiet.step_of (by change (0x80002906#32).getLsbD 0=false;decide) rt2147494150 fun o => ?_
    change Observed.interp B img o (exec c1 _ _) ram 0 [] [] = ⟨.ok c2 ram [],[]⟩
    have p : c1.get 13=pattern := by simp [c1,Core.wr_get_ne,Core.wr_get,h20,h10,h13]
    rw [exec_op,Core.get_zero,p]
    change Observed.interp B img o (.done (c1.wr 10 (0#32+pattern) 0x80002908#32)) ram 0 [] []=_
    rw [BitVec.zero_add];first | rfl | (rw [hp];rfl)
  have t2 : Quiet.Step B img ⟨c2,ram⟩ ⟨c3,ram⟩ := by
    refine Quiet.step_of (by change (0x80002908#32).getLsbD 0=false;decide) rt2147494152 fun o => ?_
    change Observed.interp B img o (exec c2 _ _) ram 0 [] [] = ⟨.ok c3 ram [],[]⟩
    rw [exec_auipc];first | rfl | (rw [hp];rfl)
  have t3 : Quiet.Step B img ⟨c3,ram⟩ ⟨c4,ram⟩ := by
    refine Quiet.step_of (by change (0x8000290c#32).getLsbD 0=false;decide) rt2147494156 fun o => ?_
    change Observed.interp B img o (exec c3 _ _) ram 0 [] [] = ⟨.ok c4 ram [],[]⟩
    have ra : c3.get 1=0x80005908#32 := by simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,h20,h10,h13]
    rw [exec_jalr,ra]
    change Observed.interp B img o (jump (c3.set 1 0x80002910#32) 0x80005162#32) ram 0 [] []=_
    rw [jump_ok _ _ (by decide)];first | rfl | (rw [hp];rfl)
  refine ⟨c4,.step t0 (.step t1 (.step t2 (.single t3))),rfl,?_ ,?_ ,?_ ,?_ ,by rfl⟩
  · simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h20,h10,h13]
  · simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h20,h10,h13]
  · simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h20,h10,h13]
  · intro reg h11 h10 h1;simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h20,h10,h13,h11,h10,h1]
end E5R.Thermostat.RouteLiteralCall
