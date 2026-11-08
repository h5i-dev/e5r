import Projects.thermostat.HttpParseCode
import Projects.thermostat.QuietRam
import Projects.thermostat.Memory
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.HeadVersionOffset
open E5R E5R.Thermostat

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (m length offset : Word) (h17 : c.get 17=m) (h12 : c.get 12=length) (h30 : c.get 30=offset)
(ht : taken .eq (offset+(m-length)) 0xfffffffd#32=false)
    (hp : c.pc=0x80002e3e#32) :
    ∃ d, Quiet.Steps B img 4 ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc=0x80002e4a#32 ∧
      d.get 10=0xfffffffd#32 ∧ d.get 30=offset+(m-length) ∧ (∀ r : Reg, r≠10 → r≠30 → d.get r=c.get r) ∧ d.sameCsr c := by
  let c1 := c.wr 10 (m-length) 0x80002e42#32
  let c2 := c1.wr 30 (offset+(m-length)) 0x80002e44#32
  let c3 := c2.wr 10 (0xfffffffd#32) 0x80002e46#32
  let c4 := c3.goto 0x80002e4a#32
  have t0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine Quiet.step_of (by rw [hp];decide) (by rw [hp];exact hh2147495486) fun o => ?_
    change Observed.interp B img o (exec c _ _) ram 0 [] [] = ⟨.ok c1 ram [],[]⟩
    rw [exec_op,h17,h12];first | rfl | (rw [hp];rfl)
  have t1 : Quiet.Step B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    refine Quiet.step_of (by change (0x80002e42#32).getLsbD 0=false;decide) hh2147495490 fun o => ?_
    change Observed.interp B img o (exec c1 _ _) ram 0 [] [] = ⟨.ok c2 ram [],[]⟩
    have v30 : c1.get 30=offset := by simp [c1,Core.wr_get_ne,Core.wr_get,h17,h12,h30]
    have v10 : c1.get 10=m-length := by simp [c1,Core.wr_get_ne,Core.wr_get,h17,h12,h30]
    rw [exec_op,v30,v10];first | rfl | (rw [hp];rfl)
  have t2 : Quiet.Step B img ⟨c2,ram⟩ ⟨c3,ram⟩ := by
    refine Quiet.step_of (by change (0x80002e44#32).getLsbD 0=false;decide) hh2147495492 fun o => ?_
    change Observed.interp B img o (exec c2 _ _) ram 0 [] [] = ⟨.ok c3 ram [],[]⟩
    rw [exec_opimm,Core.get_zero];first | rfl | (rw [hp];rfl)
  have t3 : Quiet.Step B img ⟨c3,ram⟩ ⟨c4,ram⟩ := by
    refine Quiet.step_of (by change (0x80002e46#32).getLsbD 0=false;decide) hh2147495494 fun o => ?_
    change Observed.interp B img o (exec c3 _ _) ram 0 [] [] = ⟨.ok c4 ram [],[]⟩
    have v30 : c3.get 30=offset+(m-length) := by simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,h17,h12,h30]
    have v10 : c3.get 10=0xfffffffd#32 := by simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,h17,h12,h30]
    rw [exec_branch,v30,v10,ht];first | rfl | (rw [hp];rfl)
  refine ⟨c4,.step t0 (.step t1 (.step t2 (.single t3))),rfl,?_ ,?_ ,?_ ,by rfl⟩
  · simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h17,h12,h30]
  · simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h17,h12,h30]
  · intro reg h10 h30;simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h17,h12,h30,h10,h30]
end E5R.Thermostat.HeadVersionOffset
