import Projects.thermostat.MainWriteCode
import Projects.thermostat.QuietRam
import Projects.thermostat.Memory
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.MainWriteCaller
open E5R E5R.Thermostat

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (sp obj : Word) (h2 : c.get 2=sp) (h24 : c.get 24=obj)
    (hp : c.pc=0x8000195a#32) :
    ∃ d, Quiet.Steps B img 6 ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc=0x800004c6#32 ∧
      d.get 10=sp+4520#32 ∧ d.get 11=obj ∧ d.get 1=0x8000196c#32 ∧ (∀ r : Reg, r≠10 → r≠11 → r≠1 → d.get r=c.get r) ∧ d.sameCsr c := by
  let c1 := c.wr 10 (4096#32) 0x8000195c#32
  let c2 := c1.wr 10 (4520#32) 0x80001960#32
  let c3 := c2.wr 10 (sp+4520#32) 0x80001962#32
  let c4 := c3.wr 11 (obj) 0x80001964#32
  let c5 := c4.wr 1 (0x80000964#32) 0x80001968#32
  let c6 := c5.wr 1 (0x8000196c#32) 0x800004c6#32
  have t0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine Quiet.step_of (by rw [hp];decide) (by rw [hp];exact mw2147490138) fun o => ?_
    change Observed.interp B img o (exec c _ _) ram 0 [] [] = ⟨.ok c1 ram [],[]⟩
    rw [exec_lui,hp];first | rfl | (rw [hp];rfl)
  have t1 : Quiet.Step B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    refine Quiet.step_of (by change (0x8000195c#32).getLsbD 0=false;decide) mw2147490140 fun o => ?_
    change Observed.interp B img o (exec c1 _ _) ram 0 [] [] = ⟨.ok c2 ram [],[]⟩
    have v10 : c1.get 10=4096#32 := by simp [c1,Core.wr_get_ne,Core.wr_get,h2,h24]
    rw [exec_opimm,v10];first | rfl | (rw [hp];rfl)
  have t2 : Quiet.Step B img ⟨c2,ram⟩ ⟨c3,ram⟩ := by
    refine Quiet.step_of (by change (0x80001960#32).getLsbD 0=false;decide) mw2147490144 fun o => ?_
    change Observed.interp B img o (exec c2 _ _) ram 0 [] [] = ⟨.ok c3 ram [],[]⟩
    have v10 : c2.get 10=4520#32 := by simp [c2,c1,Core.wr_get_ne,Core.wr_get,h2,h24]
    have v2 : c2.get 2=sp := by simp [c2,c1,Core.wr_get_ne,Core.wr_get,h2,h24]
    rw [exec_op,v10,v2,(show alu .add 4520#32 sp=sp+4520#32 from BitVec.add_comm _ _)];first | rfl | (rw [hp];rfl)
  have t3 : Quiet.Step B img ⟨c3,ram⟩ ⟨c4,ram⟩ := by
    refine Quiet.step_of (by change (0x80001962#32).getLsbD 0=false;decide) mw2147490146 fun o => ?_
    change Observed.interp B img o (exec c3 _ _) ram 0 [] [] = ⟨.ok c4 ram [],[]⟩
    have v24 : c3.get 24=obj := by simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h24]
    rw [exec_op,Core.get_zero,v24,(show alu .add (0 : Word) obj=obj from BitVec.zero_add _)];first | rfl | (rw [hp];rfl)
  have t4 : Quiet.Step B img ⟨c4,ram⟩ ⟨c5,ram⟩ := by
    refine Quiet.step_of (by change (0x80001964#32).getLsbD 0=false;decide) mw2147490148 fun o => ?_
    change Observed.interp B img o (exec c4 _ _) ram 0 [] [] = ⟨.ok c5 ram [],[]⟩
    rw [exec_auipc,show c4.pc=0x80001964#32 by rfl,show 0x80001964#32+0xfffff000#32=0x80000964#32 by decide +kernel];first | rfl | (rw [hp];rfl)
  have t5 : Quiet.Step B img ⟨c5,ram⟩ ⟨c6,ram⟩ := by
    refine Quiet.step_of (by change (0x80001968#32).getLsbD 0=false;decide) mw2147490152 fun o => ?_
    change Observed.interp B img o (exec c5 _ _) ram 0 [] [] = ⟨.ok c6 ram [],[]⟩
    have v1 : c5.get 1=0x80000964#32 := by simp [c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h24]
    rw [exec_jalr,v1]
    change Observed.interp B img o (jump (c5.set 1 (0x80001968#32+4#32)) ((0x80000964#32+0xfffffb62#32) &&& ~~~1)) ram 0 [] [] = _
    rw [show (0x80000964#32+0xfffffb62#32) &&& ~~~1=0x800004c6#32 by decide +kernel,jump_ok _ _ (by decide)];first | rfl | (rw [hp];rfl)
  refine ⟨c6,.step t0 (.step t1 (.step t2 (.step t3 (.step t4 (.single t5))))),rfl,?_ ,?_ ,?_ ,?_ ,by rfl⟩
  · simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h24]
  · simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h24]
  · simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h24]
  · intro reg h10 h11 h1;simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h24,h10,h11,h1]
end E5R.Thermostat.MainWriteCaller
