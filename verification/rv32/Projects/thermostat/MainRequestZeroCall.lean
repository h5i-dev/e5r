import Projects.thermostat.MainRequestBuildCode
import Projects.thermostat.QuietRam
import Projects.thermostat.Memory
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.MainRequestZeroCall
open E5R E5R.Thermostat

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (sp : Word) (h2 : c.get 2=sp)
    (hp : c.pc=0x80001230#32) :
    ∃ d, Quiet.Steps B img 6 ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc=0x80005638#32 ∧
      d.get 12=36#32 ∧ d.get 10=sp+3648#32 ∧ d.get 11=0#32 ∧ d.get 1=0x80001246#32 ∧ (∀ r : Reg, r≠12 → r≠10 → r≠11 → r≠1 → d.get r=c.get r) ∧ d.sameCsr c := by
  let c1 := c.wr 12 (36#32) 0x80001234#32
  let c2 := c1.wr 10 (sp+2047#32) 0x80001238#32
  let c3 := c2.wr 10 (sp+3648#32) 0x8000123c#32
  let c4 := c3.wr 11 (0#32) 0x8000123e#32
  let c5 := c4.wr 1 (0x8000523e#32) 0x80001242#32
  let c6 := c5.wr 1 (0x80001246#32) 0x80005638#32
  have t0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine Quiet.step_of (by rw [hp];decide) (by rw [hp];exact re2147488304) fun o => ?_
    change Observed.interp B img o (exec c _ _) ram 0 [] [] = ⟨.ok c1 ram [],[]⟩
    rw [exec_opimm,Core.get_zero];first | rfl | (rw [hp];rfl)
  have t1 : Quiet.Step B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    refine Quiet.step_of (by change (0x80001234#32).getLsbD 0=false;decide) re2147488308 fun o => ?_
    change Observed.interp B img o (exec c1 _ _) ram 0 [] [] = ⟨.ok c2 ram [],[]⟩
    have v2 : c1.get 2=sp := by simp [c1,Core.wr_get_ne,Core.wr_get,h2]
    rw [exec_opimm,v2];first | rfl | (rw [hp];rfl)
  have t2 : Quiet.Step B img ⟨c2,ram⟩ ⟨c3,ram⟩ := by
    refine Quiet.step_of (by change (0x80001238#32).getLsbD 0=false;decide) re2147488312 fun o => ?_
    change Observed.interp B img o (exec c2 _ _) ram 0 [] [] = ⟨.ok c3 ram [],[]⟩
    have v10 : c2.get 10=sp+2047#32 := by simp [c2,c1,Core.wr_get_ne,Core.wr_get,h2]
    rw [exec_opimm,v10]
    change Observed.interp B img o (Eff.done (c2.wr 10 ((sp+2047#32)+1601#32) 0x8000123c#32)) ram 0 [] []=_
    rw [BitVec.add_assoc,show 2047#32+1601#32=3648#32 by decide +kernel];first | rfl | (rw [hp];rfl)
  have t3 : Quiet.Step B img ⟨c3,ram⟩ ⟨c4,ram⟩ := by
    refine Quiet.step_of (by change (0x8000123c#32).getLsbD 0=false;decide) re2147488316 fun o => ?_
    change Observed.interp B img o (exec c3 _ _) ram 0 [] [] = ⟨.ok c4 ram [],[]⟩
    rw [exec_opimm,Core.get_zero];first | rfl | (rw [hp];rfl)
  have t4 : Quiet.Step B img ⟨c4,ram⟩ ⟨c5,ram⟩ := by
    refine Quiet.step_of (by change (0x8000123e#32).getLsbD 0=false;decide) re2147488318 fun o => ?_
    change Observed.interp B img o (exec c4 _ _) ram 0 [] [] = ⟨.ok c5 ram [],[]⟩
    rw [exec_auipc];first | rfl | (rw [hp];rfl)
  have t5 : Quiet.Step B img ⟨c5,ram⟩ ⟨c6,ram⟩ := by
    refine Quiet.step_of (by change (0x80001242#32).getLsbD 0=false;decide) re2147488322 fun o => ?_
    change Observed.interp B img o (exec c5 _ _) ram 0 [] [] = ⟨.ok c6 ram [],[]⟩
    have v1 : c5.get 1=0x8000523e#32 := by simp [c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2]
    rw [exec_jalr,v1]
    change Observed.interp B img o (jump (c5.set 1 0x80001246#32) ((0x8000523e#32+1018#32) &&& ~~~1)) ram 0 [] []=_
    rw [show (0x8000523e#32+1018#32) &&& ~~~1=0x80005638#32 by decide +kernel,jump_ok _ _ (by decide)];first | rfl | (rw [hp];rfl)
  refine ⟨c6,.step t0 (.step t1 (.step t2 (.step t3 (.step t4 (.single t5))))),rfl,?_ ,?_ ,?_ ,?_ ,?_ ,by rfl⟩
  · simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2]
  · simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2]
  · simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2]
  · simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2]
  · intro reg h12 h10 h11 h1;simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h12,h10,h11,h1]
end E5R.Thermostat.MainRequestZeroCall
