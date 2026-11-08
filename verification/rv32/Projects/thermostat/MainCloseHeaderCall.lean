import Projects.thermostat.MainCloseCode
import Projects.thermostat.QuietRam
import Projects.thermostat.Memory
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.MainCloseHeaderCall
open E5R E5R.Thermostat

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (sp : Word) (h2 : c.get 2=sp)
    (hp : c.pc=0x80001266#32) :
    ∃ d, Quiet.Steps B img 4 ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc=0x800023f2#32 ∧
      d.get 10=sp+3312#32 ∧ d.get 1=0x80001276#32 ∧ (∀ r : Reg, r≠10 → r≠1 → d.get r=c.get r) ∧ d.sameCsr c := by
  let c1 := c.wr 10 (sp+2047#32) 0x8000126a#32
  let c2 := c1.wr 10 (sp+3312#32) 0x8000126e#32
  let c3 := c2.wr 1 (0x8000226e#32) 0x80001272#32
  let c4 := c3.wr 1 (0x80001276#32) 0x800023f2#32
  have t0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine Quiet.step_of (by rw [hp];decide) (by rw [hp];exact re2147488358) fun o => ?_
    change Observed.interp B img o (exec c _ _) ram 0 [] [] = ⟨.ok c1 ram [],[]⟩
    have v2 : c.get 2=sp := by simp [Core.wr_get_ne,Core.wr_get,h2]
    rw [exec_opimm,v2];first | rfl | (rw [hp];rfl)
  have t1 : Quiet.Step B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    refine Quiet.step_of (by change (0x8000126a#32).getLsbD 0=false;decide) re2147488362 fun o => ?_
    change Observed.interp B img o (exec c1 _ _) ram 0 [] [] = ⟨.ok c2 ram [],[]⟩
    have v10 : c1.get 10=sp+2047#32 := by simp [c1,Core.wr_get_ne,Core.wr_get,h2]
    rw [exec_opimm,v10]
    change Observed.interp B img o (Eff.done (c1.wr 10 ((sp+2047#32)+1265#32) 0x8000126e#32)) ram 0 [] []=_
    rw [BitVec.add_assoc,show 2047#32+1265#32=3312#32 by decide +kernel];first | rfl | (rw [hp];rfl)
  have t2 : Quiet.Step B img ⟨c2,ram⟩ ⟨c3,ram⟩ := by
    refine Quiet.step_of (by change (0x8000126e#32).getLsbD 0=false;decide) re2147488366 fun o => ?_
    change Observed.interp B img o (exec c2 _ _) ram 0 [] [] = ⟨.ok c3 ram [],[]⟩
    rw [exec_auipc];first | rfl | (rw [hp];rfl)
  have t3 : Quiet.Step B img ⟨c3,ram⟩ ⟨c4,ram⟩ := by
    refine Quiet.step_of (by change (0x80001272#32).getLsbD 0=false;decide) re2147488370 fun o => ?_
    change Observed.interp B img o (exec c3 _ _) ram 0 [] [] = ⟨.ok c4 ram [],[]⟩
    have v1 : c3.get 1=0x8000226e#32 := by simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2]
    rw [exec_jalr,v1]
    change Observed.interp B img o (jump (c3.set 1 0x80001276#32) ((0x8000226e#32+388#32) &&& ~~~1)) ram 0 [] []=_
    rw [show (0x8000226e#32+388#32) &&& ~~~1=0x800023f2#32 by decide +kernel,jump_ok _ _ (by decide)];first | rfl | (rw [hp];rfl)
  refine ⟨c4,.step t0 (.step t1 (.step t2 (.single t3))),rfl,?_ ,?_ ,?_ ,by rfl⟩
  · simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2]
  · simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2]
  · intro reg h10 h1;simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h10,h1]
end E5R.Thermostat.MainCloseHeaderCall
