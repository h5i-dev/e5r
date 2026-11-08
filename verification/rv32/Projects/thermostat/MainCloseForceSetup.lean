import Projects.thermostat.MainCloseCode
import Projects.thermostat.QuietRam
import Projects.thermostat.Memory
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.MainCloseForceSetup
open E5R E5R.Thermostat

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (sp : Word) (h2 : c.get 2=sp)
    (hp : c.pc=0x80001278#32) :
    ∃ d, Quiet.Steps B img 6 ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc=0x8000128c#32 ∧
      d.get 20=5#32 ∧ d.get 21=6#32 ∧ d.get 24=sp+3740#32 ∧ d.get 25=sp+3784#32 ∧ (∀ r : Reg, r≠20 → r≠21 → r≠24 → r≠25 → d.get r=c.get r) ∧ d.sameCsr c := by
  let c1 := c.wr 20 (5#32) 0x8000127a#32
  let c2 := c1.wr 21 (6#32) 0x8000127c#32
  let c3 := c2.wr 24 (sp+2047#32) 0x80001280#32
  let c4 := c3.wr 24 (sp+3740#32) 0x80001284#32
  let c5 := c4.wr 25 (sp+2047#32) 0x80001288#32
  let c6 := c5.wr 25 (sp+3784#32) 0x8000128c#32
  have t0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine Quiet.step_of (by rw [hp];decide) (by rw [hp];exact re2147488376) fun o => ?_
    change Observed.interp B img o (exec c _ _) ram 0 [] [] = ⟨.ok c1 ram [],[]⟩
    rw [exec_opimm,Core.get_zero];first | rfl | (rw [hp];rfl)
  have t1 : Quiet.Step B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    refine Quiet.step_of (by change (0x8000127a#32).getLsbD 0=false;decide) re2147488378 fun o => ?_
    change Observed.interp B img o (exec c1 _ _) ram 0 [] [] = ⟨.ok c2 ram [],[]⟩
    rw [exec_opimm,Core.get_zero];first | rfl | (rw [hp];rfl)
  have t2 : Quiet.Step B img ⟨c2,ram⟩ ⟨c3,ram⟩ := by
    refine Quiet.step_of (by change (0x8000127c#32).getLsbD 0=false;decide) re2147488380 fun o => ?_
    change Observed.interp B img o (exec c2 _ _) ram 0 [] [] = ⟨.ok c3 ram [],[]⟩
    have v2 : c2.get 2=sp := by simp [c2,c1,Core.wr_get_ne,Core.wr_get,h2]
    rw [exec_opimm,v2];first | rfl | (rw [hp];rfl)
  have t3 : Quiet.Step B img ⟨c3,ram⟩ ⟨c4,ram⟩ := by
    refine Quiet.step_of (by change (0x80001280#32).getLsbD 0=false;decide) re2147488384 fun o => ?_
    change Observed.interp B img o (exec c3 _ _) ram 0 [] [] = ⟨.ok c4 ram [],[]⟩
    have v24 : c3.get 24=sp+2047#32 := by simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2]
    rw [exec_opimm,v24]
    change Observed.interp B img o (Eff.done (c3.wr 24 ((sp+2047#32)+1693#32) 0x80001284#32)) ram 0 [] []=_
    rw [BitVec.add_assoc,show 2047#32+1693#32=3740#32 by decide +kernel];first | rfl | (rw [hp];rfl)
  have t4 : Quiet.Step B img ⟨c4,ram⟩ ⟨c5,ram⟩ := by
    refine Quiet.step_of (by change (0x80001284#32).getLsbD 0=false;decide) re2147488388 fun o => ?_
    change Observed.interp B img o (exec c4 _ _) ram 0 [] [] = ⟨.ok c5 ram [],[]⟩
    have v2 : c4.get 2=sp := by simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2]
    rw [exec_opimm,v2];first | rfl | (rw [hp];rfl)
  have t5 : Quiet.Step B img ⟨c5,ram⟩ ⟨c6,ram⟩ := by
    refine Quiet.step_of (by change (0x80001288#32).getLsbD 0=false;decide) re2147488392 fun o => ?_
    change Observed.interp B img o (exec c5 _ _) ram 0 [] [] = ⟨.ok c6 ram [],[]⟩
    have v25 : c5.get 25=sp+2047#32 := by simp [c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2]
    rw [exec_opimm,v25]
    change Observed.interp B img o (Eff.done (c5.wr 25 ((sp+2047#32)+1737#32) 0x8000128c#32)) ram 0 [] []=_
    rw [BitVec.add_assoc,show 2047#32+1737#32=3784#32 by decide +kernel];first | rfl | (rw [hp];rfl)
  refine ⟨c6,.step t0 (.step t1 (.step t2 (.step t3 (.step t4 (.single t5))))),rfl,?_ ,?_ ,?_ ,?_ ,?_ ,by rfl⟩
  · simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2]
  · simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2]
  · simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2]
  · simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2]
  · intro reg h20 h21 h24 h25;simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h20,h21,h24,h25]
end E5R.Thermostat.MainCloseForceSetup
