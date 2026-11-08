import Projects.thermostat.MainWriteCode
import Projects.thermostat.QuietRam
import Projects.thermostat.Memory
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.MainWriteReady
open E5R E5R.Thermostat

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (fp : Word) (h8 : c.get 8=fp) (h18 : c.get 18=1#32) (hm : Memory.Block B fp 1332) (ha : fp.toNat%4=0) (hflag : ram (fp+1330#32)=0#8)
    (hp : c.pc=0x8000196c#32) :
    ∃ d, Quiet.Steps B img 3 ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc=0x80001998#32 ∧
      d.get 13=0#32 ∧ d.get 9=4#32 ∧ (∀ r : Reg, r≠13 → r≠9 → d.get r=c.get r) ∧ d.sameCsr c := by
  let c1 := c.wr 13 (0#32) 0x80001970#32
  let c2 := c1.wr 9 (4#32) 0x80001972#32
  let c3 := c2.goto 0x80001998#32
  have t0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine Quiet.step_of (by rw [hp];decide) (by rw [hp];exact mw2147490156) fun o => ?_
    change Observed.interp B img o (exec c _ _) ram 0 [] [] = ⟨.ok c1 ram [],[]⟩
    have v8 : c.get 8=fp := by simp [Core.wr_get_ne,Core.wr_get,h8,h18]
    rw [exec_load,v8,Quiet.interp_load_ram (B := B) (img := img) (w := .b) o (by exact Nat.mod_one _) (Memory.block_access hm (off := 1330) (by decide) (by decide)),Memory.load_byte,hflag];first | rfl | (rw [hp];rfl)
  have t1 : Quiet.Step B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    refine Quiet.step_of (by change (0x80001970#32).getLsbD 0=false;decide) mw2147490160 fun o => ?_
    change Observed.interp B img o (exec c1 _ _) ram 0 [] [] = ⟨.ok c2 ram [],[]⟩
    rw [exec_opimm,Core.get_zero];first | rfl | (rw [hp];rfl)
  have t2 : Quiet.Step B img ⟨c2,ram⟩ ⟨c3,ram⟩ := by
    refine Quiet.step_of (by change (0x80001972#32).getLsbD 0=false;decide) mw2147490162 fun o => ?_
    change Observed.interp B img o (exec c2 _ _) ram 0 [] [] = ⟨.ok c3 ram [],[]⟩
    have v13 : c2.get 13=0#32 := by simp [c2,c1,Core.wr_get_ne,Core.wr_get,h8,h18]
    have v18 : c2.get 18=1#32 := by simp [c2,c1,Core.wr_get_ne,Core.wr_get,h8,h18]
    rw [exec_branch,v13,v18,show taken .ne 0#32 1#32=true by decide]
    simp only [ite_true]
    rw [show c2.pc=0x80001972#32 by rfl,show 0x80001972#32+38#32=0x80001998#32 by decide +kernel,jump_ok _ _ (by decide)];first | rfl | (rw [hp];rfl)
  refine ⟨c3,.step t0 (.step t1 (.single t2)),rfl,?_ ,?_ ,?_ ,by rfl⟩
  · simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h18]
  · simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h18]
  · intro reg h13 h9;simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h18,h13,h9]
end E5R.Thermostat.MainWriteReady
