import Projects.thermostat.MainHeaderCode
import Projects.thermostat.QuietRam
import Projects.thermostat.Memory
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.MainHeaderResultReject
open E5R E5R.Thermostat

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (fp status : Word) (h8 : c.get 8=fp) (h1324 : extend .h false (ramRead ram (fp+1324#32) .h)=status)
(object : Memory.Block B fp 1326) (aligned : fp.toNat%4=0)
    (hp : c.pc=0x80000a42#32) :
    ∃ d, Quiet.Steps B img 4 ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc=0x80000a9a#32 ∧
      d.get 18=0#32 ∧ d.get 27=status ∧ d.get 9=3#32 ∧ (∀ r : Reg, r≠18 → r≠27 → r≠9 → d.get r=c.get r) ∧ d.sameCsr c := by
  let c1 := c.wr 18 (0#32) 0x80000a44#32
  let c2 := c1.wr 27 (status) 0x80000a48#32
  let c3 := c2.wr 9 (3#32) 0x80000a4a#32
  let c4 := c3.goto 0x80000a9a#32
  have t0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine Quiet.step_of (by rw [hp];decide) (by rw [hp];exact mh2147486274) fun o => ?_
    change Observed.interp B img o (exec c _ _) ram 0 [] [] = ⟨.ok c1 ram [],[]⟩
    rw [exec_opimm,Core.get_zero];first | rfl | (rw [hp];rfl)
  have t1 : Quiet.Step B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    refine Quiet.step_of (by change (0x80000a44#32).getLsbD 0=false;decide) mh2147486276 fun o => ?_
    change Observed.interp B img o (exec c1 _ _) ram 0 [] [] = ⟨.ok c2 ram [],[]⟩
    have v8 : c1.get 8=fp := by simp [c1,Core.wr_get_ne,Core.wr_get,h8]
    rw [exec_load,v8,Quiet.interp_load_ram (B := B) (img := img) (w := .h) o (Memory.half_aligned fp 662 (by omega)) (Memory.block_access object (off := 1324) (by decide) (by decide)),h1324];first | rfl | (rw [hp];rfl)
  have t2 : Quiet.Step B img ⟨c2,ram⟩ ⟨c3,ram⟩ := by
    refine Quiet.step_of (by change (0x80000a48#32).getLsbD 0=false;decide) mh2147486280 fun o => ?_
    change Observed.interp B img o (exec c2 _ _) ram 0 [] [] = ⟨.ok c3 ram [],[]⟩
    rw [exec_opimm,Core.get_zero];first | rfl | (rw [hp];rfl)
  have t3 : Quiet.Step B img ⟨c3,ram⟩ ⟨c4,ram⟩ := by
    refine Quiet.step_of (by change (0x80000a4a#32).getLsbD 0=false;decide) mh2147486282 fun o => ?_
    change Observed.interp B img o (exec c3 _ _) ram 0 [] [] = ⟨.ok c4 ram [],[]⟩
    rw [exec_jal,Core.set_zero]
    change Observed.interp B img o (jump c3 (0x80000a4a#32+80#32)) ram 0 [] []=_
    rw [show 0x80000a4a#32+80#32=0x80000a9a#32 by decide +kernel,jump_ok _ _ (by decide)];first | rfl | (rw [hp];rfl)
  refine ⟨c4,.step t0 (.step t1 (.step t2 (.single t3))),rfl,?_ ,?_ ,?_ ,?_ ,by rfl⟩
  · simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8]
  · simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8]
  · simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8]
  · intro reg h18 h27 h9;simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h18,h27,h9]
end E5R.Thermostat.MainHeaderResultReject
