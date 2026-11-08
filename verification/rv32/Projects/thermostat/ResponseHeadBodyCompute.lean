import Projects.thermostat.ResponseHeadCode
import Projects.thermostat.QuietRam
import Projects.thermostat.ResponseHeadBodyMath
import Projects.thermostat.Memory
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.ResponseHeadBodyCompute
open E5R E5R.Thermostat

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8)  (status : Nat) (hs : status≤599) (h12 : c.get 12=BitVec.ofNat 32 status)
    (hp : c.pc=0x80003ee2#32) :
    ∃ d, Quiet.Steps B img 8 ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc=0x80003f02#32 ∧
      d.get 17=((alu .sltu (BitVec.ofNat 32 status) 200#32) ^^^ 1#32) ∧ d.get 5=((ResponseHeadBodyMath.not204 status) &&& (ResponseHeadBodyMath.not304 status)) ∧ d.get 6=ResponseHeadBodyMath.not304 status ∧ d.get 25=ResponseHeadBodyMath.boolWord (ResponseHeadSpec.hasBody status) ∧ (∀ r : Reg, r≠17 → r≠5 → r≠6 → r≠25 → d.get r=c.get r) ∧ d.sameCsr c := by
  let c1 := c.wr 17 (alu .sltu (BitVec.ofNat 32 status) 200#32) 0x80003ee6#32
  let c2 := c1.wr 5 (BitVec.ofNat 32 status+0xffffff34#32) 0x80003eea#32
  let c3 := c2.wr 6 (BitVec.ofNat 32 status+0xfffffed0#32) 0x80003eee#32
  let c4 := c3.wr 5 (ResponseHeadBodyMath.not204 status) 0x80003ef2#32
  let c5 := c4.wr 6 (ResponseHeadBodyMath.not304 status) 0x80003ef6#32
  let c6 := c5.wr 17 (((alu .sltu (BitVec.ofNat 32 status) 200#32) ^^^ 1#32)) 0x80003efa#32
  let c7 := c6.wr 5 (((ResponseHeadBodyMath.not204 status) &&& (ResponseHeadBodyMath.not304 status))) 0x80003efe#32
  let c8 := c7.wr 25 (ResponseHeadBodyMath.boolWord (ResponseHeadSpec.hasBody status)) 0x80003f02#32
  have t0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine Quiet.step_of (by rw [hp];decide) (by rw [hp];exact rh2147499746) fun o => ?_
    change Observed.interp B img o (exec c _ _) ram 0 [] [] = ⟨.ok c1 ram [],[]⟩
    rw [exec_opimm,h12,hp];first | rfl | (rw [hp];rfl)
  have t1 : Quiet.Step B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    refine Quiet.step_of (by change (0x80003ee6#32).getLsbD 0=false;decide) rh2147499750 fun o => ?_
    change Observed.interp B img o (exec c1 _ _) ram 0 [] [] = ⟨.ok c2 ram [],[]⟩
    have v12 : c1.get 12=BitVec.ofNat 32 status := by simp [c1,Core.wr_get_ne,Core.wr_get,h12]
    rw [exec_opimm,v12];first | rfl | (rw [hp];rfl)
  have t2 : Quiet.Step B img ⟨c2,ram⟩ ⟨c3,ram⟩ := by
    refine Quiet.step_of (by change (0x80003eea#32).getLsbD 0=false;decide) rh2147499754 fun o => ?_
    change Observed.interp B img o (exec c2 _ _) ram 0 [] [] = ⟨.ok c3 ram [],[]⟩
    have v12 : c2.get 12=BitVec.ofNat 32 status := by simp [c2,c1,Core.wr_get_ne,Core.wr_get,h12]
    rw [exec_opimm,v12];first | rfl | (rw [hp];rfl)
  have t3 : Quiet.Step B img ⟨c3,ram⟩ ⟨c4,ram⟩ := by
    refine Quiet.step_of (by change (0x80003eee#32).getLsbD 0=false;decide) rh2147499758 fun o => ?_
    change Observed.interp B img o (exec c3 _ _) ram 0 [] [] = ⟨.ok c4 ram [],[]⟩
    have v5 : c3.get 5=BitVec.ofNat 32 status+0xffffff34#32 := by simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,h12]
    rw [exec_op,Core.get_zero,v5];first | rfl | (rw [hp];rfl)
  have t4 : Quiet.Step B img ⟨c4,ram⟩ ⟨c5,ram⟩ := by
    refine Quiet.step_of (by change (0x80003ef2#32).getLsbD 0=false;decide) rh2147499762 fun o => ?_
    change Observed.interp B img o (exec c4 _ _) ram 0 [] [] = ⟨.ok c5 ram [],[]⟩
    have v6 : c4.get 6=BitVec.ofNat 32 status+0xfffffed0#32 := by simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h12]
    rw [exec_op,Core.get_zero,v6];first | rfl | (rw [hp];rfl)
  have t5 : Quiet.Step B img ⟨c5,ram⟩ ⟨c6,ram⟩ := by
    refine Quiet.step_of (by change (0x80003ef6#32).getLsbD 0=false;decide) rh2147499766 fun o => ?_
    change Observed.interp B img o (exec c5 _ _) ram 0 [] [] = ⟨.ok c6 ram [],[]⟩
    have v17 : c5.get 17=alu .sltu (BitVec.ofNat 32 status) 200#32 := by simp [c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h12]
    rw [exec_opimm,v17];first | rfl | (rw [hp];rfl)
  have t6 : Quiet.Step B img ⟨c6,ram⟩ ⟨c7,ram⟩ := by
    refine Quiet.step_of (by change (0x80003efa#32).getLsbD 0=false;decide) rh2147499770 fun o => ?_
    change Observed.interp B img o (exec c6 _ _) ram 0 [] [] = ⟨.ok c7 ram [],[]⟩
    have v5 : c6.get 5=ResponseHeadBodyMath.not204 status := by simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h12]
    have v6 : c6.get 6=ResponseHeadBodyMath.not304 status := by simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h12]
    rw [exec_op,v5,v6];first | rfl | (rw [hp];rfl)
  have t7 : Quiet.Step B img ⟨c7,ram⟩ ⟨c8,ram⟩ := by
    refine Quiet.step_of (by change (0x80003efe#32).getLsbD 0=false;decide) rh2147499774 fun o => ?_
    change Observed.interp B img o (exec c7 _ _) ram 0 [] [] = ⟨.ok c8 ram [],[]⟩
    have v5 : c7.get 5=((ResponseHeadBodyMath.not204 status) &&& (ResponseHeadBodyMath.not304 status)) := by simp [c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h12]
    have v17 : c7.get 17=((alu .sltu (BitVec.ofNat 32 status) 200#32) ^^^ 1#32) := by simp [c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h12]
    rw [exec_op,v5,v17]
    change Observed.interp B img o (.done (c7.wr 25 (ResponseHeadBodyMath.computed status) 0x80003f02#32)) ram 0 [] [] = _
    rw [ResponseHeadBodyMath.value status hs];first | rfl | (rw [hp];rfl)
  refine ⟨c8,.step t0 (.step t1 (.step t2 (.step t3 (.step t4 (.step t5 (.step t6 (.single t7))))))),rfl,?_ ,?_ ,?_ ,?_ ,?_ ,by rfl⟩
  · simp [c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h12]
  · simp [c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h12]
  · simp [c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h12]
  · simp [c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h12]
  · intro reg h17 h5 h6 h25;simp [c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h12,h17,h5,h6,h25]
end E5R.Thermostat.ResponseHeadBodyCompute
