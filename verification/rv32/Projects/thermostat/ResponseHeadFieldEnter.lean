import Projects.thermostat.ResponseHeadCode
import Projects.thermostat.QuietRam
import Projects.thermostat.HttpPutMath
import Projects.thermostat.Memory
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.ResponseHeadFieldEnter
open E5R E5R.Thermostat

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (ptr : Word) (len : Nat) (hpos : 0<len) (hlen : len≤16) (h13 : c.get 13=ptr) (h14 : c.get 14=BitVec.ofNat 32 len)
    (hp : c.pc=0x80003e82#32) :
    ∃ d, Quiet.Steps B img 13 ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc=0x80003eb0#32 ∧
      d.get 9=1#32 ∧ d.get 6=9#32 ∧ d.get 18=0x80005d19#32 ∧ d.get 21=0x80005d0b#32 ∧ d.get 7=32#32 ∧ d.get 28=127#32 ∧ d.get 29=ptr ∧ d.get 30=BitVec.ofNat 32 len ∧ d.get 17=0#32 ∧ (∀ r : Reg, r≠9 → r≠6 → r≠18 → r≠21 → r≠7 → r≠28 → r≠29 → r≠30 → r≠17 → d.get r=c.get r) ∧ d.sameCsr c := by
  let c1 := c.wr 9 (1#32) 0x80003e84#32
  let c2 := c1.goto 0x80003e86#32
  let c3 := c2.wr 6 (9#32) 0x80003e88#32
  let c4 := c3.wr 18 (0x80006000#32) 0x80003e8c#32
  let c5 := c4.wr 18 (0x80005d19#32) 0x80003e90#32
  let c6 := c5.wr 21 (0x80006000#32) 0x80003e94#32
  let c7 := c6.wr 21 (0x80005d0b#32) 0x80003e98#32
  let c8 := c7.wr 7 (32#32) 0x80003e9c#32
  let c9 := c8.wr 28 (127#32) 0x80003ea0#32
  let c10 := c9.wr 29 (ptr) 0x80003ea2#32
  let c11 := c10.wr 30 (BitVec.ofNat 32 len) 0x80003ea4#32
  let c12 := c11.wr 17 (0#32) 0x80003ea6#32
  let c13 := c12.goto 0x80003eb0#32
  have t0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine Quiet.step_of (by rw [hp];decide) (by rw [hp];exact rh2147499650) fun o => ?_
    change Observed.interp B img o (exec c _ _) ram 0 [] [] = ⟨.ok c1 ram [],[]⟩
    rw [exec_opimm,Core.get_zero,hp];first | rfl | (rw [hp];rfl)
  have t1 : Quiet.Step B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    refine Quiet.step_of (by change (0x80003e84#32).getLsbD 0=false;decide) rh2147499652 fun o => ?_
    change Observed.interp B img o (exec c1 _ _) ram 0 [] [] = ⟨.ok c2 ram [],[]⟩
    have v14 : c1.get 14=BitVec.ofNat 32 len := by simp [c1,Core.wr_get_ne,Core.wr_get,h13,h14]
    rw [exec_branch,v14,Core.get_zero,HttpPutMath.zero_guard len hpos (by omega)]
    simp only [Bool.false_eq_true,ite_false];first | rfl | (rw [hp];rfl)
  have t2 : Quiet.Step B img ⟨c2,ram⟩ ⟨c3,ram⟩ := by
    refine Quiet.step_of (by change (0x80003e86#32).getLsbD 0=false;decide) rh2147499654 fun o => ?_
    change Observed.interp B img o (exec c2 _ _) ram 0 [] [] = ⟨.ok c3 ram [],[]⟩
    rw [exec_opimm,Core.get_zero];first | rfl | (rw [hp];rfl)
  have t3 : Quiet.Step B img ⟨c3,ram⟩ ⟨c4,ram⟩ := by
    refine Quiet.step_of (by change (0x80003e88#32).getLsbD 0=false;decide) rh2147499656 fun o => ?_
    change Observed.interp B img o (exec c3 _ _) ram 0 [] [] = ⟨.ok c4 ram [],[]⟩
    rw [exec_lui];first | rfl | (rw [hp];rfl)
  have t4 : Quiet.Step B img ⟨c4,ram⟩ ⟨c5,ram⟩ := by
    refine Quiet.step_of (by change (0x80003e8c#32).getLsbD 0=false;decide) rh2147499660 fun o => ?_
    change Observed.interp B img o (exec c4 _ _) ram 0 [] [] = ⟨.ok c5 ram [],[]⟩
    have v18 : c4.get 18=0x80006000#32 := by simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h13,h14]
    rw [exec_opimm,v18];first | rfl | (rw [hp];rfl)
  have t5 : Quiet.Step B img ⟨c5,ram⟩ ⟨c6,ram⟩ := by
    refine Quiet.step_of (by change (0x80003e90#32).getLsbD 0=false;decide) rh2147499664 fun o => ?_
    change Observed.interp B img o (exec c5 _ _) ram 0 [] [] = ⟨.ok c6 ram [],[]⟩
    rw [exec_lui];first | rfl | (rw [hp];rfl)
  have t6 : Quiet.Step B img ⟨c6,ram⟩ ⟨c7,ram⟩ := by
    refine Quiet.step_of (by change (0x80003e94#32).getLsbD 0=false;decide) rh2147499668 fun o => ?_
    change Observed.interp B img o (exec c6 _ _) ram 0 [] [] = ⟨.ok c7 ram [],[]⟩
    have v21 : c6.get 21=0x80006000#32 := by simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h13,h14]
    rw [exec_opimm,v21];first | rfl | (rw [hp];rfl)
  have t7 : Quiet.Step B img ⟨c7,ram⟩ ⟨c8,ram⟩ := by
    refine Quiet.step_of (by change (0x80003e98#32).getLsbD 0=false;decide) rh2147499672 fun o => ?_
    change Observed.interp B img o (exec c7 _ _) ram 0 [] [] = ⟨.ok c8 ram [],[]⟩
    rw [exec_opimm,Core.get_zero];first | rfl | (rw [hp];rfl)
  have t8 : Quiet.Step B img ⟨c8,ram⟩ ⟨c9,ram⟩ := by
    refine Quiet.step_of (by change (0x80003e9c#32).getLsbD 0=false;decide) rh2147499676 fun o => ?_
    change Observed.interp B img o (exec c8 _ _) ram 0 [] [] = ⟨.ok c9 ram [],[]⟩
    rw [exec_opimm,Core.get_zero];first | rfl | (rw [hp];rfl)
  have t9 : Quiet.Step B img ⟨c9,ram⟩ ⟨c10,ram⟩ := by
    refine Quiet.step_of (by change (0x80003ea0#32).getLsbD 0=false;decide) rh2147499680 fun o => ?_
    change Observed.interp B img o (exec c9 _ _) ram 0 [] [] = ⟨.ok c10 ram [],[]⟩
    have v13 : c9.get 13=ptr := by simp [c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h13,h14]
    rw [exec_op,Core.get_zero,v13]
    change Observed.interp B img o (.done (c9.wr 29 (0#32+ptr) 0x80003ea2#32)) ram 0 [] [] = _
    rw [BitVec.zero_add];first | rfl | (rw [hp];rfl)
  have t10 : Quiet.Step B img ⟨c10,ram⟩ ⟨c11,ram⟩ := by
    refine Quiet.step_of (by change (0x80003ea2#32).getLsbD 0=false;decide) rh2147499682 fun o => ?_
    change Observed.interp B img o (exec c10 _ _) ram 0 [] [] = ⟨.ok c11 ram [],[]⟩
    have v14 : c10.get 14=BitVec.ofNat 32 len := by simp [c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h13,h14]
    rw [exec_op,Core.get_zero,v14]
    change Observed.interp B img o (.done (c10.wr 30 (0#32+BitVec.ofNat 32 len) 0x80003ea4#32)) ram 0 [] [] = _
    rw [BitVec.zero_add];first | rfl | (rw [hp];rfl)
  have t11 : Quiet.Step B img ⟨c11,ram⟩ ⟨c12,ram⟩ := by
    refine Quiet.step_of (by change (0x80003ea4#32).getLsbD 0=false;decide) rh2147499684 fun o => ?_
    change Observed.interp B img o (exec c11 _ _) ram 0 [] [] = ⟨.ok c12 ram [],[]⟩
    rw [exec_opimm,Core.get_zero];first | rfl | (rw [hp];rfl)
  have t12 : Quiet.Step B img ⟨c12,ram⟩ ⟨c13,ram⟩ := by
    refine Quiet.step_of (by change (0x80003ea6#32).getLsbD 0=false;decide) rh2147499686 fun o => ?_
    change Observed.interp B img o (exec c12 _ _) ram 0 [] [] = ⟨.ok c13 ram [],[]⟩
    rw [exec_jal]
    change Observed.interp B img o (jump c12 (0x80003ea6#32+10#32)) ram 0 [] [] = _
    rw [show 0x80003ea6#32+10#32=0x80003eb0#32 by decide +kernel,jump_ok _ _ (by decide)];first | rfl | (rw [hp];rfl)
  refine ⟨c13,.step t0 (.step t1 (.step t2 (.step t3 (.step t4 (.step t5 (.step t6 (.step t7 (.step t8 (.step t9 (.step t10 (.step t11 (.single t12)))))))))))),rfl,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,by rfl⟩
  · simp [c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h13,h14]
  · simp [c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h13,h14]
  · simp [c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h13,h14]
  · simp [c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h13,h14]
  · simp [c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h13,h14]
  · simp [c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h13,h14]
  · simp [c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h13,h14]
  · simp [c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h13,h14]
  · simp [c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h13,h14]
  · intro reg h9 h6 h18 h21 h7 h28 h29 h30 h17;simp [c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h13,h14,h9,h6,h18,h21,h7,h28,h29,h30,h17]
end E5R.Thermostat.ResponseHeadFieldEnter
