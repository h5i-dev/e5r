import Projects.thermostat.HttpParseCode
import Projects.thermostat.QuietRam
import Projects.thermostat.Memory
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.HeadClLowRaw
open E5R E5R.Thermostat

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (byte high product : Word) (h30 : c.get 30=byte) (h13 : c.get 13=high) (h29 : c.get 29=product)
    (hp : c.pc=0x8000322a#32) :
    ∃ d, Quiet.Steps B img 6 ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc=0x8000323c#32 ∧
      d.get 14=alu .add (alu .and (alu .add byte 0xffffffd0#32) 255#32) product ∧ d.get 30=alu .sll high 1#32 ∧ d.get 13=alu .add (alu .sll high 3#32) (alu .sll high 1#32) ∧ (∀ r : Reg, r≠14 → r≠30 → r≠13 → d.get r=c.get r) ∧ d.sameCsr c := by
  let c1 := c.wr 14 (alu .add byte 0xffffffd0#32) 0x8000322e#32
  let c2 := c1.wr 30 (alu .sll high 1#32) 0x80003232#32
  let c3 := c2.wr 14 (alu .and (alu .add byte 0xffffffd0#32) 255#32) 0x80003236#32
  let c4 := c3.wr 13 (alu .sll high 3#32) 0x80003238#32
  let c5 := c4.wr 14 (alu .add (alu .and (alu .add byte 0xffffffd0#32) 255#32) product) 0x8000323a#32
  let c6 := c5.wr 13 (alu .add (alu .sll high 3#32) (alu .sll high 1#32)) 0x8000323c#32
  have t0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine Quiet.step_of (by rw [hp];decide) (by rw [hp];exact hh2147496490) fun o => ?_
    change Observed.interp B img o (exec c _ _) ram 0 [] [] = ⟨.ok c1 ram [],[]⟩
    rw [exec_opimm,h30];first | rfl | (rw [hp];rfl)
  have t1 : Quiet.Step B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    refine Quiet.step_of (by change (0x8000322e#32).getLsbD 0=false;decide) hh2147496494 fun o => ?_
    change Observed.interp B img o (exec c1 _ _) ram 0 [] [] = ⟨.ok c2 ram [],[]⟩
    have v13 : c1.get 13=high := by simp [c1,Core.wr_get_ne,Core.wr_get,h30,h13,h29]
    rw [exec_opimm,v13];first | rfl | (rw [hp];rfl)
  have t2 : Quiet.Step B img ⟨c2,ram⟩ ⟨c3,ram⟩ := by
    refine Quiet.step_of (by change (0x80003232#32).getLsbD 0=false;decide) hh2147496498 fun o => ?_
    change Observed.interp B img o (exec c2 _ _) ram 0 [] [] = ⟨.ok c3 ram [],[]⟩
    have v14 : c2.get 14=alu .add byte 0xffffffd0#32 := by simp [c2,c1,Core.wr_get_ne,Core.wr_get,h30,h13,h29]
    rw [exec_opimm,v14];first | rfl | (rw [hp];rfl)
  have t3 : Quiet.Step B img ⟨c3,ram⟩ ⟨c4,ram⟩ := by
    refine Quiet.step_of (by change (0x80003236#32).getLsbD 0=false;decide) hh2147496502 fun o => ?_
    change Observed.interp B img o (exec c3 _ _) ram 0 [] [] = ⟨.ok c4 ram [],[]⟩
    have v13 : c3.get 13=high := by simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,h30,h13,h29]
    rw [exec_opimm,v13];first | rfl | (rw [hp];rfl)
  have t4 : Quiet.Step B img ⟨c4,ram⟩ ⟨c5,ram⟩ := by
    refine Quiet.step_of (by change (0x80003238#32).getLsbD 0=false;decide) hh2147496504 fun o => ?_
    change Observed.interp B img o (exec c4 _ _) ram 0 [] [] = ⟨.ok c5 ram [],[]⟩
    have v14 : c4.get 14=alu .and (alu .add byte 0xffffffd0#32) 255#32 := by simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h30,h13,h29]
    have v29 : c4.get 29=product := by simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h30,h13,h29]
    rw [exec_op,v14,v29];first | rfl | (rw [hp];rfl)
  have t5 : Quiet.Step B img ⟨c5,ram⟩ ⟨c6,ram⟩ := by
    refine Quiet.step_of (by change (0x8000323a#32).getLsbD 0=false;decide) hh2147496506 fun o => ?_
    change Observed.interp B img o (exec c5 _ _) ram 0 [] [] = ⟨.ok c6 ram [],[]⟩
    have v13 : c5.get 13=alu .sll high 3#32 := by simp [c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h30,h13,h29]
    have v30 : c5.get 30=alu .sll high 1#32 := by simp [c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h30,h13,h29]
    rw [exec_op,v13,v30];first | rfl | (rw [hp];rfl)
  refine ⟨c6,.step t0 (.step t1 (.step t2 (.step t3 (.step t4 (.single t5))))),rfl,?_ ,?_ ,?_ ,?_ ,by rfl⟩
  · simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h30,h13,h29]
  · simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h30,h13,h29]
  · simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h30,h13,h29]
  · intro reg h14 h30 h13;simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h30,h13,h29,h14,h30,h13]
end E5R.Thermostat.HeadClLowRaw
