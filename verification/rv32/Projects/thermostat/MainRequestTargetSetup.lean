import Projects.thermostat.MainTargetEntryCode
import Projects.thermostat.QuietRam
import Projects.thermostat.Memory
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.MainRequestTargetSetup
open E5R E5R.Thermostat

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (sp rx start : Word) (h8 : c.get 8=sp+3204#32) (h29 : c.get 29=start) (hrx : ramRead ram (sp+3260#32) .w=rx)
(stack : Memory.Block B sp 5232) (aligned : sp.toNat%4=0)
    (hp : c.pc=0x80000b82#32) :
    ∃ d, Quiet.Steps B img 4 ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc=0x80000b8e#32 ∧
      d.get 5=6#32 ∧ d.get 17=5#32 ∧ d.get 21=rx ∧ d.get 10=rx+start ∧ (∀ r : Reg, r≠5 → r≠17 → r≠21 → r≠10 → d.get r=c.get r) ∧ d.sameCsr c := by
  let c1 := c.wr 5 (6#32) 0x80000b84#32
  let c2 := c1.wr 17 (5#32) 0x80000b86#32
  let c3 := c2.wr 21 (rx) 0x80000b8a#32
  let c4 := c3.wr 10 (rx+start) 0x80000b8e#32
  have t0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine Quiet.step_of (by rw [hp];decide) (by rw [hp];exact re2147486594) fun o => ?_
    change Observed.interp B img o (exec c _ _) ram 0 [] [] = ⟨.ok c1 ram [],[]⟩
    rw [exec_opimm,Core.get_zero];first | rfl | (rw [hp];rfl)
  have t1 : Quiet.Step B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    refine Quiet.step_of (by change (0x80000b84#32).getLsbD 0=false;decide) re2147486596 fun o => ?_
    change Observed.interp B img o (exec c1 _ _) ram 0 [] [] = ⟨.ok c2 ram [],[]⟩
    rw [exec_opimm,Core.get_zero];first | rfl | (rw [hp];rfl)
  have t2 : Quiet.Step B img ⟨c2,ram⟩ ⟨c3,ram⟩ := by
    refine Quiet.step_of (by change (0x80000b86#32).getLsbD 0=false;decide) re2147486598 fun o => ?_
    change Observed.interp B img o (exec c2 _ _) ram 0 [] [] = ⟨.ok c3 ram [],[]⟩
    have v8 : c2.get 8=sp+3204#32 := by simp [c2,c1,Core.wr_get_ne,Core.wr_get,h8,h29]
    rw [exec_load,v8,BitVec.add_assoc,show 3204#32+56#32=3260#32 by decide +kernel,Quiet.interp_load_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 815 aligned) (Memory.block_access stack (off := 3260) (by decide) (by decide)),hrx];first | rfl | (rw [hp];rfl)
  have t3 : Quiet.Step B img ⟨c3,ram⟩ ⟨c4,ram⟩ := by
    refine Quiet.step_of (by change (0x80000b8a#32).getLsbD 0=false;decide) re2147486602 fun o => ?_
    change Observed.interp B img o (exec c3 _ _) ram 0 [] [] = ⟨.ok c4 ram [],[]⟩
    have v21 : c3.get 21=rx := by simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h29]
    have v29 : c3.get 29=start := by simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h29]
    rw [exec_op,v21,v29];first | rfl | (rw [hp];rfl)
  refine ⟨c4,.step t0 (.step t1 (.step t2 (.single t3))),rfl,?_ ,?_ ,?_ ,?_ ,?_ ,by rfl⟩
  · simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h29]
  · simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h29]
  · simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h29]
  · simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h29]
  · intro reg h5 h17 h21 h10;simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h29,h5,h17,h21,h10]
end E5R.Thermostat.MainRequestTargetSetup
