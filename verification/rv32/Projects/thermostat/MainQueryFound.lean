import Projects.thermostat.MainQueryCode
import Projects.thermostat.QuietRam
import Projects.thermostat.Memory
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.MainQueryFound
open E5R E5R.Thermostat

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (start finish index : Word)
(h29 : c.get 29=start) (h30 : c.get 30=finish) (h14 : c.get 14=index)
    (hp : c.pc=0x80000d44#32) :
    ∃ d, Quiet.Steps B img 4 ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc=0x80000d50#32 ∧
      d.get 13=(~~~start)+(finish-index) ∧ d.get 15=finish-index ∧ d.get 28=index ∧ (∀ r : Reg, r≠13 → r≠15 → r≠28 → d.get r=c.get r) ∧ d.sameCsr c := by
  let c1 := c.wr 13 (~~~start) 0x80000d48#32
  let c2 := c1.wr 15 (finish-index) 0x80000d4c#32
  let c3 := c2.wr 13 ((~~~start)+(finish-index)) 0x80000d4e#32
  let c4 := c3.wr 28 (index) 0x80000d50#32
  have t0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine Quiet.step_of (by rw [hp];decide) (by rw [hp];exact re2147487044) fun o => ?_
    change Observed.interp B img o (exec c _ _) ram 0 [] [] = ⟨.ok c1 ram [],[]⟩
    have v29 : c.get 29=start := by simp [Core.wr_get_ne,Core.wr_get,h29,h30,h14]
    rw [exec_opimm,v29];change Observed.interp B img o (Eff.done (c.wr 13 (start ^^^ BitVec.allOnes 32) _)) ram 0 [] [] = _;rw [BitVec.xor_allOnes,hp];rfl
  have t1 : Quiet.Step B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    refine Quiet.step_of (by change (0x80000d48#32).getLsbD 0=false;decide) re2147487048 fun o => ?_
    change Observed.interp B img o (exec c1 _ _) ram 0 [] [] = ⟨.ok c2 ram [],[]⟩
    have v30 : c1.get 30=finish := by simp [c1,Core.wr_get_ne,Core.wr_get,h29,h30,h14]
    have v14 : c1.get 14=index := by simp [c1,Core.wr_get_ne,Core.wr_get,h29,h30,h14]
    rw [exec_op,v30,v14];first | rfl | (rw [hp];rfl)
  have t2 : Quiet.Step B img ⟨c2,ram⟩ ⟨c3,ram⟩ := by
    refine Quiet.step_of (by change (0x80000d4c#32).getLsbD 0=false;decide) re2147487052 fun o => ?_
    change Observed.interp B img o (exec c2 _ _) ram 0 [] [] = ⟨.ok c3 ram [],[]⟩
    have v13 : c2.get 13= ~~~start := by simp [c2,c1,Core.wr_get_ne,Core.wr_get,h29,h30,h14]
    have v15 : c2.get 15=finish-index := by simp [c2,c1,Core.wr_get_ne,Core.wr_get,h29,h30,h14]
    rw [exec_op,v13,v15];first | rfl | (rw [hp];rfl)
  have t3 : Quiet.Step B img ⟨c3,ram⟩ ⟨c4,ram⟩ := by
    refine Quiet.step_of (by change (0x80000d4e#32).getLsbD 0=false;decide) re2147487054 fun o => ?_
    change Observed.interp B img o (exec c3 _ _) ram 0 [] [] = ⟨.ok c4 ram [],[]⟩
    have v14 : c3.get 14=index := by simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,h29,h30,h14]
    rw [exec_op,Core.get_zero,v14];change Observed.interp B img o (Eff.done (c3.wr 28 (0#32+index) _)) ram 0 [] [] = _;rw [BitVec.zero_add];rfl
  refine ⟨c4,.step t0 (.step t1 (.step t2 (.single t3))),rfl,?_ ,?_ ,?_ ,?_ ,by rfl⟩
  · simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h29,h30,h14]
  · simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h29,h30,h14]
  · simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h29,h30,h14]
  · intro reg h13 h15 h28;simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h29,h30,h14,h13,h15,h28]
end E5R.Thermostat.MainQueryFound
