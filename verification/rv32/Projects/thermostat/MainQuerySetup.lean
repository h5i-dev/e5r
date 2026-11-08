import Projects.thermostat.MainQueryCode
import Projects.thermostat.QuietRam
import Projects.thermostat.Memory
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.MainQuerySetup
open E5R E5R.Thermostat

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (sp rx start finish ms me : Word)
(h2 : c.get 2=sp) (h21 : c.get 21=rx) (h29 : c.get 29=start) (h30 : c.get 30=finish)
(hms : ramRead ram (sp+28#32) .w=ms) (hme : ramRead ram (sp+24#32) .w=me)
(stack : Memory.Block B sp 5232) (aligned : sp.toNat%4=0)
    (hp : c.pc=0x80000bd0#32) :
    ∃ d, Quiet.Steps B img 6 ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc=0x80000be0#32 ∧
      d.get 14=0#32 ∧ d.get 12=rx+start+1#32 ∧ d.get 28=finish-start ∧ d.get 7=ms ∧ d.get 11=me ∧ (∀ r : Reg, r≠14 → r≠12 → r≠28 → r≠7 → r≠11 → d.get r=c.get r) ∧ d.sameCsr c := by
  let c1 := c.wr 14 (0#32) 0x80000bd2#32
  let c2 := c1.wr 12 (rx+start) 0x80000bd6#32
  let c3 := c2.wr 28 (finish-start) 0x80000bda#32
  let c4 := c3.wr 12 (rx+start+1#32) 0x80000bdc#32
  let c5 := c4.wr 7 (ms) 0x80000bde#32
  let c6 := c5.wr 11 (me) 0x80000be0#32
  have t0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine Quiet.step_of (by rw [hp];decide) (by rw [hp];exact re2147486672) fun o => ?_
    change Observed.interp B img o (exec c _ _) ram 0 [] [] = ⟨.ok c1 ram [],[]⟩
    rw [exec_opimm,Core.get_zero];first | rfl | (rw [hp];rfl)
  have t1 : Quiet.Step B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    refine Quiet.step_of (by change (0x80000bd2#32).getLsbD 0=false;decide) re2147486674 fun o => ?_
    change Observed.interp B img o (exec c1 _ _) ram 0 [] [] = ⟨.ok c2 ram [],[]⟩
    have v21 : c1.get 21=rx := by simp [c1,Core.wr_get_ne,Core.wr_get,h2,h21,h29,h30]
    have v29 : c1.get 29=start := by simp [c1,Core.wr_get_ne,Core.wr_get,h2,h21,h29,h30]
    rw [exec_op,v21,v29];first | rfl | (rw [hp];rfl)
  have t2 : Quiet.Step B img ⟨c2,ram⟩ ⟨c3,ram⟩ := by
    refine Quiet.step_of (by change (0x80000bd6#32).getLsbD 0=false;decide) re2147486678 fun o => ?_
    change Observed.interp B img o (exec c2 _ _) ram 0 [] [] = ⟨.ok c3 ram [],[]⟩
    have v30 : c2.get 30=finish := by simp [c2,c1,Core.wr_get_ne,Core.wr_get,h2,h21,h29,h30]
    have v29 : c2.get 29=start := by simp [c2,c1,Core.wr_get_ne,Core.wr_get,h2,h21,h29,h30]
    rw [exec_op,v30,v29];first | rfl | (rw [hp];rfl)
  have t3 : Quiet.Step B img ⟨c3,ram⟩ ⟨c4,ram⟩ := by
    refine Quiet.step_of (by change (0x80000bda#32).getLsbD 0=false;decide) re2147486682 fun o => ?_
    change Observed.interp B img o (exec c3 _ _) ram 0 [] [] = ⟨.ok c4 ram [],[]⟩
    have v12 : c3.get 12=rx+start := by simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h21,h29,h30]
    rw [exec_opimm,v12];first | rfl | (rw [hp];rfl)
  have t4 : Quiet.Step B img ⟨c4,ram⟩ ⟨c5,ram⟩ := by
    refine Quiet.step_of (by change (0x80000bdc#32).getLsbD 0=false;decide) re2147486684 fun o => ?_
    change Observed.interp B img o (exec c4 _ _) ram 0 [] [] = ⟨.ok c5 ram [],[]⟩
    have v2 : c4.get 2=sp := by simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h21,h29,h30]
    rw [exec_load,v2,Quiet.interp_load_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 7 aligned) (Memory.block_access stack (off := 28) (by decide) (by decide)),hms];rfl
  have t5 : Quiet.Step B img ⟨c5,ram⟩ ⟨c6,ram⟩ := by
    refine Quiet.step_of (by change (0x80000bde#32).getLsbD 0=false;decide) re2147486686 fun o => ?_
    change Observed.interp B img o (exec c5 _ _) ram 0 [] [] = ⟨.ok c6 ram [],[]⟩
    have v2 : c5.get 2=sp := by simp [c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h21,h29,h30]
    rw [exec_load,v2,Quiet.interp_load_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 6 aligned) (Memory.block_access stack (off := 24) (by decide) (by decide)),hme];rfl
  refine ⟨c6,.step t0 (.step t1 (.step t2 (.step t3 (.step t4 (.single t5))))),rfl,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,by rfl⟩
  · simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h21,h29,h30]
  · simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h21,h29,h30]
  · simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h21,h29,h30]
  · simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h21,h29,h30]
  · simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h21,h29,h30]
  · intro reg h14 h12 h28 h7 h11;simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h21,h29,h30,h14,h12,h28,h7,h11]
end E5R.Thermostat.MainQuerySetup
