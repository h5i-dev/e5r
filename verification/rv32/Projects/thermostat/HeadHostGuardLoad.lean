import Projects.thermostat.HttpParseCode
import Projects.thermostat.QuietRam
import Projects.thermostat.Memory
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.HeadHostGuardLoad
open E5R E5R.Thermostat

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (sp start length : Word) (h2 : c.get 2=sp) (h24 : c.get 24=start) (hlength : ramRead ram (sp+48#32) .w=length) (stack : Memory.Block B sp 56) (ha : sp.toNat%4=0)
    (hp : c.pc=0x80003122#32) :
    ∃ d, Quiet.Steps B img 3 ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc=0x8000312a#32 ∧
      d.get 11=length-start ∧ d.get 12=1#32 ∧ (∀ r : Reg, r≠11 → r≠12 → d.get r=c.get r) ∧ d.sameCsr c := by
  let c1 := c.wr 11 (length) 0x80003124#32
  let c2 := c1.wr 11 (length-start) 0x80003128#32
  let c3 := c2.wr 12 (1#32) 0x8000312a#32
  have t0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine Quiet.step_of (by rw [hp];decide) (by rw [hp];exact hh2147496226) fun o => ?_
    change Observed.interp B img o (exec c _ _) ram 0 [] [] = ⟨.ok c1 ram [],[]⟩
    have v2 : c.get 2=sp := by simp [Core.wr_get_ne,Core.wr_get,h2,h24]
    rw [exec_load,v2,Quiet.interp_load_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 12 ha)
     (Memory.block_access stack (off := 48) (by decide) (by decide)),hlength];first | rfl | (rw [hp];rfl)
  have t1 : Quiet.Step B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    refine Quiet.step_of (by change (0x80003124#32).getLsbD 0=false;decide) hh2147496228 fun o => ?_
    change Observed.interp B img o (exec c1 _ _) ram 0 [] [] = ⟨.ok c2 ram [],[]⟩
    have v11 : c1.get 11=length := by simp [c1,Core.wr_get_ne,Core.wr_get,h2,h24]
    have v24 : c1.get 24=start := by simp [c1,Core.wr_get_ne,Core.wr_get,h2,h24]
    rw [exec_op,v11,v24];first | rfl | (rw [hp];rfl)
  have t2 : Quiet.Step B img ⟨c2,ram⟩ ⟨c3,ram⟩ := by
    refine Quiet.step_of (by change (0x80003128#32).getLsbD 0=false;decide) hh2147496232 fun o => ?_
    change Observed.interp B img o (exec c2 _ _) ram 0 [] [] = ⟨.ok c3 ram [],[]⟩
    rw [exec_opimm,Core.get_zero];first | rfl | (rw [hp];rfl)
  refine ⟨c3,.step t0 (.step t1 (.single t2)),rfl,?_ ,?_ ,?_ ,by rfl⟩
  · simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h24]
  · simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h24]
  · intro reg h11 h12;simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h24,h11,h12]
end E5R.Thermostat.HeadHostGuardLoad
