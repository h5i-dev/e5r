import Projects.thermostat.HttpParseCode
import Projects.thermostat.QuietRam
import Projects.thermostat.Memory
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.HeadFieldsCRCalc
open E5R E5R.Thermostat

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (sp start count cap : Word) (h24 : c.get 24=start) (h21 : c.get 21=count) (h2 : c.get 2=sp)
(hcap : ramRead ram (sp+40#32) .w=cap) (hm : Memory.Block B sp 56) (ha : sp.toNat%4=0)
    (hp : c.pc=0x80002f9a#32) :
    ∃ d, Quiet.Steps B img 3 ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc=0x80002fa4#32 ∧
      d.get 26=start+count ∧ d.get 13=start+count+1#32 ∧ d.get 10=cap ∧ (∀ r : Reg, r≠26 → r≠13 → r≠10 → d.get r=c.get r) ∧ d.sameCsr c := by
  let c1 := c.wr 26 (start+count) 0x80002f9e#32
  let c2 := c1.wr 13 (start+count+1#32) 0x80002fa2#32
  let c3 := c2.wr 10 (cap) 0x80002fa4#32
  have t0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine Quiet.step_of (by rw [hp];decide) (by rw [hp];exact hh2147495834) fun o => ?_
    change Observed.interp B img o (exec c _ _) ram 0 [] [] = ⟨.ok c1 ram [],[]⟩
    rw [exec_op,h24,h21];first | rfl | (rw [hp];rfl)
  have t1 : Quiet.Step B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    refine Quiet.step_of (by change (0x80002f9e#32).getLsbD 0=false;decide) hh2147495838 fun o => ?_
    change Observed.interp B img o (exec c1 _ _) ram 0 [] [] = ⟨.ok c2 ram [],[]⟩
    have v26 : c1.get 26=start+count := by simp [c1,Core.wr_get_ne,Core.wr_get,h24,h21,h2]
    rw [exec_opimm,v26];first | rfl | (rw [hp];rfl)
  have t2 : Quiet.Step B img ⟨c2,ram⟩ ⟨c3,ram⟩ := by
    refine Quiet.step_of (by change (0x80002fa2#32).getLsbD 0=false;decide) hh2147495842 fun o => ?_
    change Observed.interp B img o (exec c2 _ _) ram 0 [] [] = ⟨.ok c3 ram [],[]⟩
    have v2 : c2.get 2=sp := by simp [c2,c1,Core.wr_get_ne,Core.wr_get,h24,h21,h2]
    rw [exec_load,v2,Quiet.interp_load_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 10 ha)
      (Memory.block_access hm (off := 40) (by decide) (by decide)),hcap];first | rfl | (rw [hp];rfl)
  refine ⟨c3,.step t0 (.step t1 (.single t2)),rfl,?_ ,?_ ,?_ ,?_ ,by rfl⟩
  · simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,h24,h21,h2]
  · simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,h24,h21,h2]
  · simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,h24,h21,h2]
  · intro reg h26 h13 h10;simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,h24,h21,h2,h26,h13,h10]
end E5R.Thermostat.HeadFieldsCRCalc
