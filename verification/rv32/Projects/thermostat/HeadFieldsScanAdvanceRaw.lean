import Projects.thermostat.HttpParseCode
import Projects.thermostat.QuietRam
import Projects.thermostat.Memory
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.HeadFieldsScanAdvanceRaw
open E5R E5R.Thermostat

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (sp count start cursor inverse index cap : Word) (h21 : c.get 21=count) (h24 : c.get 24=start) (h14 : c.get 14=cursor)
(h25 : c.get 25=inverse) (h11 : c.get 11=index) (h2 : c.get 2=sp)
(hcap : ramRead ram (sp+40#32) .w=cap) (hm : Memory.Block B sp 56) (ha : sp.toNat%4=0)
    (hp : c.pc=0x80002f86#32) :
    ∃ d, Quiet.Steps B img 6 ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc=0x80002f94#32 ∧
      d.get 21=count+1#32 ∧ d.get 30=start+(count+1#32) ∧ d.get 14=cursor+1#32 ∧ d.get 25=inverse+1#32 ∧ d.get 11=index+1#32 ∧ d.get 15=cap ∧ (∀ r : Reg, r≠21 → r≠30 → r≠14 → r≠25 → r≠11 → r≠15 → d.get r=c.get r) ∧ d.sameCsr c := by
  let c1 := c.wr 21 (count+1#32) 0x80002f88#32
  let c2 := c1.wr 30 (start+(count+1#32)) 0x80002f8c#32
  let c3 := c2.wr 14 (cursor+1#32) 0x80002f8e#32
  let c4 := c3.wr 25 (inverse+1#32) 0x80002f90#32
  let c5 := c4.wr 11 (index+1#32) 0x80002f92#32
  let c6 := c5.wr 15 (cap) 0x80002f94#32
  have t0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine Quiet.step_of (by rw [hp];decide) (by rw [hp];exact hh2147495814) fun o => ?_
    change Observed.interp B img o (exec c _ _) ram 0 [] [] = ⟨.ok c1 ram [],[]⟩
    rw [exec_opimm,h21];first | rfl | (rw [hp];rfl)
  have t1 : Quiet.Step B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    refine Quiet.step_of (by change (0x80002f88#32).getLsbD 0=false;decide) hh2147495816 fun o => ?_
    change Observed.interp B img o (exec c1 _ _) ram 0 [] [] = ⟨.ok c2 ram [],[]⟩
    have v24 : c1.get 24=start := by simp [c1,Core.wr_get_ne,Core.wr_get,h21,h24,h14,h25,h11,h2]
    have v21 : c1.get 21=count+1#32 := by simp [c1,Core.wr_get_ne,Core.wr_get,h21,h24,h14,h25,h11,h2]
    rw [exec_op,v24,v21];first | rfl | (rw [hp];rfl)
  have t2 : Quiet.Step B img ⟨c2,ram⟩ ⟨c3,ram⟩ := by
    refine Quiet.step_of (by change (0x80002f8c#32).getLsbD 0=false;decide) hh2147495820 fun o => ?_
    change Observed.interp B img o (exec c2 _ _) ram 0 [] [] = ⟨.ok c3 ram [],[]⟩
    have v14 : c2.get 14=cursor := by simp [c2,c1,Core.wr_get_ne,Core.wr_get,h21,h24,h14,h25,h11,h2]
    rw [exec_opimm,v14];first | rfl | (rw [hp];rfl)
  have t3 : Quiet.Step B img ⟨c3,ram⟩ ⟨c4,ram⟩ := by
    refine Quiet.step_of (by change (0x80002f8e#32).getLsbD 0=false;decide) hh2147495822 fun o => ?_
    change Observed.interp B img o (exec c3 _ _) ram 0 [] [] = ⟨.ok c4 ram [],[]⟩
    have v25 : c3.get 25=inverse := by simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,h21,h24,h14,h25,h11,h2]
    rw [exec_opimm,v25];first | rfl | (rw [hp];rfl)
  have t4 : Quiet.Step B img ⟨c4,ram⟩ ⟨c5,ram⟩ := by
    refine Quiet.step_of (by change (0x80002f90#32).getLsbD 0=false;decide) hh2147495824 fun o => ?_
    change Observed.interp B img o (exec c4 _ _) ram 0 [] [] = ⟨.ok c5 ram [],[]⟩
    have v11 : c4.get 11=index := by simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h21,h24,h14,h25,h11,h2]
    rw [exec_opimm,v11];first | rfl | (rw [hp];rfl)
  have t5 : Quiet.Step B img ⟨c5,ram⟩ ⟨c6,ram⟩ := by
    refine Quiet.step_of (by change (0x80002f92#32).getLsbD 0=false;decide) hh2147495826 fun o => ?_
    change Observed.interp B img o (exec c5 _ _) ram 0 [] [] = ⟨.ok c6 ram [],[]⟩
    have v2 : c5.get 2=sp := by simp [c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h21,h24,h14,h25,h11,h2]
    rw [exec_load,v2,Quiet.interp_load_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 10 ha)
      (Memory.block_access hm (off := 40) (by decide) (by decide)),hcap];first | rfl | (rw [hp];rfl)
  refine ⟨c6,.step t0 (.step t1 (.step t2 (.step t3 (.step t4 (.single t5))))),rfl,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,by rfl⟩
  · simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h21,h24,h14,h25,h11,h2]
  · simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h21,h24,h14,h25,h11,h2]
  · simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h21,h24,h14,h25,h11,h2]
  · simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h21,h24,h14,h25,h11,h2]
  · simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h21,h24,h14,h25,h11,h2]
  · simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h21,h24,h14,h25,h11,h2]
  · intro reg h21 h30 h14 h25 h11 h15;simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h21,h24,h14,h25,h11,h2,h21,h30,h14,h25,h11,h15]
end E5R.Thermostat.HeadFieldsScanAdvanceRaw
