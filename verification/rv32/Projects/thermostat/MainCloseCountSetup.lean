import Projects.thermostat.MainCloseCode
import Projects.thermostat.QuietRam
import Projects.thermostat.Memory
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.MainCloseCountSetup
open E5R E5R.Thermostat

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (sp : Word) (h2 : c.get 2=sp) (h8 : c.get 8=sp+3204#32) (stack : Memory.Block B sp 5232) (aligned : sp.toNat%4=0)
(hconfig : ramRead ram (sp+3248#32) .w=sp+3204#32) (hrequests : ramRead ram (sp+3212#32) .w=100#32)
    (hp : c.pc=0x8000124a#32) :
    ∃ d, Quiet.Steps B img 8 ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc=0x80001262#32 ∧
      d.get 11=100#32 ∧ d.get 20=5#32 ∧ d.get 21=6#32 ∧ d.get 24=sp+3740#32 ∧ d.get 25=sp+3784#32 ∧ (∀ r : Reg, r≠11 → r≠20 → r≠21 → r≠24 → r≠25 → d.get r=c.get r) ∧ d.sameCsr c := by
  let c1 := c.wr 11 (sp+3204#32) 0x8000124c#32
  let c2 := c1.wr 11 (100#32) 0x8000124e#32
  let c3 := c2.wr 20 (5#32) 0x80001250#32
  let c4 := c3.wr 21 (6#32) 0x80001252#32
  let c5 := c4.wr 24 (sp+2047#32) 0x80001256#32
  let c6 := c5.wr 24 (sp+3740#32) 0x8000125a#32
  let c7 := c6.wr 25 (sp+2047#32) 0x8000125e#32
  let c8 := c7.wr 25 (sp+3784#32) 0x80001262#32
  have t0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine Quiet.step_of (by rw [hp];decide) (by rw [hp];exact re2147488330) fun o => ?_
    change Observed.interp B img o (exec c _ _) ram 0 [] [] = ⟨.ok c1 ram [],[]⟩
    have v8 : c.get 8=sp+3204#32 := by simp [Core.wr_get_ne,Core.wr_get,h2,h8]
    rw [exec_load,v8,BitVec.add_assoc,show 3204#32+44#32=3248#32 by decide +kernel,Quiet.interp_load_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 812 aligned) (Memory.block_access stack (off := 3248) (by decide) (by decide)),hconfig];first | rfl | (rw [hp];rfl)
  have t1 : Quiet.Step B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    refine Quiet.step_of (by change (0x8000124c#32).getLsbD 0=false;decide) re2147488332 fun o => ?_
    change Observed.interp B img o (exec c1 _ _) ram 0 [] [] = ⟨.ok c2 ram [],[]⟩
    have v11 : c1.get 11=sp+3204#32 := by simp [c1,Core.wr_get_ne,Core.wr_get,h2,h8]
    rw [exec_load,v11,BitVec.add_assoc,show 3204#32+8#32=3212#32 by decide +kernel,Quiet.interp_load_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 803 aligned) (Memory.block_access stack (off := 3212) (by decide) (by decide)),hrequests];first | rfl | (rw [hp];rfl)
  have t2 : Quiet.Step B img ⟨c2,ram⟩ ⟨c3,ram⟩ := by
    refine Quiet.step_of (by change (0x8000124e#32).getLsbD 0=false;decide) re2147488334 fun o => ?_
    change Observed.interp B img o (exec c2 _ _) ram 0 [] [] = ⟨.ok c3 ram [],[]⟩
    rw [exec_opimm,Core.get_zero];first | rfl | (rw [hp];rfl)
  have t3 : Quiet.Step B img ⟨c3,ram⟩ ⟨c4,ram⟩ := by
    refine Quiet.step_of (by change (0x80001250#32).getLsbD 0=false;decide) re2147488336 fun o => ?_
    change Observed.interp B img o (exec c3 _ _) ram 0 [] [] = ⟨.ok c4 ram [],[]⟩
    rw [exec_opimm,Core.get_zero];first | rfl | (rw [hp];rfl)
  have t4 : Quiet.Step B img ⟨c4,ram⟩ ⟨c5,ram⟩ := by
    refine Quiet.step_of (by change (0x80001252#32).getLsbD 0=false;decide) re2147488338 fun o => ?_
    change Observed.interp B img o (exec c4 _ _) ram 0 [] [] = ⟨.ok c5 ram [],[]⟩
    have v2 : c4.get 2=sp := by simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8]
    rw [exec_opimm,v2];first | rfl | (rw [hp];rfl)
  have t5 : Quiet.Step B img ⟨c5,ram⟩ ⟨c6,ram⟩ := by
    refine Quiet.step_of (by change (0x80001256#32).getLsbD 0=false;decide) re2147488342 fun o => ?_
    change Observed.interp B img o (exec c5 _ _) ram 0 [] [] = ⟨.ok c6 ram [],[]⟩
    have v24 : c5.get 24=sp+2047#32 := by simp [c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8]
    rw [exec_opimm,v24]
    change Observed.interp B img o (Eff.done (c5.wr 24 ((sp+2047#32)+1693#32) 0x8000125a#32)) ram 0 [] []=_
    rw [BitVec.add_assoc,show 2047#32+1693#32=3740#32 by decide +kernel];first | rfl | (rw [hp];rfl)
  have t6 : Quiet.Step B img ⟨c6,ram⟩ ⟨c7,ram⟩ := by
    refine Quiet.step_of (by change (0x8000125a#32).getLsbD 0=false;decide) re2147488346 fun o => ?_
    change Observed.interp B img o (exec c6 _ _) ram 0 [] [] = ⟨.ok c7 ram [],[]⟩
    have v2 : c6.get 2=sp := by simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8]
    rw [exec_opimm,v2];first | rfl | (rw [hp];rfl)
  have t7 : Quiet.Step B img ⟨c7,ram⟩ ⟨c8,ram⟩ := by
    refine Quiet.step_of (by change (0x8000125e#32).getLsbD 0=false;decide) re2147488350 fun o => ?_
    change Observed.interp B img o (exec c7 _ _) ram 0 [] [] = ⟨.ok c8 ram [],[]⟩
    have v25 : c7.get 25=sp+2047#32 := by simp [c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8]
    rw [exec_opimm,v25]
    change Observed.interp B img o (Eff.done (c7.wr 25 ((sp+2047#32)+1737#32) 0x80001262#32)) ram 0 [] []=_
    rw [BitVec.add_assoc,show 2047#32+1737#32=3784#32 by decide +kernel];first | rfl | (rw [hp];rfl)
  refine ⟨c8,.step t0 (.step t1 (.step t2 (.step t3 (.step t4 (.step t5 (.step t6 (.single t7))))))),rfl,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,by rfl⟩
  · simp [c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8]
  · simp [c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8]
  · simp [c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8]
  · simp [c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8]
  · simp [c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8]
  · intro reg h11 h20 h21 h24 h25;simp [c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h11,h20,h21,h24,h25]
end E5R.Thermostat.MainCloseCountSetup
