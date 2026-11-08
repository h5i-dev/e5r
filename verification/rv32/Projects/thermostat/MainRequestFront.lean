import Projects.thermostat.MainRequestBuildCode
import Projects.thermostat.QuietRam
import Projects.thermostat.Memory
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.MainRequestFront
open E5R E5R.Thermostat

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (sp start finish rx : Word) (h8 : c.get 8=sp+3204#32) (stack : Memory.Block B sp 5232) (aligned : sp.toNat%4=0)
(h20 : c.get 20=start) (h25 : c.get 25=finish) (h21 : c.get 21=rx)
(hhalf0 : extend .h true (ramRead ram (sp+4512#32) .h)=0#32)
(hhalf1 : extend .h true (ramRead ram (sp+4514#32) .h)=0#32)
    (hp : c.pc=0x80001168#32) :
    ∃ d, Quiet.Steps B img 4 ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc=0x80001176#32 ∧
      d.get 15=finish-start ∧ d.get 20=start+rx ∧ d.get 16=0#32 ∧ d.get 17=0#32 ∧ (∀ r : Reg, r≠15 → r≠20 → r≠16 → r≠17 → d.get r=c.get r) ∧ d.sameCsr c := by
  let c1 := c.wr 15 (finish-start) 0x8000116c#32
  let c2 := c1.wr 20 (start+rx) 0x8000116e#32
  let c3 := c2.wr 16 (0#32) 0x80001172#32
  let c4 := c3.wr 17 (0#32) 0x80001176#32
  have t0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine Quiet.step_of (by rw [hp];decide) (by rw [hp];exact re2147488104) fun o => ?_
    change Observed.interp B img o (exec c _ _) ram 0 [] [] = ⟨.ok c1 ram [],[]⟩
    have v25 : c.get 25=finish := by simp [Core.wr_get_ne,Core.wr_get,h8,h20,h25,h21]
    have v20 : c.get 20=start := by simp [Core.wr_get_ne,Core.wr_get,h8,h20,h25,h21]
    rw [exec_op,v25,v20];first | rfl | (rw [hp];rfl)
  have t1 : Quiet.Step B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    refine Quiet.step_of (by change (0x8000116c#32).getLsbD 0=false;decide) re2147488108 fun o => ?_
    change Observed.interp B img o (exec c1 _ _) ram 0 [] [] = ⟨.ok c2 ram [],[]⟩
    have v20 : c1.get 20=start := by simp [c1,Core.wr_get_ne,Core.wr_get,h8,h20,h25,h21]
    have v21 : c1.get 21=rx := by simp [c1,Core.wr_get_ne,Core.wr_get,h8,h20,h25,h21]
    rw [exec_op,v20,v21];first | rfl | (rw [hp];rfl)
  have t2 : Quiet.Step B img ⟨c2,ram⟩ ⟨c3,ram⟩ := by
    refine Quiet.step_of (by change (0x8000116e#32).getLsbD 0=false;decide) re2147488110 fun o => ?_
    change Observed.interp B img o (exec c2 _ _) ram 0 [] [] = ⟨.ok c3 ram [],[]⟩
    have v8 : c2.get 8=sp+3204#32 := by simp [c2,c1,Core.wr_get_ne,Core.wr_get,h8,h20,h25,h21]
    rw [exec_load,v8,BitVec.add_assoc,show 3204#32+1308#32=4512#32 by decide +kernel,Quiet.interp_load_ram (B := B) (img := img) (w := .h) o (Memory.half_aligned sp 2256 (by omega)) (Memory.block_access stack (off := 4512) (by decide) (by decide)),hhalf0];first | rfl | (rw [hp];rfl)
  have t3 : Quiet.Step B img ⟨c3,ram⟩ ⟨c4,ram⟩ := by
    refine Quiet.step_of (by change (0x80001172#32).getLsbD 0=false;decide) re2147488114 fun o => ?_
    change Observed.interp B img o (exec c3 _ _) ram 0 [] [] = ⟨.ok c4 ram [],[]⟩
    have v8 : c3.get 8=sp+3204#32 := by simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h20,h25,h21]
    rw [exec_load,v8,BitVec.add_assoc,show 3204#32+1310#32=4514#32 by decide +kernel,Quiet.interp_load_ram (B := B) (img := img) (w := .h) o (Memory.half_aligned sp 2257 (by omega)) (Memory.block_access stack (off := 4514) (by decide) (by decide)),hhalf1];first | rfl | (rw [hp];rfl)
  refine ⟨c4,.step t0 (.step t1 (.step t2 (.single t3))),rfl,?_ ,?_ ,?_ ,?_ ,?_ ,by rfl⟩
  · simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h20,h25,h21]
  · simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h20,h25,h21]
  · simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h20,h25,h21]
  · simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h20,h25,h21]
  · intro reg h15 h20 h16 h17;simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h20,h25,h21,h15,h20,h16,h17]
end E5R.Thermostat.MainRequestFront
