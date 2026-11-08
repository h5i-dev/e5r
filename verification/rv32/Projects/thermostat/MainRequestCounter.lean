import Projects.thermostat.MainTargetEntryCode
import Projects.thermostat.QuietRam
import Projects.thermostat.Memory
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.MainRequestCounter
open E5R E5R.Thermostat

def memory (ram : Word → BitVec 8) (sp count used : Word) :=
  ramWrite (ramWrite (ram) (sp+3292#32) (count+1#32) .w) (sp+3296#32) (used) .w

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (sp count used : Word) (h8 : c.get 8=sp+3204#32) (h18 : c.get 18=0#32) (h24 : c.get 24=used)
(hcount : ramRead ram (sp+3292#32) .w=count) (hcapacity : ramRead ram (sp+3264#32) .w=2048#32)
(stack : Memory.Block B sp 5232) (aligned : sp.toNat%4=0)
    (hp : c.pc=0x80000b50#32) :
    ∃ d, Quiet.Steps B img 7 ⟨c,ram⟩ ⟨d,memory ram sp count used⟩ ∧ d.pc=0x80000b66#32 ∧
      d.get 31=0#32 ∧ d.get 18=count+1#32 ∧ d.get 12=2048#32 ∧ d.get 15=63#32 ∧ (∀ r : Reg, r≠31 → r≠18 → r≠12 → r≠15 → d.get r=c.get r) ∧ d.sameCsr c := by
  let c1 := c.wr 31 (0#32) 0x80000b52#32
  let c2 := c1.wr 18 (count) 0x80000b56#32
  let c3 := c2.wr 12 (2048#32) 0x80000b58#32
  let c4 := c3.wr 18 (count+1#32) 0x80000b5a#32
  let r1 := ramWrite ram (sp+3292#32) (count+1#32) .w
  let c5 := c4.goto 0x80000b5e#32
  let r2 := ramWrite r1 (sp+3296#32) (used) .w
  let c6 := c5.goto 0x80000b62#32
  let c7 := c6.wr 15 (63#32) 0x80000b66#32
  have t0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine Quiet.step_of (by rw [hp];decide) (by rw [hp];exact re2147486544) fun o => ?_
    change Observed.interp B img o (exec c _ _) ram 0 [] [] = ⟨.ok c1 ram [],[]⟩
    rw [exec_op,Core.get_zero,h18];first | rfl | (rw [hp];rfl)
  have t1 : Quiet.Step B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    refine Quiet.step_of (by change (0x80000b52#32).getLsbD 0=false;decide) re2147486546 fun o => ?_
    change Observed.interp B img o (exec c1 _ _) ram 0 [] [] = ⟨.ok c2 ram [],[]⟩
    have v8 : c1.get 8=sp+3204#32 := by simp [c1,Core.wr_get_ne,Core.wr_get,h8,h18,h24]
    rw [exec_load,v8,BitVec.add_assoc,show 3204#32+88#32=3292#32 by decide +kernel,Quiet.interp_load_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 823 aligned) (Memory.block_access stack (off := 3292) (by decide) (by decide)),hcount];first | rfl | (rw [hp];rfl)
  have t2 : Quiet.Step B img ⟨c2,ram⟩ ⟨c3,ram⟩ := by
    refine Quiet.step_of (by change (0x80000b56#32).getLsbD 0=false;decide) re2147486550 fun o => ?_
    change Observed.interp B img o (exec c2 _ _) ram 0 [] [] = ⟨.ok c3 ram [],[]⟩
    have v8 : c2.get 8=sp+3204#32 := by simp [c2,c1,Core.wr_get_ne,Core.wr_get,h8,h18,h24]
    rw [exec_load,v8,BitVec.add_assoc,show 3204#32+60#32=3264#32 by decide +kernel,Quiet.interp_load_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 816 aligned) (Memory.block_access stack (off := 3264) (by decide) (by decide)),hcapacity];first | rfl | (rw [hp];rfl)
  have t3 : Quiet.Step B img ⟨c3,ram⟩ ⟨c4,ram⟩ := by
    refine Quiet.step_of (by change (0x80000b58#32).getLsbD 0=false;decide) re2147486552 fun o => ?_
    change Observed.interp B img o (exec c3 _ _) ram 0 [] [] = ⟨.ok c4 ram [],[]⟩
    have v18 : c3.get 18=count := by simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h18,h24]
    rw [exec_opimm,v18];first | rfl | (rw [hp];rfl)
  have t4 : Quiet.Step B img ⟨c4,ram⟩ ⟨c5,r1⟩ := by
    refine Quiet.step_of (by change (0x80000b5a#32).getLsbD 0=false;decide) re2147486554 fun o => ?_
    change Observed.interp B img o (exec c4 _ _) ram 0 [] [] = ⟨.ok c5 r1 [],[]⟩
    have v8 : c4.get 8=sp+3204#32 := by simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h18,h24]
    have v18 : c4.get 18=count+1#32 := by simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h18,h24]
    rw [exec_store,v8,v18,BitVec.add_assoc,show 3204#32+88#32=3292#32 by decide +kernel,Quiet.interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 823 aligned) (Memory.block_access stack (off := 3292) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t5 : Quiet.Step B img ⟨c5,r1⟩ ⟨c6,r2⟩ := by
    refine Quiet.step_of (by change (0x80000b5e#32).getLsbD 0=false;decide) re2147486558 fun o => ?_
    change Observed.interp B img o (exec c5 _ _) r1 0 [] [] = ⟨.ok c6 r2 [],[]⟩
    have v8 : c5.get 8=sp+3204#32 := by simp [c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h18,h24]
    have v24 : c5.get 24=used := by simp [c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h18,h24]
    rw [exec_store,v8,v24,BitVec.add_assoc,show 3204#32+92#32=3296#32 by decide +kernel,Quiet.interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 824 aligned) (Memory.block_access stack (off := 3296) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t6 : Quiet.Step B img ⟨c6,r2⟩ ⟨c7,r2⟩ := by
    refine Quiet.step_of (by change (0x80000b62#32).getLsbD 0=false;decide) re2147486562 fun o => ?_
    change Observed.interp B img o (exec c6 _ _) r2 0 [] [] = ⟨.ok c7 r2 [],[]⟩
    rw [exec_opimm,Core.get_zero];first | rfl | (rw [hp];rfl)
  refine ⟨c7,.step t0 (.step t1 (.step t2 (.step t3 (.step t4 (.step t5 (.single t6)))))),rfl,?_ ,?_ ,?_ ,?_ ,?_ ,by rfl⟩
  · simp [c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h18,h24]
  · simp [c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h18,h24]
  · simp [c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h18,h24]
  · simp [c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h18,h24]
  · intro reg h31 h18 h12 h15;simp [c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h18,h24,h31,h18,h12,h15]
end E5R.Thermostat.MainRequestCounter
