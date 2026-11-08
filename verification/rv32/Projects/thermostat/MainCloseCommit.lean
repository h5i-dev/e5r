import Projects.thermostat.MainCloseCode
import Projects.thermostat.QuietRam
import Projects.thermostat.Memory
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.MainCloseCommit
open E5R E5R.Thermostat

def memory (ram : Word → BitVec 8) (sp close : Word) :=
  ramWrite (ram) (sp+3304#32) (close) .b

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (sp close : Word) (h8 : c.get 8=sp+3204#32) (h10 : c.get 10=close) (stack : Memory.Block B sp 5232) (aligned : sp.toNat%4=0)
(hcapacity : ramRead ram (sp+3272#32) .w=1024#32)
    (hp : c.pc=0x8000128c#32) :
    ∃ d, Quiet.Steps B img 4 ⟨c,ram⟩ ⟨d,memory ram sp close⟩ ∧ d.pc=0x8000129a#32 ∧
      d.get 12=1024#32 ∧ d.get 10=191#32 ∧ (∀ r : Reg, r≠12 → r≠10 → d.get r=c.get r) ∧ d.sameCsr c := by
  let c1 := c.wr 12 (1024#32) 0x8000128e#32
  let r1 := ramWrite ram (sp+3304#32) (close) .b
  let c2 := c1.goto 0x80001292#32
  let c3 := c2.wr 10 (191#32) 0x80001296#32
  let c4 := c3.goto 0x8000129a#32
  have t0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine Quiet.step_of (by rw [hp];decide) (by rw [hp];exact re2147488396) fun o => ?_
    change Observed.interp B img o (exec c _ _) ram 0 [] [] = ⟨.ok c1 ram [],[]⟩
    have v8 : c.get 8=sp+3204#32 := by simp [Core.wr_get_ne,Core.wr_get,h8,h10]
    rw [exec_load,v8,BitVec.add_assoc,show 3204#32+68#32=3272#32 by decide +kernel,Quiet.interp_load_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 818 aligned) (Memory.block_access stack (off := 3272) (by decide) (by decide)),hcapacity];first | rfl | (rw [hp];rfl)
  have t1 : Quiet.Step B img ⟨c1,ram⟩ ⟨c2,r1⟩ := by
    refine Quiet.step_of (by change (0x8000128e#32).getLsbD 0=false;decide) re2147488398 fun o => ?_
    change Observed.interp B img o (exec c1 _ _) ram 0 [] [] = ⟨.ok c2 r1 [],[]⟩
    have v8 : c1.get 8=sp+3204#32 := by simp [c1,Core.wr_get_ne,Core.wr_get,h8,h10]
    have v10 : c1.get 10=close := by simp [c1,Core.wr_get_ne,Core.wr_get,h8,h10]
    rw [exec_store,v8,v10,BitVec.add_assoc,show 3204#32+100#32=3304#32 by decide +kernel,Quiet.interp_store_ram (B := B) (img := img) (w := .b) o (Nat.mod_one _) (Memory.block_access stack (off := 3304) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t2 : Quiet.Step B img ⟨c2,r1⟩ ⟨c3,r1⟩ := by
    refine Quiet.step_of (by change (0x80001292#32).getLsbD 0=false;decide) re2147488402 fun o => ?_
    change Observed.interp B img o (exec c2 _ _) r1 0 [] [] = ⟨.ok c3 r1 [],[]⟩
    rw [exec_opimm,Core.get_zero];first | rfl | (rw [hp];rfl)
  have t3 : Quiet.Step B img ⟨c3,r1⟩ ⟨c4,r1⟩ := by
    refine Quiet.step_of (by change (0x80001296#32).getLsbD 0=false;decide) re2147488406 fun o => ?_
    change Observed.interp B img o (exec c3 _ _) r1 0 [] [] = ⟨.ok c4 r1 [],[]⟩
    have v10 : c3.get 10=191#32 := by simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h10]
    have v12 : c3.get 12=1024#32 := by simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h10]
    rw [exec_branch,v10,v12,show taken .geu 191#32 1024#32=false by decide +kernel];first | rfl | (rw [hp];rfl)
  refine ⟨c4,.step t0 (.step t1 (.step t2 (.single t3))),rfl,?_ ,?_ ,?_ ,by rfl⟩
  · simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h10]
  · simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h10]
  · intro reg h12 h10;simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h10,h12,h10]
end E5R.Thermostat.MainCloseCommit
