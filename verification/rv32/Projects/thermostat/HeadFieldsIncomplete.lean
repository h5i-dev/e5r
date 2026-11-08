import Projects.thermostat.HttpParseCode
import Projects.thermostat.QuietRam
import Projects.thermostat.HeadIncomplete
import Projects.thermostat.Memory
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.HeadFieldsIncomplete
open E5R E5R.Thermostat

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (sp dst : Word) (h2 : c.get 2=sp) (hword : ramRead ram (sp+52#32) .w=dst)
(stack : Memory.Block B sp 56) (ha : sp.toNat%4=0) (hm : Memory.Block B dst 12) (aligned : dst.toNat%4=0)
    (hp : c.pc=0x800033f2#32) :
    ∃ d, Quiet.Steps B img 5 ⟨c,ram⟩ ⟨d,HeadIncomplete.memory ram dst⟩ ∧ d.pc=0x80002d6a#32 ∧
      d.get 10=3#32 ∧ d.get 11=dst ∧ (∀ r : Reg, r≠10 → r≠11 → d.get r=c.get r) ∧ d.sameCsr c := by
  let c1 := c.wr 10 (3#32) 0x800033f4#32
  let c2 := c1.wr 11 (dst) 0x800033f6#32
  let r1 := ramWrite ram (dst+0#32) (3#32) .w
  let c3 := c2.goto 0x800033f8#32
  let r2 := ramWrite r1 (dst+4#32) (0#32) .w
  let c4 := c3.goto 0x800033fc#32
  let c5 := c4.goto 0x80002d6a#32
  have t0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine Quiet.step_of (by rw [hp];decide) (by rw [hp];exact hh2147496946) fun o => ?_
    change Observed.interp B img o (exec c _ _) ram 0 [] [] = ⟨.ok c1 ram [],[]⟩
    rw [exec_opimm,Core.get_zero];first | rfl | (rw [hp];rfl)
  have t1 : Quiet.Step B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    refine Quiet.step_of (by change (0x800033f4#32).getLsbD 0=false;decide) hh2147496948 fun o => ?_
    change Observed.interp B img o (exec c1 _ _) ram 0 [] [] = ⟨.ok c2 ram [],[]⟩
    have v2 : c1.get 2=sp := by simp [c1,Core.wr_get_ne,Core.wr_get,h2]
    rw [exec_load,v2,Quiet.interp_load_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 13 ha)
      (Memory.block_access stack (off := 52) (by decide) (by decide)),hword];first | rfl | (rw [hp];rfl)
  have t2 : Quiet.Step B img ⟨c2,ram⟩ ⟨c3,r1⟩ := by
    refine Quiet.step_of (by change (0x800033f6#32).getLsbD 0=false;decide) hh2147496950 fun o => ?_
    change Observed.interp B img o (exec c2 _ _) ram 0 [] [] = ⟨.ok c3 r1 [],[]⟩
    have v11 : c2.get 11=dst := by simp [c2,c1,Core.wr_get_ne,Core.wr_get,h2]
    have vv : c2.get 10=3#32 := by simp [c2,c1,Core.wr_get_ne,Core.wr_get,h2]
    rw [exec_store,v11,vv,Quiet.interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned dst 0 aligned)
      (Memory.block_access hm (off := 0) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t3 : Quiet.Step B img ⟨c3,r1⟩ ⟨c4,r2⟩ := by
    refine Quiet.step_of (by change (0x800033f8#32).getLsbD 0=false;decide) hh2147496952 fun o => ?_
    change Observed.interp B img o (exec c3 _ _) r1 0 [] [] = ⟨.ok c4 r2 [],[]⟩
    have v11 : c3.get 11=dst := by simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2]
    rw [exec_store,v11,Core.get_zero,Quiet.interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned dst 1 aligned)
      (Memory.block_access hm (off := 4) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t4 : Quiet.Step B img ⟨c4,r2⟩ ⟨c5,r2⟩ := by
    refine Quiet.step_of (by change (0x800033fc#32).getLsbD 0=false;decide) hh2147496956 fun o => ?_
    change Observed.interp B img o (exec c4 _ _) r2 0 [] [] = ⟨.ok c5 r2 [],[]⟩
    rw [exec_jal,Core.set_zero]
    change Observed.interp B img o (jump c4 (0x800033fc#32+0xfffff96e#32)) r2 0 [] [] = _
    rw [show 0x800033fc#32+0xfffff96e#32=0x80002d6a#32 by decide +kernel,jump_ok _ _ (by decide)];first | rfl | (rw [hp];rfl)
  refine ⟨c5,.step t0 (.step t1 (.step t2 (.step t3 (.single t4)))),rfl,?_ ,?_ ,?_ ,by rfl⟩
  · simp [c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2]
  · simp [c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2]
  · intro reg h10 h11;simp [c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h10,h11]
end E5R.Thermostat.HeadFieldsIncomplete
