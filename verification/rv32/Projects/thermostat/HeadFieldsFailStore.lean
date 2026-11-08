import Projects.thermostat.HttpParseCode
import Projects.thermostat.QuietRam
import Projects.thermostat.HeadResultStore
import Projects.thermostat.Memory
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.HeadFieldsFailStore
open E5R E5R.Thermostat

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (sp dst tag status : Word) (h2 : c.get 2=sp) (h10 : c.get 10=tag) (h11 : c.get 11=status) (hword : ramRead ram (sp+52#32) .w=dst)
(stack : Memory.Block B sp 56) (ha : sp.toNat%4=0) (hm : Memory.Block B dst 12) (aligned : dst.toNat%4=0)
    (hp : c.pc=0x8000341a#32) :
    ∃ d, Quiet.Steps B img 5 ⟨c,ram⟩ ⟨d,HeadResultStore.memory ram dst tag status⟩ ∧ d.pc=0x80002d6a#32 ∧
      d.get 12=dst ∧ (∀ r : Reg, r≠12 → d.get r=c.get r) ∧ d.sameCsr c := by
  let c1 := c.wr 12 (dst) 0x8000341c#32
  let r1 := ramWrite ram (dst+0#32) (tag) .w
  let c2 := c1.goto 0x8000341e#32
  let r2 := ramWrite r1 (dst+4#32) (0#32) .w
  let c3 := c2.goto 0x80003422#32
  let r3 := ramWrite r2 (dst+8#32) (status) .h
  let c4 := c3.goto 0x80003426#32
  let c5 := c4.goto 0x80002d6a#32
  have t0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine Quiet.step_of (by rw [hp];decide) (by rw [hp];exact hh2147496986) fun o => ?_
    change Observed.interp B img o (exec c _ _) ram 0 [] [] = ⟨.ok c1 ram [],[]⟩
    rw [exec_load,h2,Quiet.interp_load_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 13 ha)
      (Memory.block_access stack (off := 52) (by decide) (by decide)),hword];first | rfl | (rw [hp];rfl)
  have t1 : Quiet.Step B img ⟨c1,ram⟩ ⟨c2,r1⟩ := by
    refine Quiet.step_of (by change (0x8000341c#32).getLsbD 0=false;decide) hh2147496988 fun o => ?_
    change Observed.interp B img o (exec c1 _ _) ram 0 [] [] = ⟨.ok c2 r1 [],[]⟩
    have v12 : c1.get 12=dst := by simp [c1,Core.wr_get_ne,Core.wr_get,h2,h10,h11]
    have vv : c1.get 10=tag := by simp [c1,Core.wr_get_ne,Core.wr_get,h2,h10,h11]
    rw [exec_store,v12,vv,Quiet.interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned dst 0 aligned)
      (Memory.block_access hm (off := 0) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t2 : Quiet.Step B img ⟨c2,r1⟩ ⟨c3,r2⟩ := by
    refine Quiet.step_of (by change (0x8000341e#32).getLsbD 0=false;decide) hh2147496990 fun o => ?_
    change Observed.interp B img o (exec c2 _ _) r1 0 [] [] = ⟨.ok c3 r2 [],[]⟩
    have v12 : c2.get 12=dst := by simp [c2,c1,Core.wr_get_ne,Core.wr_get,h2,h10,h11]
    rw [exec_store,v12,Core.get_zero,Quiet.interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned dst 1 aligned)
      (Memory.block_access hm (off := 4) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t3 : Quiet.Step B img ⟨c3,r2⟩ ⟨c4,r3⟩ := by
    refine Quiet.step_of (by change (0x80003422#32).getLsbD 0=false;decide) hh2147496994 fun o => ?_
    change Observed.interp B img o (exec c3 _ _) r2 0 [] [] = ⟨.ok c4 r3 [],[]⟩
    have v12 : c3.get 12=dst := by simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h10,h11]
    have vv : c3.get 11=status := by simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h10,h11]
    rw [exec_store,v12,vv,Quiet.interp_store_ram (B := B) (img := img) (w := .h) o (Memory.half_aligned dst 4 (by omega))
      (Memory.block_access hm (off := 8) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t4 : Quiet.Step B img ⟨c4,r3⟩ ⟨c5,r3⟩ := by
    refine Quiet.step_of (by change (0x80003426#32).getLsbD 0=false;decide) hh2147496998 fun o => ?_
    change Observed.interp B img o (exec c4 _ _) r3 0 [] [] = ⟨.ok c5 r3 [],[]⟩
    rw [exec_jal,Core.set_zero]
    change Observed.interp B img o (jump c4 (0x80003426#32+0xfffff944#32)) r3 0 [] [] = _
    rw [show 0x80003426#32+0xfffff944#32=0x80002d6a#32 by decide +kernel,jump_ok _ _ (by decide)];first | rfl | (rw [hp];rfl)
  refine ⟨c5,.step t0 (.step t1 (.step t2 (.step t3 (.single t4)))),rfl,?_ ,?_ ,by rfl⟩
  · simp [c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h10,h11]
  · intro reg h12;simp [c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h10,h11,h12]
end E5R.Thermostat.HeadFieldsFailStore
