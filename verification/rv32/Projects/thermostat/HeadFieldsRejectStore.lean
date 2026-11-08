import Projects.thermostat.HttpParseCode
import Projects.thermostat.QuietRam
import Projects.thermostat.HeadResultStore
import Projects.thermostat.Memory
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.HeadFieldsRejectStore
open E5R E5R.Thermostat

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (sp dst status : Word) (h2 : c.get 2=sp) (h1 : c.get 1=status) (hword : ramRead ram (sp+52#32) .w=dst)
(stack : Memory.Block B sp 56) (ha : sp.toNat%4=0) (hm : Memory.Block B dst 12) (aligned : dst.toNat%4=0)
    (hp : c.pc=0x8000342c#32) :
    ∃ d, Quiet.Steps B img 6 ⟨c,ram⟩ ⟨d,HeadResultStore.memory ram dst 4#32 status⟩ ∧ d.pc=0x80002d6a#32 ∧
      d.get 10=4#32 ∧ d.get 11=dst ∧ (∀ r : Reg, r≠10 → r≠11 → d.get r=c.get r) ∧ d.sameCsr c := by
  let c1 := c.wr 10 (4#32) 0x8000342e#32
  let c2 := c1.wr 11 (dst) 0x80003430#32
  let r1 := ramWrite ram (dst+0#32) (4#32) .w
  let c3 := c2.goto 0x80003432#32
  let r2 := ramWrite r1 (dst+4#32) (0#32) .w
  let c4 := c3.goto 0x80003436#32
  let r3 := ramWrite r2 (dst+8#32) (status) .h
  let c5 := c4.goto 0x8000343a#32
  let c6 := c5.goto 0x80002d6a#32
  have t0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine Quiet.step_of (by rw [hp];decide) (by rw [hp];exact hh2147497004) fun o => ?_
    change Observed.interp B img o (exec c _ _) ram 0 [] [] = ⟨.ok c1 ram [],[]⟩
    rw [exec_opimm,Core.get_zero];first | rfl | (rw [hp];rfl)
  have t1 : Quiet.Step B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    refine Quiet.step_of (by change (0x8000342e#32).getLsbD 0=false;decide) hh2147497006 fun o => ?_
    change Observed.interp B img o (exec c1 _ _) ram 0 [] [] = ⟨.ok c2 ram [],[]⟩
    have v2 : c1.get 2=sp := by simp [c1,Core.wr_get_ne,Core.wr_get,h2,h1]
    rw [exec_load,v2,Quiet.interp_load_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 13 ha)
      (Memory.block_access stack (off := 52) (by decide) (by decide)),hword];first | rfl | (rw [hp];rfl)
  have t2 : Quiet.Step B img ⟨c2,ram⟩ ⟨c3,r1⟩ := by
    refine Quiet.step_of (by change (0x80003430#32).getLsbD 0=false;decide) hh2147497008 fun o => ?_
    change Observed.interp B img o (exec c2 _ _) ram 0 [] [] = ⟨.ok c3 r1 [],[]⟩
    have v11 : c2.get 11=dst := by simp [c2,c1,Core.wr_get_ne,Core.wr_get,h2,h1]
    have vv : c2.get 10=4#32 := by simp [c2,c1,Core.wr_get_ne,Core.wr_get,h2,h1]
    rw [exec_store,v11,vv,Quiet.interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned dst 0 aligned)
     (Memory.block_access hm (off := 0) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t3 : Quiet.Step B img ⟨c3,r1⟩ ⟨c4,r2⟩ := by
    refine Quiet.step_of (by change (0x80003432#32).getLsbD 0=false;decide) hh2147497010 fun o => ?_
    change Observed.interp B img o (exec c3 _ _) r1 0 [] [] = ⟨.ok c4 r2 [],[]⟩
    have v11 : c3.get 11=dst := by simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h1]
    rw [exec_store,v11,Core.get_zero,Quiet.interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned dst 1 aligned)
     (Memory.block_access hm (off := 4) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t4 : Quiet.Step B img ⟨c4,r2⟩ ⟨c5,r3⟩ := by
    refine Quiet.step_of (by change (0x80003436#32).getLsbD 0=false;decide) hh2147497014 fun o => ?_
    change Observed.interp B img o (exec c4 _ _) r2 0 [] [] = ⟨.ok c5 r3 [],[]⟩
    have v11 : c4.get 11=dst := by simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h1]
    have vv : c4.get 1=status := by simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h1]
    rw [exec_store,v11,vv,Quiet.interp_store_ram (B := B) (img := img) (w := .h) o (Memory.half_aligned dst 4 (by omega))
     (Memory.block_access hm (off := 8) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t5 : Quiet.Step B img ⟨c5,r3⟩ ⟨c6,r3⟩ := by
    refine Quiet.step_of (by change (0x8000343a#32).getLsbD 0=false;decide) hh2147497018 fun o => ?_
    change Observed.interp B img o (exec c5 _ _) r3 0 [] [] = ⟨.ok c6 r3 [],[]⟩
    rw [exec_jal,Core.set_zero]
    change Observed.interp B img o (jump c5 (0x8000343a#32+0xfffff930#32)) r3 0 [] [] = _
    rw [show 0x8000343a#32+0xfffff930#32=0x80002d6a#32 by decide +kernel,jump_ok _ _ (by decide)];first | rfl | (rw [hp];rfl)
  refine ⟨c6,.step t0 (.step t1 (.step t2 (.step t3 (.step t4 (.single t5))))),rfl,?_ ,?_ ,?_ ,by rfl⟩
  · simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h1]
  · simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h1]
  · intro reg h10 h11;simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h1,h10,h11]
end E5R.Thermostat.HeadFieldsRejectStore
