import Projects.thermostat.HttpParseCode
import Projects.thermostat.QuietRam
import Projects.thermostat.HeadResultStore
import Projects.thermostat.Memory
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.HeadMethodRejectStore
open E5R E5R.Thermostat

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (dst status : Word) (h10 : c.get 10=dst) (h15 : c.get 15=status)
(hm : Memory.Block B dst 12) (ha : dst.toNat%4=0)
    (hp : c.pc=0x80002efc#32) :
    ∃ d, Quiet.Steps B img 5 ⟨c,ram⟩ ⟨d,HeadResultStore.memory ram dst 4#32 status⟩ ∧ d.pc=0x80002d6a#32 ∧
      d.get 11=4#32 ∧ (∀ r : Reg, r≠11 → d.get r=c.get r) ∧ d.sameCsr c := by
  let c1 := c.wr 11 (4#32) 0x80002efe#32
  let r1 := ramWrite ram (dst+0#32) (4#32) .w
  let c2 := c1.goto 0x80002f00#32
  let r2 := ramWrite r1 (dst+4#32) (0#32) .w
  let c3 := c2.goto 0x80002f04#32
  let r3 := ramWrite r2 (dst+8#32) (status) .h
  let c4 := c3.goto 0x80002f08#32
  let c5 := c4.goto 0x80002d6a#32
  have t0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine Quiet.step_of (by rw [hp];decide) (by rw [hp];exact hh2147495676) fun o => ?_
    change Observed.interp B img o (exec c _ _) ram 0 [] [] = ⟨.ok c1 ram [],[]⟩
    rw [exec_opimm,Core.get_zero];first | rfl | (rw [hp];rfl)
  have t1 : Quiet.Step B img ⟨c1,ram⟩ ⟨c2,r1⟩ := by
    refine Quiet.step_of (by change (0x80002efe#32).getLsbD 0=false;decide) hh2147495678 fun o => ?_
    change Observed.interp B img o (exec c1 _ _) ram 0 [] [] = ⟨.ok c2 r1 [],[]⟩
    have v10 : c1.get 10=dst := by simp [c1,Core.wr_get_ne,Core.wr_get,h10,h15]
    have vv : c1.get 11=4#32 := by simp [c1,Core.wr_get_ne,Core.wr_get,h10,h15]
    rw [exec_store,v10,vv,Quiet.interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned dst 0 ha)
        (Memory.block_access hm (off := 0) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t2 : Quiet.Step B img ⟨c2,r1⟩ ⟨c3,r2⟩ := by
    refine Quiet.step_of (by change (0x80002f00#32).getLsbD 0=false;decide) hh2147495680 fun o => ?_
    change Observed.interp B img o (exec c2 _ _) r1 0 [] [] = ⟨.ok c3 r2 [],[]⟩
    have v10 : c2.get 10=dst := by simp [c2,c1,Core.wr_get_ne,Core.wr_get,h10,h15]
    rw [exec_store,v10,Core.get_zero,Quiet.interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned dst 1 ha)
        (Memory.block_access hm (off := 4) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t3 : Quiet.Step B img ⟨c3,r2⟩ ⟨c4,r3⟩ := by
    refine Quiet.step_of (by change (0x80002f04#32).getLsbD 0=false;decide) hh2147495684 fun o => ?_
    change Observed.interp B img o (exec c3 _ _) r2 0 [] [] = ⟨.ok c4 r3 [],[]⟩
    have v10 : c3.get 10=dst := by simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h15]
    have vv : c3.get 15=status := by simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h15]
    rw [exec_store,v10,vv,Quiet.interp_store_ram (B := B) (img := img) (w := .h) o (Memory.half_aligned dst 4 (by omega))
        (Memory.block_access hm (off := 8) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t4 : Quiet.Step B img ⟨c4,r3⟩ ⟨c5,r3⟩ := by
    refine Quiet.step_of (by change (0x80002f08#32).getLsbD 0=false;decide) hh2147495688 fun o => ?_
    change Observed.interp B img o (exec c4 _ _) r3 0 [] [] = ⟨.ok c5 r3 [],[]⟩
    rw [exec_jal]
    change Observed.interp B img o (jump (c4.set 0 (c4.pc+2#32)) (0x80002f08#32+0xfffffe62#32)) r3 0 [] [] = _
    rw [show 0x80002f08#32+0xfffffe62#32=0x80002d6a#32 by decide +kernel,jump_ok _ _ (by decide)]
    rfl
  refine ⟨c5,.step t0 (.step t1 (.step t2 (.step t3 (.single t4)))),rfl,?_ ,?_ ,by rfl⟩
  · simp [c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h15]
  · intro reg h11;simp [c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h15,h11]
end E5R.Thermostat.HeadMethodRejectStore
