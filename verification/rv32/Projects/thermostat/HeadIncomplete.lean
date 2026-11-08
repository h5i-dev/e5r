import Projects.thermostat.HttpParseCode00
import Projects.thermostat.QuietRam
import Projects.thermostat.Memory
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.HeadIncomplete
open E5R E5R.Thermostat

def memory (ram : Word → BitVec 8) (dst : Word) :=
  ramWrite (ramWrite (ram) (dst+0#32) (3#32) .w) (dst+4#32) (0#32) .w

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (dst : Word) (h10 : c.get 10=dst) (hm : Memory.Block B dst 12) (ha : dst.toNat%4=0)
    (hp : c.pc=0x80002cea#32) :
    ∃ d, Quiet.Steps B img 4 ⟨c,ram⟩ ⟨d,memory ram dst⟩ ∧ d.pc=0x80002d6a#32 ∧
      d.get 11=3#32 ∧ (∀ r : Reg, r≠11 → d.get r=c.get r) ∧ d.sameCsr c := by
  let c1 := c.wr 11 (3#32) 0x80002cec#32
  let r1 := ramWrite ram (dst+0#32) (3#32) .w
  let c2 := c1.goto 0x80002cee#32
  let r2 := ramWrite r1 (dst+4#32) (0#32) .w
  let c3 := c2.goto 0x80002cf2#32
  let c4 := c3.goto 0x80002d6a#32
  have t0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine Quiet.step_of (by rw [hp];decide) (by rw [hp];exact hh2147495146) fun o => ?_
    change Observed.interp B img o (exec c _ _) ram 0 [] [] = ⟨.ok c1 ram [],[]⟩
    rw [exec_opimm,Core.get_zero];first | rfl | (rw [hp];rfl)
  have t1 : Quiet.Step B img ⟨c1,ram⟩ ⟨c2,r1⟩ := by
    refine Quiet.step_of (by change (0x80002cec#32).getLsbD 0=false;decide) hh2147495148 fun o => ?_
    change Observed.interp B img o (exec c1 _ _) ram 0 [] [] = ⟨.ok c2 r1 [],[]⟩
    have v10 : c1.get 10=dst := by simp [c1,Core.wr_get_ne,Core.wr_get,h10]
    have v11 : c1.get 11=3#32 := by simp [c1,Core.wr_get_ne,Core.wr_get,h10]
    rw [exec_store,v10,v11,Quiet.interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned dst 0 ha)
    (Memory.block_access hm (off := 0) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t2 : Quiet.Step B img ⟨c2,r1⟩ ⟨c3,r2⟩ := by
    refine Quiet.step_of (by change (0x80002cee#32).getLsbD 0=false;decide) hh2147495150 fun o => ?_
    change Observed.interp B img o (exec c2 _ _) r1 0 [] [] = ⟨.ok c3 r2 [],[]⟩
    have v10 : c2.get 10=dst := by simp [c2,c1,Core.wr_get_ne,Core.wr_get,h10]
    rw [exec_store,v10,Core.get_zero,Quiet.interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned dst 1 ha)
    (Memory.block_access hm (off := 4) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t3 : Quiet.Step B img ⟨c3,r2⟩ ⟨c4,r2⟩ := by
    refine Quiet.step_of (by change (0x80002cf2#32).getLsbD 0=false;decide) hh2147495154 fun o => ?_
    change Observed.interp B img o (exec c3 _ _) r2 0 [] [] = ⟨.ok c4 r2 [],[]⟩
    rw [exec_jal,Core.set_zero]
    change Observed.interp B img o (jump c3 (0x80002cf2#32+0x78#32)) r2 0 [] []=_
    rw [show 0x80002cf2#32+0x78#32=0x80002d6a#32 by decide +kernel,jump_ok _ _ (by decide)];first | rfl | (rw [hp];rfl)
  refine ⟨c4,.step t0 (.step t1 (.step t2 (.single t3))),rfl,?_ ,?_ ,by rfl⟩
  · simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10]
  · intro reg h11;simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11]
end E5R.Thermostat.HeadIncomplete
