import Projects.thermostat.HttpParseCode01
import Projects.thermostat.QuietRam
import Projects.thermostat.Memory
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.HeadResultStore
open E5R E5R.Thermostat

def memory (ram : Word → BitVec 8) (dst tag status : Word) :=
  ramWrite (ramWrite (ramWrite (ram) (dst+0#32) (tag) .w) (dst+4#32) (0#32) .w) (dst+8#32) (status) .h

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (dst tag status : Word) (h10 : c.get 10=dst) (h11 : c.get 11=tag) (h12 : c.get 12=status)
(hm : Memory.Block B dst 12) (ha : dst.toNat%4=0)
    (hp : c.pc=0x80002d60#32) :
    ∃ d, Quiet.Steps B img 3 ⟨c,ram⟩ ⟨d,memory ram dst tag status⟩ ∧ d.pc=0x80002d6a#32 ∧
      (∀ r : Reg, d.get r=c.get r) ∧ d.sameCsr c := by
  let r1 := ramWrite ram (dst+0#32) (tag) .w
  let c1 := c.goto 0x80002d62#32
  let r2 := ramWrite r1 (dst+4#32) (0#32) .w
  let c2 := c1.goto 0x80002d66#32
  let r3 := ramWrite r2 (dst+8#32) (status) .h
  let c3 := c2.goto 0x80002d6a#32
  have t0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,r1⟩ := by
    refine Quiet.step_of (by rw [hp];decide) (by rw [hp];exact hh2147495264) fun o => ?_
    change Observed.interp B img o (exec c _ _) ram 0 [] [] = ⟨.ok c1 r1 [],[]⟩
    have v10 : c.get 10=dst := by simp [Core.wr_get_ne,Core.wr_get,h10,h11,h12]
    have vv : c.get 11=tag := by simp [Core.wr_get_ne,Core.wr_get,h10,h11,h12]
    rw [exec_store,v10,vv,Quiet.interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned dst 0 ha)
    (Memory.block_access hm (off := 0) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t1 : Quiet.Step B img ⟨c1,r1⟩ ⟨c2,r2⟩ := by
    refine Quiet.step_of (by change (0x80002d62#32).getLsbD 0=false;decide) hh2147495266 fun o => ?_
    change Observed.interp B img o (exec c1 _ _) r1 0 [] [] = ⟨.ok c2 r2 [],[]⟩
    have v10 : c1.get 10=dst := by simp [c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12]
    rw [exec_store,v10,Core.get_zero,Quiet.interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned dst 1 ha)
    (Memory.block_access hm (off := 4) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t2 : Quiet.Step B img ⟨c2,r2⟩ ⟨c3,r3⟩ := by
    refine Quiet.step_of (by change (0x80002d66#32).getLsbD 0=false;decide) hh2147495270 fun o => ?_
    change Observed.interp B img o (exec c2 _ _) r2 0 [] [] = ⟨.ok c3 r3 [],[]⟩
    have v10 : c2.get 10=dst := by simp [c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12]
    have vv : c2.get 12=status := by simp [c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12]
    rw [exec_store,v10,vv,Quiet.interp_store_ram (B := B) (img := img) (w := .h) o (Memory.half_aligned dst 4 (by omega))
    (Memory.block_access hm (off := 8) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  refine ⟨c3,.step t0 (.step t1 (.single t2)),rfl,?_ ,by rfl⟩
  · intro reg ;simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12]
end E5R.Thermostat.HeadResultStore
