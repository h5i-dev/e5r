import Projects.thermostat.UartWriteCode
import Projects.thermostat.QuietRam
import Projects.thermostat.Memory
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.UartWriteRemaining
open E5R E5R.Thermostat

def memory (ram : Word → BitVec 8) (obj ptr len : Word) :=
  ramWrite (ramWrite (ram) (obj+16#32) (ptr) .w) (obj+20#32) (len) .w

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (obj ptr len : Word) (h10 : c.get 10=obj) (h11 : c.get 11=ptr) (h12 : c.get 12=len) (hm : Memory.Block B obj 41) (ha : obj.toNat%4=0)
    (hp : c.pc=0x800007c8#32) :
    ∃ d, Quiet.Steps B img 2 ⟨c,ram⟩ ⟨d,memory ram obj ptr len⟩ ∧ d.pc=0x800007cc#32 ∧
      (∀ r : Reg, d.get r=c.get r) ∧ d.sameCsr c := by
  let r1 := ramWrite ram (obj+16#32) (ptr) .w
  let c1 := c.goto 0x800007ca#32
  let r2 := ramWrite r1 (obj+20#32) (len) .w
  let c2 := c1.goto 0x800007cc#32
  have t0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,r1⟩ := by
    refine Quiet.step_of (by rw [hp];decide) (by rw [hp];exact uw2147485640) fun o => ?_
    change Observed.interp B img o (exec c _ _) ram 0 [] [] = ⟨.ok c1 r1 [],[]⟩
    have v10 : c.get 10=obj := by simp [Core.wr_get_ne,Core.wr_get,h10,h11,h12]
    have vv : c.get 11=ptr := by simp [Core.wr_get_ne,Core.wr_get,h10,h11,h12]
    rw [exec_store,v10,vv,Quiet.interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned obj 4 ha) (Memory.block_access hm (off := 16) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t1 : Quiet.Step B img ⟨c1,r1⟩ ⟨c2,r2⟩ := by
    refine Quiet.step_of (by change (0x800007ca#32).getLsbD 0=false;decide) uw2147485642 fun o => ?_
    change Observed.interp B img o (exec c1 _ _) r1 0 [] [] = ⟨.ok c2 r2 [],[]⟩
    have v10 : c1.get 10=obj := by simp [c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12]
    have vv : c1.get 12=len := by simp [c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12]
    rw [exec_store,v10,vv,Quiet.interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned obj 5 ha) (Memory.block_access hm (off := 20) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  refine ⟨c2,.step t0 (.single t1),rfl,?_ ,by rfl⟩
  · intro reg ;simp [c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12]
end E5R.Thermostat.UartWriteRemaining
