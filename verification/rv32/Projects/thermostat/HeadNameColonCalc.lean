import Projects.thermostat.HttpParseCode
import Projects.thermostat.QuietRam
import Projects.thermostat.Memory
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.HeadNameColonCalc
open E5R E5R.Thermostat

def memory (ram : Word → BitVec 8) (sp start count : Word) :=
  ramWrite (ram) (sp+4#32) (start+count) .w

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (sp start count : Word) (h2 : c.get 2=sp) (h24 : c.get 24=start) (h14 : c.get 14=count) (stack : Memory.Block B sp 56) (ha : sp.toNat%4=0)
    (hp : c.pc=0x8000305a#32) :
    ∃ d, Quiet.Steps B img 2 ⟨c,ram⟩ ⟨d,memory ram sp start count⟩ ∧ d.pc=0x80003060#32 ∧
      d.get 12=start+count ∧ (∀ r : Reg, r≠12 → d.get r=c.get r) ∧ d.sameCsr c := by
  let c1 := c.wr 12 (start+count) 0x8000305e#32
  let r1 := ramWrite ram (sp+4#32) (start+count) .w
  let c2 := c1.goto 0x80003060#32
  have t0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine Quiet.step_of (by rw [hp];decide) (by rw [hp];exact hh2147496026) fun o => ?_
    change Observed.interp B img o (exec c _ _) ram 0 [] [] = ⟨.ok c1 ram [],[]⟩
    rw [exec_op,h24,h14];first | rfl | (rw [hp];rfl)
  have t1 : Quiet.Step B img ⟨c1,ram⟩ ⟨c2,r1⟩ := by
    refine Quiet.step_of (by change (0x8000305e#32).getLsbD 0=false;decide) hh2147496030 fun o => ?_
    change Observed.interp B img o (exec c1 _ _) ram 0 [] [] = ⟨.ok c2 r1 [],[]⟩
    have v2 : c1.get 2=sp := by simp [c1,Core.wr_get_ne,Core.wr_get,h2,h24,h14]
    have v12 : c1.get 12=start+count := by simp [c1,Core.wr_get_ne,Core.wr_get,h2,h24,h14]
    rw [exec_store,v2,v12,Quiet.interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 1 ha)
     (Memory.block_access stack (off := 4) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  refine ⟨c2,.step t0 (.single t1),rfl,?_ ,?_ ,by rfl⟩
  · simp [c2,c1,Core.wr_get_ne,Core.wr_get,h2,h24,h14]
  · intro reg h12;simp [c2,c1,Core.wr_get_ne,Core.wr_get,h2,h24,h14,h12]
end E5R.Thermostat.HeadNameColonCalc
