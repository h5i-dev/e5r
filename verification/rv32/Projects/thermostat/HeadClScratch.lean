import Projects.thermostat.HttpParseCode
import Projects.thermostat.QuietRam
import Projects.thermostat.Memory
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.HeadClScratch
open E5R E5R.Thermostat

def memory (ram : Word → BitVec 8) (sp start finish span : Word) :=
  ramWrite (ram) (sp+0#32) ((start-finish)+span) .w

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (sp start finish span : Word) (h2 : c.get 2=sp) (h24 : c.get 24=start) (h25 : c.get 25=finish) (h21 : c.get 21=span) (stack : Memory.Block B sp 56) (ha : sp.toNat%4=0)
    (hp : c.pc=0x80003192#32) :
    ∃ d, Quiet.Steps B img 3 ⟨c,ram⟩ ⟨d,memory ram sp start finish span⟩ ∧ d.pc=0x8000319a#32 ∧
      d.get 10=(start-finish)+span ∧ (∀ r : Reg, r≠10 → d.get r=c.get r) ∧ d.sameCsr c := by
  let c1 := c.wr 10 (start-finish) 0x80003196#32
  let c2 := c1.wr 10 ((start-finish)+span) 0x80003198#32
  let r1 := ramWrite ram (sp+0#32) ((start-finish)+span) .w
  let c3 := c2.goto 0x8000319a#32
  have t0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine Quiet.step_of (by rw [hp];decide) (by rw [hp];exact hh2147496338) fun o => ?_
    change Observed.interp B img o (exec c _ _) ram 0 [] [] = ⟨.ok c1 ram [],[]⟩
    rw [exec_op,h24,h25];first | rfl | (rw [hp];rfl)
  have t1 : Quiet.Step B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    refine Quiet.step_of (by change (0x80003196#32).getLsbD 0=false;decide) hh2147496342 fun o => ?_
    change Observed.interp B img o (exec c1 _ _) ram 0 [] [] = ⟨.ok c2 ram [],[]⟩
    have v10 : c1.get 10=start-finish := by simp [c1,Core.wr_get_ne,Core.wr_get,h2,h24,h25,h21]
    have v21 : c1.get 21=span := by simp [c1,Core.wr_get_ne,Core.wr_get,h2,h24,h25,h21]
    rw [exec_op,v10,v21];first | rfl | (rw [hp];rfl)
  have t2 : Quiet.Step B img ⟨c2,ram⟩ ⟨c3,r1⟩ := by
    refine Quiet.step_of (by change (0x80003198#32).getLsbD 0=false;decide) hh2147496344 fun o => ?_
    change Observed.interp B img o (exec c2 _ _) ram 0 [] [] = ⟨.ok c3 r1 [],[]⟩
    have v2 : c2.get 2=sp := by simp [c2,c1,Core.wr_get_ne,Core.wr_get,h2,h24,h25,h21]
    have v10 : c2.get 10=(start-finish)+span := by simp [c2,c1,Core.wr_get_ne,Core.wr_get,h2,h24,h25,h21]
    rw [exec_store,v2,v10,Quiet.interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 0 ha)
     (Memory.block_access stack (off := 0) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  refine ⟨c3,.step t0 (.step t1 (.single t2)),rfl,?_ ,?_ ,by rfl⟩
  · simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h24,h25,h21]
  · intro reg h10;simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h24,h25,h21,h10]
end E5R.Thermostat.HeadClScratch
