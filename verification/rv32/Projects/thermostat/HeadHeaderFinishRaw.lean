import Projects.thermostat.HttpParseCode
import Projects.thermostat.QuietRam
import Projects.thermostat.Memory
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.HeadHeaderFinishRaw
open E5R E5R.Thermostat

def memory (ram : Word → BitVec 8) (sp p ne count : Word) :=
  ramWrite (ramWrite (ram) (p+4#32) (ne) .w) (sp+320#32) (count) .w

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (sp p ne count : Word) (h2 : c.get 2=sp) (h10 : c.get 10=p) (h9 : c.get 9=count) (hname : ramRead ram (sp+4#32) .w=ne)
(stack : Memory.Block B sp 327) (ha : sp.toNat%4=0) (pmem : Memory.Block B p 16) (aligned : p.toNat%4=0)
    (hp : c.pc=0x800033d0#32) :
    ∃ d, Quiet.Steps B img 3 ⟨c,ram⟩ ⟨d,memory ram sp p ne count⟩ ∧ d.pc=0x800033d8#32 ∧
      d.get 11=ne ∧ (∀ r : Reg, r≠11 → d.get r=c.get r) ∧ d.sameCsr c := by
  let c1 := c.wr 11 (ne) 0x800033d2#32
  let r1 := ramWrite ram (p+4#32) (ne) .w
  let c2 := c1.goto 0x800033d4#32
  let r2 := ramWrite r1 (sp+320#32) (count) .w
  let c3 := c2.goto 0x800033d8#32
  have t0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine Quiet.step_of (by rw [hp];decide) (by rw [hp];exact hh2147496912) fun o => ?_
    change Observed.interp B img o (exec c _ _) ram 0 [] [] = ⟨.ok c1 ram [],[]⟩
    rw [exec_load,h2,Quiet.interp_load_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 1 ha)
     (Memory.block_access stack (off := 4) (by decide) (by decide)),hname];first | rfl | (rw [hp];rfl)
  have t1 : Quiet.Step B img ⟨c1,ram⟩ ⟨c2,r1⟩ := by
    refine Quiet.step_of (by change (0x800033d2#32).getLsbD 0=false;decide) hh2147496914 fun o => ?_
    change Observed.interp B img o (exec c1 _ _) ram 0 [] [] = ⟨.ok c2 r1 [],[]⟩
    have v10 : c1.get 10=p := by simp [c1,Core.wr_get_ne,Core.wr_get,h2,h10,h9]
    have v11 : c1.get 11=ne := by simp [c1,Core.wr_get_ne,Core.wr_get,h2,h10,h9]
    rw [exec_store,v10,v11,Quiet.interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned p 1 aligned)
     (Memory.block_access pmem (off := 4) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t2 : Quiet.Step B img ⟨c2,r1⟩ ⟨c3,r2⟩ := by
    refine Quiet.step_of (by change (0x800033d4#32).getLsbD 0=false;decide) hh2147496916 fun o => ?_
    change Observed.interp B img o (exec c2 _ _) r1 0 [] [] = ⟨.ok c3 r2 [],[]⟩
    have v2 : c2.get 2=sp := by simp [c2,c1,Core.wr_get_ne,Core.wr_get,h2,h10,h9]
    have v9 : c2.get 9=count := by simp [c2,c1,Core.wr_get_ne,Core.wr_get,h2,h10,h9]
    rw [exec_store,v2,v9,Quiet.interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 80 ha)
     (Memory.block_access stack (off := 320) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  refine ⟨c3,.step t0 (.step t1 (.single t2)),rfl,?_ ,?_ ,by rfl⟩
  · simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h10,h9]
  · intro reg h11;simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h10,h9,h11]
end E5R.Thermostat.HeadHeaderFinishRaw
