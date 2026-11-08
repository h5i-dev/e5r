import Projects.thermostat.HttpParseCode
import Projects.thermostat.QuietRam
import Projects.thermostat.Memory
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.HeadTeFlagStore
open E5R E5R.Thermostat

def memory (ram : Word → BitVec 8) (sp : Word) :=
  ramWrite (ram) (sp+326#32) (1#32) .b

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (sp : Word) (h2 : c.get 2=sp) (hm : B.inRam (sp+326#32) 1=true)
    (hp : c.pc=0x800033b0#32) :
    ∃ d, Quiet.Steps B img 2 ⟨c,ram⟩ ⟨d,memory ram sp⟩ ∧ d.pc=0x800033b6#32 ∧
      d.get 10=1#32 ∧ (∀ r : Reg, r≠10 → d.get r=c.get r) ∧ d.sameCsr c := by
  let c1 := c.wr 10 (1#32) 0x800033b2#32
  let r1 := ramWrite ram (sp+326#32) (1#32) .b
  let c2 := c1.goto 0x800033b6#32
  have t0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine Quiet.step_of (by rw [hp];decide) (by rw [hp];exact hh2147496880) fun o => ?_
    change Observed.interp B img o (exec c _ _) ram 0 [] [] = ⟨.ok c1 ram [],[]⟩
    rw [exec_opimm,Core.get_zero];first | rfl | (rw [hp];rfl)
  have t1 : Quiet.Step B img ⟨c1,ram⟩ ⟨c2,r1⟩ := by
    refine Quiet.step_of (by change (0x800033b2#32).getLsbD 0=false;decide) hh2147496882 fun o => ?_
    change Observed.interp B img o (exec c1 _ _) ram 0 [] [] = ⟨.ok c2 r1 [],[]⟩
    have v2 : c1.get 2=sp := by simp [c1,Core.wr_get_ne,Core.wr_get,h2]
    have v10 : c1.get 10=1#32 := by simp [c1,Core.wr_get_ne,Core.wr_get,h2]
    rw [exec_store,v2,v10,Quiet.interp_store_ram (B := B) (img := img) (w := .b) o (by exact Nat.mod_one _) hm];first | rfl | (rw [hp];rfl)
  refine ⟨c2,.step t0 (.single t1),rfl,?_ ,?_ ,by rfl⟩
  · simp [c2,c1,Core.wr_get_ne,Core.wr_get,h2]
  · intro reg h10;simp [c2,c1,Core.wr_get_ne,Core.wr_get,h2,h10]
end E5R.Thermostat.HeadTeFlagStore
