import Projects.thermostat.HttpParseCode
import Projects.thermostat.QuietRam
import Projects.thermostat.Memory
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.HeadFieldsLength
open E5R E5R.Thermostat

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (sp length maximum : Word) (h2 : c.get 2=sp) (hlength : ramRead ram (sp+48#32) .w=length) (hmaximum : ramRead ram (sp+36#32) .w=maximum)
(hm : Memory.Block B sp 56) (ha : sp.toNat%4=0)
    (hp : c.pc=0x800033ea#32) :
    ∃ d, Quiet.Steps B img 2 ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc=0x800033ee#32 ∧
      d.get 10=length ∧ d.get 11=maximum ∧ (∀ r : Reg, r≠10 → r≠11 → d.get r=c.get r) ∧ d.sameCsr c := by
  let c1 := c.wr 10 (length) 0x800033ec#32
  let c2 := c1.wr 11 (maximum) 0x800033ee#32
  have t0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine Quiet.step_of (by rw [hp];decide) (by rw [hp];exact hh2147496938) fun o => ?_
    change Observed.interp B img o (exec c _ _) ram 0 [] [] = ⟨.ok c1 ram [],[]⟩
    have v2 : c.get 2=sp := by simp [Core.wr_get_ne,Core.wr_get,h2]
    rw [exec_load,v2,Quiet.interp_load_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 12 ha)
      (Memory.block_access hm (off := 48) (by decide) (by decide)),hlength];first | rfl | (rw [hp];rfl)
  have t1 : Quiet.Step B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    refine Quiet.step_of (by change (0x800033ec#32).getLsbD 0=false;decide) hh2147496940 fun o => ?_
    change Observed.interp B img o (exec c1 _ _) ram 0 [] [] = ⟨.ok c2 ram [],[]⟩
    have v2 : c1.get 2=sp := by simp [c1,Core.wr_get_ne,Core.wr_get,h2]
    rw [exec_load,v2,Quiet.interp_load_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 9 ha)
      (Memory.block_access hm (off := 36) (by decide) (by decide)),hmaximum];first | rfl | (rw [hp];rfl)
  refine ⟨c2,.step t0 (.single t1),rfl,?_ ,?_ ,?_ ,by rfl⟩
  · simp [c2,c1,Core.wr_get_ne,Core.wr_get,h2]
  · simp [c2,c1,Core.wr_get_ne,Core.wr_get,h2]
  · intro reg h10 h11;simp [c2,c1,Core.wr_get_ne,Core.wr_get,h2,h10,h11]
end E5R.Thermostat.HeadFieldsLength
