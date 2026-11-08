import Projects.thermostat.WriteHandlerCode
import Projects.thermostat.Memory
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.FutureExtract
open E5R E5R.Thermostat

theorem fresh (B : Board) (c : Core) (ram : Word → BitVec 8) (f out : Word)
    (hp : c.pc = 0x800004e2#32) (h11 : c.get 11 = f) (h10 : c.get 10 = out)
    (hm : Memory.Block B f 41) (hz : ram (f+40#32) = 0#8) :
    ∃ d, DetSteps B img 4 ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc = 0x8000050a#32 ∧
      d.get 8 = f ∧ d.get 9 = out ∧
      (∀ r : Reg, r ≠ 8 → r ≠ 9 → r ≠ 11 → d.get r = c.get r) ∧ d.sameCsr c := by
  let c1 := c.wr 8 f 0x800004e4#32
  let c2 := c1.wr 11 0#32 0x800004e8#32
  let c3 := c2.wr 9 out 0x800004ea#32
  let d := c3.goto 0x8000050a#32
  have s0 : DetStep B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine detStep_of (by rw [hp];decide) (by rw [hp];exact wh2147484898) fun o => ?_
    rw [exec_op,h11,Core.get_zero,hp];simp only [alu,show (0 : Word) = 0#32 from rfl,BitVec.zero_add];rfl
  have s1 : DetStep B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    refine detStep_of (by change (0x800004e4#32).getLsbD 0 = false;decide) wh2147484900 fun o => ?_
    have hf : c1.get 11 = f := (Core.wr_get_ne c 8 11 f _ (by decide)).trans h11
    rw [exec_load,hf,interp_load_ram (B := B) (img := img) (w := .b) (a := f+40#32) o (by exact Nat.mod_one _)
      (Memory.block_access hm (off := 40) (by decide) (by decide)),Memory.load_byte]
    change interp B img o (.done (c1.wr 11 (BitVec.ofNat 32 (ram (f+40#32)).toNat) 0x800004e8#32)) ram 0 [] = _
    rw [hz];rfl
  have s2 : DetStep B img ⟨c2,ram⟩ ⟨c3,ram⟩ := by
    refine detStep_of (by change (0x800004e8#32).getLsbD 0 = false;decide) wh2147484904 fun o => ?_
    have ho : c2.get 10 = out := by simp [c2,c1,Core.wr_get_ne,h10]
    rw [exec_op,Core.get_zero,ho];simp only [alu,show (0 : Word) = 0#32 from rfl,BitVec.zero_add];rfl
  have s3 : DetStep B img ⟨c3,ram⟩ ⟨d,ram⟩ := by
    refine detStep_of (by change (0x800004ea#32).getLsbD 0 = false;decide) wh2147484906 fun o => ?_
    have hz' : c3.get 11 = 0#32 := by simp [c3,c2,Core.wr_get_ne,Core.wr_get]
    rw [exec_branch,hz',Core.get_zero,show taken .eq 0#32 (0 : Word) = true by decide]
    simp only [ite_true]
    change interp B img o (jump c3 0x8000050a#32) ram 0 [] = _
    rw [jump_ok c3 _ (by decide)];rfl
  refine ⟨d,.step s0 (.step s1 (.step s2 (.single s3))),rfl,?_,?_,?_,by rfl⟩
  · simp [d,c3,c2,c1,Core.wr_get_ne,Core.wr_get]
  · simp [d,c3,c2,c1,Core.wr_get_ne,Core.wr_get]
  · intro r h8 h9 h11
    simp [d,c3,c2,c1,Core.wr_get_ne,h8,h9,h11]
end E5R.Thermostat.FutureExtract
