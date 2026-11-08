import Projects.thermostat.UartWriteCode
import Projects.thermostat.QuietRam
import Projects.thermostat.Memory
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.UartWriteFresh
open E5R E5R.Thermostat

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (obj : Word) (h10 : c.get 10=obj) (hm : Memory.Block B obj 41) (hz : ram (obj+40#32)=0#8)
    (hp : c.pc = 0x80000786#32) :
    ∃ d, Quiet.Steps B img 3 ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc = 0x800007ae#32 ∧
      d.get 11 = 0#32 ∧ d.get 13 = 0x10000000#32 ∧ (∀ r : Reg, r ≠ 11 → r ≠ 13 → d.get r = c.get r) ∧ d.sameCsr c := by
  let c1 := c.wr 11 (0#32) 0x8000078a#32
  let c2 := c1.wr 13 (0x10000000#32) 0x8000078e#32
  let c3 := c2.goto 0x800007ae#32
  have s0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine Quiet.step_of (by rw [hp];decide) (by rw [hp];exact uw2147485574) fun o => ?_
    rw [exec_load,h10,Quiet.interp_load_ram (B := B) (img := img) (w := .b) o (by exact Nat.mod_one _) (Memory.block_access hm (off := 40) (by decide) (by decide)),Memory.load_byte]
    change Observed.interp B img o (.done (c.wr 11 (BitVec.ofNat 32 (ram (obj+40#32)).toNat) (c.pc+4#32))) ram 0 [] [] = _
    rw [hz,hp];first | rfl | (rw [hp]; rfl)
  have s1 : Quiet.Step B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    refine Quiet.step_of (by change (0x8000078a#32).getLsbD 0 = false;decide) uw2147485578 fun o => ?_
    rw [exec_lui];first | rfl | (rw [hp]; rfl)
  have s2 : Quiet.Step B img ⟨c2,ram⟩ ⟨c3,ram⟩ := by
    refine Quiet.step_of (by change (0x8000078e#32).getLsbD 0 = false;decide) uw2147485582 fun o => ?_
    have hv : c2.get 11=0#32 := by simp [c2,c1,Core.wr_get_ne,Core.wr_get,h10]
    rw [exec_branch,hv,Core.get_zero,show taken .eq 0#32 (0 : Word)=true by decide]
    simp only [ite_true]
    change Observed.interp B img o (jump c2 0x800007ae#32) ram 0 [] [] = _
    rw [jump_ok _ _ (by decide)];first | rfl | (rw [hp]; rfl)
  refine ⟨c3,.step s0 (.step s1 (.single s2)),rfl,?_ ,?_ ,?_ ,by rfl⟩
  · simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10]
  · simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10]
  · intro r h11 h13
    simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h13]
end E5R.Thermostat.UartWriteFresh
