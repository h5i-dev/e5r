-- Generated stronger trace proofs; Lean checks every decoded-instruction side condition.
import Projects.thermostat.ReleaseBorrowRegs
import Projects.thermostat.QuietDet
import Projects.thermostat.RamRunQuiet
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
open E5R E5R.Thermostat
namespace E5R.Thermostat.ReleaseBorrow
theorem contract_regs_quiet (B : Board) (c : Core) (ram : Word → BitVec 8)
    (hp : c.pc = 0x80000648) (he : Memory.Block B (c.get 23) 14)
    (ha : (c.get 23).toNat % 4 = 0) :
    ∃ d, Quiet.Steps B img 3 ⟨c,ram⟩ ⟨d,result ram (c.get 23)⟩ ∧ d.pc = 0x80000652 ∧
      d.get 2 = c.get 2 ∧ d.get 20 = c.get 20 ∧ d.get 23 = c.get 23 ∧ d.sameCsr c ∧ (∀ r : Reg, r ≠ 11 → d.get r = c.get r) := by
  let eng := c.get 23
  let v := ramRead ram eng .w
  let c1 := c.wr 11 v 0x8000064c
  let c2 := c1.wr 11 (v+1#32) 0x8000064e
  let d := c2.goto 0x80000652
  have hr : B.inRam eng 4 = true := by
    simpa using Memory.block_access (B := B) (p := eng) (n := 14) (off := 0) (width := 4) he (by decide) (by decide)
  have s0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine QuietDet.step_of (by rw [hp];decide) (by rw [hp];exact u2147485256) fun o => ?_
    rw [exec_load,BitVec.add_zero,interp_load_ram (B := B) (img := img) (w := .w) (a := eng) o ha hr,hp]
    rfl
  have s1 : Quiet.Step B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    refine QuietDet.step_of (by change (0x8000064c : Word).getLsbD 0 = false;decide) u2147485260 fun o => ?_
    have hv : c1.get 11 = v := by simp [c1,Core.wr_get]
    rw [exec_opimm,hv]
    rfl
  have s2 : Quiet.Step B img ⟨c2,ram⟩ ⟨d,result ram eng⟩ := by
    refine QuietDet.step_of (by change (0x8000064e : Word).getLsbD 0 = false;decide) u2147485262 fun o => ?_
    have hs : c2.get 23 = eng := by simp [c2,c1,eng,Core.wr_get_ne]
    have hv : c2.get 11 = v+1#32 := by simp [c2,Core.wr_get]
    rw [exec_store,hs,hv,BitVec.add_zero,interp_store_ram (B := B) (img := img) (w := .w) (a := eng) (v := v+1#32) o ha hr]
    rfl
  refine ⟨d,.step s0 (.step s1 (.single s2)),rfl,?_,?_,?_,by rfl,?_⟩
  · simp [d,c2,c1,Core.wr_get_ne]
  · simp [d,c2,c1,Core.wr_get_ne]
  · simp [d,c2,c1,Core.wr_get_ne]
  · intro reg hr
    simp [d,c2,c1,Core.wr_get_ne,hr]

end E5R.Thermostat.ReleaseBorrow
