-- Generated stronger trace proofs; Lean checks every decoded-instruction side condition.
import Projects.thermostat.ReadAcquire
import Projects.thermostat.QuietDet
import Projects.thermostat.RamRunQuiet
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
open E5R E5R.Thermostat
namespace E5R.Thermostat.ReadAcquire
theorem available_quiet (B : Board) (c : Core) (ram : Word → BitVec 8)
    (hp : c.pc = 0x80001a08) (he : Memory.Block B (c.get 9) 14)
    (ha : (c.get 9).toNat % 4 = 0) (hb : ramRead ram (c.get 9) .w = 0#32) :
    Quiet.Steps B img 4 ⟨c,ram⟩ ⟨acquired c,result ram (c.get 9)⟩ := by
  let eng := c.get 9
  let v := ramRead ram eng .w
  let c1 := c.wr 10 v 0x80001a0a
  have hr : B.inRam eng 4 = true := by
    simpa using Memory.block_access (B := B) (p := eng) (n := 14) (off := 0) (width := 4) he (by decide) (by decide)
  have s0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine QuietDet.step_of (by rw [hp];decide) (by rw [hp];exact rs2147490312) fun o => ?_
    rw [exec_load,BitVec.add_zero,interp_load_ram (B := B) (img := img) (w := .w) (a := eng) o ha hr,hp]
    rfl
  let c2 := c1.goto 0x80001a0e
  let c3 := c2.wr 10 0xffffffff#32 0x80001a10
  have s1 : Quiet.Step B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    refine QuietDet.step_of (by change (0x80001a0a : Word).getLsbD 0 = false;decide) rs2147490314 fun o => ?_
    have hv : c1.get 10 = 0#32 := by
      change v = 0#32
      exact hb
    rw [exec_branch,hv,Core.get_zero]
    rfl
  have s2 : Quiet.Step B img ⟨c2,ram⟩ ⟨c3,ram⟩ := by
    refine QuietDet.step_of (by change (0x80001a0e : Word).getLsbD 0 = false;decide) rs2147490318 fun o => ?_
    rw [exec_opimm,Core.get_zero]
    simp only [alu,BitVec.zero_add]
    rfl
  have s3 : Quiet.Step B img ⟨c3,ram⟩ ⟨acquired c,result ram eng⟩ := by
    refine QuietDet.step_of (by change (0x80001a10 : Word).getLsbD 0 = false;decide) rs2147490320 fun o => ?_
    have hs : c3.get 9 = eng := by simp [c3,c2,c1,eng,Core.wr_get_ne]
    have hv : c3.get 10 = 0xffffffff#32 := by simp [c3,Core.wr_get]
    rw [exec_store,hs,hv,BitVec.add_zero,interp_store_ram (B := B) (img := img) (w := .w) (a := eng) (v := 0xffffffff#32) o ha hr]
    change Result.ok (c3.goto 0x80001a12) (result ram eng) [] = _
    congr 1
    change ((c.wr 10 v 0x80001a0a).wr 10 0xffffffff#32 0x80001a12) = c.wr 10 0xffffffff#32 0x80001a12
    simp [Core.wr,Core.set]
    funext i
    by_cases hi : i = 10 <;> simp [hi]
  exact .step s0 (.step s1 (.step s2 (.single s3)))

end E5R.Thermostat.ReadAcquire
