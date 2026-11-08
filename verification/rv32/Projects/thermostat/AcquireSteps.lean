import Projects.thermostat.AcquireCode
import Projects.thermostat.Memory
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.AcquireSteps
open E5R E5R.Thermostat

theorem load (B : Board) (c : Core) (ram : Word → BitVec 8)
    (hp : c.pc = 0x80000614) (ha : (c.get 23).toNat % 4 = 0)
    (hr : B.inRam (c.get 23) 4 = true) :
    DetStep B img ⟨c,ram⟩ ⟨c.wr 10 (ramRead ram (c.get 23) .w) 0x80000618,ram⟩ := by
  refine detStep_of (by rw [hp];decide) (by rw [hp];exact ac2147485204) fun o => ?_
  rw [exec_load,BitVec.add_zero,interp_load_ram (B := B) (img := img) (w := .w) o ha hr,hp]
  rfl

theorem free (B : Board) (c : Core) (ram : Word → BitVec 8)
    (hp : c.pc = 0x80000618) (hv : c.get 10 = 0#32) :
    DetStep B img ⟨c,ram⟩ ⟨c.goto 0x8000061c,ram⟩ := by
  refine detStep_of (by rw [hp];decide) (by rw [hp];exact ac2147485208) fun o => ?_
  rw [exec_branch,hv,Core.get_zero,hp]
  rfl

theorem fail (B : Board) (c : Core) (ram : Word → BitVec 8)
    (hp : c.pc = 0x80000618) (hv : c.get 10 ≠ 0#32) :
    DetStep B img ⟨c,ram⟩ ⟨c.goto 0x80000766,ram⟩ := by
  refine detStep_of (by rw [hp];decide) (by rw [hp];exact ac2147485208) fun o => ?_
  rw [exec_branch,Core.get_zero,hp]
  have ht : taken .ne (c.get 10) 0 = true := by simp [taken,hv]
  rw [ht]
  rfl

theorem minusOne (B : Board) (c : Core) (ram : Word → BitVec 8)
    (hp : c.pc = 0x8000061c) :
    DetStep B img ⟨c,ram⟩ ⟨c.wr 10 0xffffffff#32 0x8000061e,ram⟩ := by
  refine detStep_of (by rw [hp];decide) (by rw [hp];exact ac2147485212) fun o => ?_
  rw [exec_opimm,hp,Core.get_zero]
  simp only [alu,BitVec.zero_add]
  rfl

theorem store (B : Board) (c : Core) (ram : Word → BitVec 8)
    (hp : c.pc = 0x8000061e) (hv : c.get 10 = 0xffffffff#32)
    (ha : (c.get 23).toNat % 4 = 0) (hr : B.inRam (c.get 23) 4 = true) :
    DetStep B img ⟨c,ram⟩ ⟨c.goto 0x80000622,ramWrite ram (c.get 23) 0xffffffff#32 .w⟩ := by
  refine detStep_of (by rw [hp];decide) (by rw [hp];exact ac2147485214) fun o => ?_
  rw [exec_store,hv,BitVec.add_zero,interp_store_ram (B := B) (img := img) (w := .w) o ha hr,hp]
  rfl
end E5R.Thermostat.AcquireSteps
