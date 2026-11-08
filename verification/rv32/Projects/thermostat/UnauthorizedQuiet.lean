-- Generated stronger trace proofs; Lean checks every decoded-instruction side condition.
import Projects.thermostat.Unauthorized
import Projects.thermostat.QuietDet
import Projects.thermostat.RamRunQuiet
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
open E5R E5R.Thermostat
namespace E5R.Thermostat.Unauthorized
theorem enter_quiet (B : Board) (c : Core) (ram : Word → BitVec 8) (kind : Fin 3)
    (hp : c.pc = entry kind) (hr : B.inRam (c.get 11) 1 = true) (ha : ram (c.get 11) = 0#8) :
    ∃ d, Quiet.Steps B img 2 ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc = 0x8000011c ∧
      (∀ r : Reg, r ≠ 11 → d.get r = c.get r) ∧ d.sameCsr c := by
  have hi := kind.isLt
  have hc : kind.val = 0 ∨ kind.val = 1 ∨ kind.val = 2 := by omega
  rcases hc with hkind|hkind|hkind
  · have hp' : c.pc = 0x800000d6 := by simpa [entry,hkind] using hp
    let c1 := c.wr 11 0#32 0x800000da
    let d := c1.goto 0x8000011c
    have s0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
      refine QuietDet.step_of (by rw [hp'];decide) (by rw [hp'];exact d2147483862) fun o => ?_
      rw [exec_load,BitVec.add_zero,interp_load_ram (B := B) (img := img) (w := .b) o (by simp only [Width.bytes,Nat.mod_one]) hr]
      rw [Memory.load_byte]
      dsimp only
      rw [ha,hp']
      rfl
    have s1 : Quiet.Step B img ⟨c1,ram⟩ ⟨d,ram⟩ := by
      refine QuietDet.step_of (by change (0x800000da : Word).getLsbD 0 = false;decide) d2147483866 fun o => ?_
      have hv : c1.get 11 = 0#32 := by simp [c1,Core.wr_get]
      rw [exec_branch,hv,Core.get_zero,ite_eq_left (by decide +kernel),jump_ok _ _ (by change (0x8000011c : Word).getLsbD 0 = false;decide)]
      rfl
    refine ⟨d,.step s0 (.single s1),rfl,?_,?_⟩
    · intro r h; simp [d,c1,Core.wr_get_ne,h]
    · exact (Core.sameCsr_goto _ _).trans (Core.sameCsr_wr _ _ _ _)
  · have hp' : c.pc = 0x800000fe := by simpa [entry,hkind] using hp
    let c1 := c.wr 11 0#32 0x80000102
    let d := c1.goto 0x8000011c
    have s0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
      refine QuietDet.step_of (by rw [hp'];decide) (by rw [hp'];exact d2147483902) fun o => ?_
      rw [exec_load,BitVec.add_zero,interp_load_ram (B := B) (img := img) (w := .b) o (by simp only [Width.bytes,Nat.mod_one]) hr]
      rw [Memory.load_byte]
      dsimp only
      rw [ha,hp']
      rfl
    have s1 : Quiet.Step B img ⟨c1,ram⟩ ⟨d,ram⟩ := by
      refine QuietDet.step_of (by change (0x80000102 : Word).getLsbD 0 = false;decide) d2147483906 fun o => ?_
      have hv : c1.get 11 = 0#32 := by simp [c1,Core.wr_get]
      rw [exec_branch,hv,Core.get_zero,ite_eq_left (by decide +kernel),jump_ok _ _ (by change (0x8000011c : Word).getLsbD 0 = false;decide)]
      rfl
    refine ⟨d,.step s0 (.single s1),rfl,?_,?_⟩
    · intro r h; simp [d,c1,Core.wr_get_ne,h]
    · exact (Core.sameCsr_goto _ _).trans (Core.sameCsr_wr _ _ _ _)
  · have hp' : c.pc = 0x80000078 := by simpa [entry,hkind] using hp
    let c1 := c.wr 11 0#32 0x8000007c
    let d := c1.goto 0x8000011c
    have s0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
      refine QuietDet.step_of (by rw [hp'];decide) (by rw [hp'];exact d2147483768) fun o => ?_
      rw [exec_load,BitVec.add_zero,interp_load_ram (B := B) (img := img) (w := .b) o (by simp only [Width.bytes,Nat.mod_one]) hr]
      rw [Memory.load_byte]
      dsimp only
      rw [ha,hp']
      rfl
    have s1 : Quiet.Step B img ⟨c1,ram⟩ ⟨d,ram⟩ := by
      refine QuietDet.step_of (by change (0x8000007c : Word).getLsbD 0 = false;decide) d2147483772 fun o => ?_
      have hv : c1.get 11 = 0#32 := by simp [c1,Core.wr_get]
      rw [exec_branch,hv,Core.get_zero,ite_eq_left (by decide +kernel),jump_ok _ _ (by change (0x8000011c : Word).getLsbD 0 = false;decide)]
      rfl
    refine ⟨d,.step s0 (.single s1),rfl,?_,?_⟩
    · intro r h; simp [d,c1,Core.wr_get_ne,h]
    · exact (Core.sameCsr_goto _ _).trans (Core.sameCsr_wr _ _ _ _)

end E5R.Thermostat.Unauthorized
