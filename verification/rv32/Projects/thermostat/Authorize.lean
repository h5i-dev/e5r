import Projects.thermostat.Unauthorized
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
namespace E5R.Thermostat.Authorize
open E5R E5R.Thermostat

def next (kind : Fin 3) : Word := match kind.val with
 | 0 => 0x800000dc | 1 => 0x80000104 | _ => 0x8000007e

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (kind : Fin 3)
    (hp : c.pc = Unauthorized.entry kind) (hr : B.inRam (c.get 11) 1 = true) (ha : ram (c.get 11) = 1#8) :
    ∃ d, DetSteps B img 2 ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc = next kind ∧
      (∀ r : Reg, r ≠ 11 → d.get r = c.get r) ∧ d.sameCsr c := by
  have hi := kind.isLt
  have hc : kind.val = 0 ∨ kind.val = 1 ∨ kind.val = 2 := by omega
  rcases hc with hkind|hkind|hkind
  · have hp' : c.pc = 0x800000d6 := by simpa [Unauthorized.entry,hkind] using hp
    let c1 := c.wr 11 1#32 0x800000da
    let d := c1.goto 0x800000dc
    have s0 : DetStep B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
      refine detStep_of (by rw [hp'];decide) (by rw [hp'];exact d2147483862) fun o => ?_
      rw [exec_load,BitVec.add_zero,interp_load_ram (B := B) (img := img) (w := .b) o (by simp only [Width.bytes,Nat.mod_one]) hr]
      rw [Memory.load_byte]
      dsimp only
      rw [ha,hp']
      rfl
    have s1 : DetStep B img ⟨c1,ram⟩ ⟨d,ram⟩ := by
      refine detStep_of (by change (0x800000da : Word).getLsbD 0 = false;decide) d2147483866 fun o => ?_
      have hv : c1.get 11 = 1#32 := by simp [c1,Core.wr_get]
      rw [exec_branch,hv,Core.get_zero,ite_eq_right (by decide +kernel)]
      rfl
    refine ⟨d,.step s0 (.single s1),?_,?_,?_⟩
    · simp [d,next,hkind]
    · intro r h; simp [d,c1,Core.wr_get_ne,h]
    · exact (Core.sameCsr_goto _ _).trans (Core.sameCsr_wr _ _ _ _)
  · have hp' : c.pc = 0x800000fe := by simpa [Unauthorized.entry,hkind] using hp
    let c1 := c.wr 11 1#32 0x80000102
    let d := c1.goto 0x80000104
    have s0 : DetStep B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
      refine detStep_of (by rw [hp'];decide) (by rw [hp'];exact d2147483902) fun o => ?_
      rw [exec_load,BitVec.add_zero,interp_load_ram (B := B) (img := img) (w := .b) o (by simp only [Width.bytes,Nat.mod_one]) hr]
      rw [Memory.load_byte]
      dsimp only
      rw [ha,hp']
      rfl
    have s1 : DetStep B img ⟨c1,ram⟩ ⟨d,ram⟩ := by
      refine detStep_of (by change (0x80000102 : Word).getLsbD 0 = false;decide) d2147483906 fun o => ?_
      have hv : c1.get 11 = 1#32 := by simp [c1,Core.wr_get]
      rw [exec_branch,hv,Core.get_zero,ite_eq_right (by decide +kernel)]
      rfl
    refine ⟨d,.step s0 (.single s1),?_,?_,?_⟩
    · simp [d,next,hkind]
    · intro r h; simp [d,c1,Core.wr_get_ne,h]
    · exact (Core.sameCsr_goto _ _).trans (Core.sameCsr_wr _ _ _ _)
  · have hp' : c.pc = 0x80000078 := by simpa [Unauthorized.entry,hkind] using hp
    let c1 := c.wr 11 1#32 0x8000007c
    let d := c1.goto 0x8000007e
    have s0 : DetStep B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
      refine detStep_of (by rw [hp'];decide) (by rw [hp'];exact d2147483768) fun o => ?_
      rw [exec_load,BitVec.add_zero,interp_load_ram (B := B) (img := img) (w := .b) o (by simp only [Width.bytes,Nat.mod_one]) hr]
      rw [Memory.load_byte]
      dsimp only
      rw [ha,hp']
      rfl
    have s1 : DetStep B img ⟨c1,ram⟩ ⟨d,ram⟩ := by
      refine detStep_of (by change (0x8000007c : Word).getLsbD 0 = false;decide) d2147483772 fun o => ?_
      have hv : c1.get 11 = 1#32 := by simp [c1,Core.wr_get]
      rw [exec_branch,hv,Core.get_zero,ite_eq_right (by decide +kernel)]
      rfl
    refine ⟨d,.step s0 (.single s1),?_,?_,?_⟩
    · simp [d,next,hkind]
    · intro r h; simp [d,c1,Core.wr_get_ne,h]
    · exact (Core.sameCsr_goto _ _).trans (Core.sameCsr_wr _ _ _ _)


end E5R.Thermostat.Authorize
