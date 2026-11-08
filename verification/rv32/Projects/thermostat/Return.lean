import Projects.thermostat.Wrapper
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.Return
open E5R E5R.Thermostat

/-- The same real wrapper epilogue, with any saved return address. -/
theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (ret : Word)
    (hp : c.pc = 0x80001e32) (hr : B.inRam (c.get 2+12#32) 4 = true)
    (ha : (c.get 2+12#32).toNat % 4 = 0)
    (hv : ramRead ram (c.get 2+12#32) .w = ret) :
    ∃ d, DetSteps B img 3 ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc = ret &&& ~~~1 ∧
      d.get 2 = c.get 2+16#32 ∧
      (∀ r : Reg, r ≠ 1 → r ≠ 2 → d.get r = c.get r) ∧ d.sameCsr c := by
  let c1 := c.wr 1 ret 0x80001e34
  let c2 := c1.wr 2 (c.get 2+16#32) 0x80001e36
  let d := c2.goto (ret &&& ~~~1)
  have h0 : DetStep B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine detStep_of (by rw [hp];decide) (by rw [hp];exact s2147491378) fun o => ?_
    rw [exec_load,interp_load_ram (B := B) (img := img) (w := .w) (a := c.get 2+12#32) o ha hr,hv,hp]
    rfl
  have h1 : DetStep B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    refine detStep_of (by change (0x80001e34 : Word).getLsbD 0 = false;decide) s2147491380 fun o => ?_
    have hs : c1.get 2 = c.get 2 := by simp [c1,Core.wr_get_ne]
    rw [exec_opimm,hs]
    rfl
  have h2 : DetStep B img ⟨c2,ram⟩ ⟨d,ram⟩ := by
    refine detStep_of (by change (0x80001e36 : Word).getLsbD 0 = false;decide) s2147491382 fun o => ?_
    have hr1 : c2.get 1 = ret := by simp [c2,c1,Core.wr_get,Core.wr_get_ne]
    rw [exec_jalr,hr1,BitVec.add_zero,jump_ok _ _ (clear_bit0 _)]
    rfl
  refine ⟨d,.step h0 (.step h1 (.single h2)),rfl,?_,?_,by rfl⟩
  · simp [d,c2,Core.wr_get]
  · intro r h1' h2'
    simp [d,c2,c1,Core.wr_get_ne,h1',h2']
end E5R.Thermostat.Return
