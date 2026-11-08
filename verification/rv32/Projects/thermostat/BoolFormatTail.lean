import Projects.thermostat.BoolFormatCode
import Projects.thermostat.FormatLiterals
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.BoolFormatTail
open E5R E5R.Thermostat

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (b : Bool)
    (hp : c.pc = (if b then 0x8000511a#32 else 0x8000512c#32)) :
    ∃ d, DetSteps B img 5 ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc = 0x80004790#32 ∧
      d.get 11 = FormatLiterals.boolPointer b ∧ d.get 12 = BitVec.ofNat 32 (ReplyJson.boolean b).length ∧
      (∀ r : Reg, r ≠ 6 → r ≠ 11 → r ≠ 12 → d.get r = c.get r) ∧ d.sameCsr c := by
  cases b with
  | false =>
    change c.pc = 0x8000512c#32 at hp
    let c1 := c.wr 11 0x80006000#32 0x80005130#32
    let c2 := c1.wr 11 0x80005efb#32 0x80005134#32
    let c3 := c2.wr 12 5#32 0x80005136#32
    let c4 := c3.wr 6 0x80004136#32 0x8000513a#32
    let d := c4.goto 0x80004790#32
    have s0 : DetStep B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
      refine detStep_of (by rw [hp];decide) (by rw [hp];exact bf2147504428) fun o => ?_
      rw [exec_lui,hp];rfl
    have s1 : DetStep B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
      refine detStep_of (by change (0x80005130#32).getLsbD 0 = false;decide) bf2147504432 fun o => ?_
      have hv : c1.get 11 = 0x80006000#32 := by simp [c1,Core.wr_get]
      rw [exec_opimm,hv];rfl
    have s2 : DetStep B img ⟨c2,ram⟩ ⟨c3,ram⟩ := by
      refine detStep_of (by change (0x80005134#32).getLsbD 0 = false;decide) bf2147504436 fun o => ?_
      rw [exec_opimm,Core.get_zero];rfl
    have s3 : DetStep B img ⟨c3,ram⟩ ⟨c4,ram⟩ := by
      refine detStep_of (by change (0x80005136#32).getLsbD 0 = false;decide) bf2147504438 fun o => ?_
      rw [exec_auipc]
      change interp B img o (.done (c3.wr 6 (0x80005136#32+0xfffff000#32) 0x8000513a#32)) ram 0 [] = _
      rw [show 0x80005136#32+0xfffff000#32 = 0x80004136#32 by decide +kernel];rfl
    have s4 : DetStep B img ⟨c4,ram⟩ ⟨d,ram⟩ := by
      refine detStep_of (by change (0x8000513a#32).getLsbD 0 = false;decide) bf2147504442 fun o => ?_
      have hv : c4.get 6 = 0x80004136#32 := by simp [c4,Core.wr_get]
      rw [exec_jalr,hv]
      change interp B img o (jump c4 ((0x80004136#32+0x0000065a#32) &&& ~~~1)) ram 0 [] = _
      rw [show (0x80004136#32+0x0000065a#32) &&& ~~~1 = 0x80004790#32 by decide +kernel,jump_ok _ _ (by decide)];rfl
    refine ⟨d,.step s0 (.step s1 (.step s2 (.step s3 (.single s4)))),rfl,?_,?_,?_,by rfl⟩
    · change d.get 11 = 0x80005efb#32
      simp [d,c4,c3,c2,Core.wr_get_ne,Core.wr_get]
    · change d.get 12 = 5#32
      simp [d,c4,c3,Core.wr_get_ne,Core.wr_get]
    · intro r h6 h11 h12
      simp [d,c4,c3,c2,c1,Core.wr_get_ne,h6,h11,h12]
  | true =>
    change c.pc = 0x8000511a#32 at hp
    let c1 := c.wr 11 0x80006000#32 0x8000511e#32
    let c2 := c1.wr 11 0x80005bfc#32 0x80005122#32
    let c3 := c2.wr 12 4#32 0x80005124#32
    let c4 := c3.wr 6 0x80004124#32 0x80005128#32
    let d := c4.goto 0x80004790#32
    have s0 : DetStep B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
      refine detStep_of (by rw [hp];decide) (by rw [hp];exact bf2147504410) fun o => ?_
      rw [exec_lui,hp];rfl
    have s1 : DetStep B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
      refine detStep_of (by change (0x8000511e#32).getLsbD 0 = false;decide) bf2147504414 fun o => ?_
      have hv : c1.get 11 = 0x80006000#32 := by simp [c1,Core.wr_get]
      rw [exec_opimm,hv];rfl
    have s2 : DetStep B img ⟨c2,ram⟩ ⟨c3,ram⟩ := by
      refine detStep_of (by change (0x80005122#32).getLsbD 0 = false;decide) bf2147504418 fun o => ?_
      rw [exec_opimm,Core.get_zero];rfl
    have s3 : DetStep B img ⟨c3,ram⟩ ⟨c4,ram⟩ := by
      refine detStep_of (by change (0x80005124#32).getLsbD 0 = false;decide) bf2147504420 fun o => ?_
      rw [exec_auipc]
      change interp B img o (.done (c3.wr 6 (0x80005124#32+0xfffff000#32) 0x80005128#32)) ram 0 [] = _
      rw [show 0x80005124#32+0xfffff000#32 = 0x80004124#32 by decide +kernel];rfl
    have s4 : DetStep B img ⟨c4,ram⟩ ⟨d,ram⟩ := by
      refine detStep_of (by change (0x80005128#32).getLsbD 0 = false;decide) bf2147504424 fun o => ?_
      have hv : c4.get 6 = 0x80004124#32 := by simp [c4,Core.wr_get]
      rw [exec_jalr,hv]
      change interp B img o (jump c4 ((0x80004124#32+0x0000066c#32) &&& ~~~1)) ram 0 [] = _
      rw [show (0x80004124#32+0x0000066c#32) &&& ~~~1 = 0x80004790#32 by decide +kernel,jump_ok _ _ (by decide)];rfl
    refine ⟨d,.step s0 (.step s1 (.step s2 (.step s3 (.single s4)))),rfl,?_,?_,?_,by rfl⟩
    · change d.get 11 = 0x80005bfc#32
      simp [d,c4,c3,c2,Core.wr_get_ne,Core.wr_get]
    · change d.get 12 = 4#32
      simp [d,c4,c3,Core.wr_get_ne,Core.wr_get]
    · intro r h6 h11 h12
      simp [d,c4,c3,c2,c1,Core.wr_get_ne,h6,h11,h12]
end E5R.Thermostat.BoolFormatTail
