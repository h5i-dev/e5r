import Projects.thermostat.MainCloseCode
import Projects.thermostat.QuietRam
set_option autoImplicit false
namespace E5R.Thermostat.MainCloseTrimFlow
open E5R E5R.Thermostat

theorem leftSetup (B : Board) (c : Core) (ram : Word → BitVec 8) (p length : Word)
    (hp : c.pc=0x800025b0#32) (h22 : c.get 22=p) (h23 : c.get 23=length) :
    ∃ d, Quiet.Steps B img 2 ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc=0x800025b4#32 ∧ d.get 15=p ∧ d.get 24=length ∧
      (∀ r : Reg, r≠15 → r≠24 → d.get r=c.get r) ∧ d.sameCsr c := by
  let a := c.wr 15 p 0x800025b2#32
  let d := a.wr 24 length 0x800025b4#32
  have sa : Quiet.Step B img ⟨c,ram⟩ ⟨a,ram⟩ := by
    refine Quiet.step_of (by rw [hp];decide) (by rw [hp];exact re2147493296) fun o => ?_
    change Observed.interp B img o (exec c _ _) ram 0 [] [] = ⟨.ok a ram [],[]⟩
    rw [exec_op,Core.get_zero,h22,hp];simp only [alu,show (0 : Word)=0#32 from rfl,BitVec.zero_add];rfl
  have sd : Quiet.Step B img ⟨a,ram⟩ ⟨d,ram⟩ := by
    refine Quiet.step_of (by change (0x800025b2#32).getLsbD 0=false;decide) re2147493298 fun o => ?_
    change Observed.interp B img o (exec a _ _) ram 0 [] [] = ⟨.ok d ram [],[]⟩
    have av : a.get 23=length := by simp [a,Core.wr_get,h23]
    rw [exec_op,Core.get_zero,av];simp only [alu,show (0 : Word)=0#32 from rfl,BitVec.zero_add];rfl
  refine ⟨d,.step sa (.single sd),rfl,?_,?_,?_,by rfl⟩
  · simp [d,a,Core.wr_get_ne,Core.wr_get]
  · simp [d,a,Core.wr_get_ne,Core.wr_get]
  · intro r n15 n24
    simp only [d,a,Core.wr_get_ne _ _ _ _ _ n24,Core.wr_get_ne _ _ _ _ _ n15]

theorem rightSetup (B : Board) (c : Core) (ram : Word → BitVec 8) (p length : Word)
    (hp : c.pc=0x800025e4#32) (h22 : c.get 22=p) (h23 : c.get 23=length) :
    ∃ d, Quiet.Steps B img 2 ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc=0x800025e8#32 ∧ d.get 22=(p+length)+0xffffffff#32 ∧
      (∀ r : Reg, r≠22 → d.get r=c.get r) ∧ d.sameCsr c := by
  let a := c.wr 22 (p+length) 0x800025e6#32
  let d := a.wr 22 ((p+length)+0xffffffff#32) 0x800025e8#32
  have sa : Quiet.Step B img ⟨c,ram⟩ ⟨a,ram⟩ := by
    refine Quiet.step_of (by rw [hp];decide) (by rw [hp];exact re2147493348) fun o => ?_
    change Observed.interp B img o (exec c _ _) ram 0 [] [] = ⟨.ok a ram [],[]⟩
    rw [exec_op,h22,h23,hp];rfl
  have sd : Quiet.Step B img ⟨a,ram⟩ ⟨d,ram⟩ := by
    refine Quiet.step_of (by change (0x800025e6#32).getLsbD 0=false;decide) re2147493350 fun o => ?_
    change Observed.interp B img o (exec a _ _) ram 0 [] [] = ⟨.ok d ram [],[]⟩
    have av : a.get 22=p+length := by simp [a,Core.wr_get]
    rw [exec_opimm,av];rfl
  refine ⟨d,.step sa (.single sd),rfl,?_,?_,by rfl⟩
  · simp [d,Core.wr_get]
  · intro r ne
    simp only [d,a,Core.wr_get_ne _ _ _ _ _ ne]
end E5R.Thermostat.MainCloseTrimFlow
