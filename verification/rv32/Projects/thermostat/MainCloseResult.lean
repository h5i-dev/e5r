import Projects.thermostat.MainCloseCode
import Projects.thermostat.QuietRam
set_option autoImplicit false
namespace E5R.Thermostat.MainCloseResult
open E5R E5R.Thermostat

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (answer : Bool)
    (hp : c.pc=(if answer then 0x800026bc#32 else 0x8000267c#32)) :
    ∃ n d, n≤2 ∧ Quiet.Steps B img n ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc=0x8000267e#32 ∧
      d.get 10=(if answer then 1#32 else 0#32) ∧ (∀ r : Reg, r≠10 → d.get r=c.get r) ∧ d.sameCsr c := by
  cases answer with
  | false =>
    have pc : c.pc=0x8000267c#32 := hp
    let d := c.wr 10 0#32 0x8000267e#32
    have step : Quiet.Step B img ⟨c,ram⟩ ⟨d,ram⟩ := by
      refine Quiet.step_of (by rw [pc];decide) (by rw [pc];exact re2147493500) fun o => ?_
      change Observed.interp B img o (exec c _ _) ram 0 [] []=⟨.ok d ram [],[]⟩
      rw [exec_opimm,Core.get_zero,pc];rfl
    refine ⟨1,d,by decide,.single step,rfl,?_,?_,by rfl⟩
    · simp [d,Core.wr_get]
    · intro r n10;simp [d,Core.wr_get_ne,n10]
  | true =>
    have pc : c.pc=0x800026bc#32 := hp
    let a := c.wr 10 1#32 0x800026be#32
    let d := a.goto 0x8000267e#32
    have step : Quiet.Step B img ⟨c,ram⟩ ⟨a,ram⟩ := by
      refine Quiet.step_of (by rw [pc];decide) (by rw [pc];exact re2147493564) fun o => ?_
      change Observed.interp B img o (exec c _ _) ram 0 [] []=⟨.ok a ram [],[]⟩
      rw [exec_opimm,Core.get_zero,pc];rfl
    have branch : Quiet.Step B img ⟨a,ram⟩ ⟨d,ram⟩ := by
      refine Quiet.step_of (by change (0x800026be#32).getLsbD 0=false;decide) re2147493566 fun o => ?_
      change Observed.interp B img o (exec a _ _) ram 0 [] []=⟨.ok d ram [],[]⟩
      rw [exec_jal]
      change Observed.interp B img o (jump a (0x800026be#32+0xffffffc0#32)) ram 0 [] []=_
      rw [show 0x800026be#32+0xffffffc0#32=0x8000267e#32 by decide +kernel,jump_ok _ _ (by decide)];rfl
    refine ⟨2,d,by decide,.step step (.single branch),rfl,?_,?_,by rfl⟩
    · simp [d,a,Core.wr_get]
    · intro r n10;simp [d,a,Core.wr_get_ne,n10]
end E5R.Thermostat.MainCloseResult
