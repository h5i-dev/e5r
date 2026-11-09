import Projects.thermostat.Boot
import Projects.thermostat.QuietPrefix
import Projects.thermostat.DetRunUnique
set_option autoImplicit false
namespace E5R.Thermostat.PanicLoop
open E5R E5R.Thermostat

/-- Exact unchanged-ELF panic spin instructions, checked against image bytes. -/
theorem fence : fetchDecode img 0x8000085c#32=some (.fence,4#32) := by
  exact PackedFetch.fetchDecode_of _ (by decide) (by decide) (bits := 0x0100000f#32) (by decide +kernel) (by decide +kernel)
theorem back : fetchDecode img 0x80000860#32=some (.jal 0 0xfffffffc#32,2#32) := by
  exact PackedFetch.fetchDecode_of _ (by decide) (by decide) (bits := 0x0000bff5#32) (by decide +kernel) (by decide +kernel)

def At (c : Core) : Prop := c.pc=0x80000034#32 ∨ c.pc=0x8000085c#32 ∨ c.pc=0x80000860#32

theorem next {B c ram} (h : At c) : ∃ d,Quiet.Step B img ⟨c,ram⟩ ⟨d,ram⟩ ∧ At d := by
  rcases h with pc|pc|pc
  · refine ⟨c.goto 0x80000034#32,?_,Or.inl rfl⟩
    intro o
    rw [Observed.stepInstr_of (by rw [pc];decide) (by rw [pc];exact bt2147483700),exec_jal,Core.set_zero,pc]
    rw [show 0x80000034#32+0#32=0x80000034#32 by decide +kernel,jump_ok _ _ (by decide)]
    rfl
  · refine ⟨c.goto 0x80000860#32,?_,Or.inr (Or.inr rfl)⟩
    intro o
    rw [Observed.stepInstr_of (by rw [pc];decide) (by rw [pc];exact fence)]
    change Observed.interp B img o (.done (c.goto (c.pc+4#32))) ram 0 [] []=_
    rw [pc];rfl
  · refine ⟨c.goto 0x8000085c#32,?_,Or.inr (Or.inl rfl)⟩
    intro o
    rw [Observed.stepInstr_of (by rw [pc];decide) (by rw [pc];exact back),exec_jal,Core.set_zero,pc]
    rw [show 0x80000860#32+0xfffffffc#32=0x8000085c#32 by decide +kernel,jump_ok _ _ (by decide)]
    rfl

/-- Once at the actual spin, every quiet execution stays there. Thus a
    certificate reaching an actual UART cut cannot have passed this loop. -/
theorem quiet {B n m d} (h : At m.core) (trace : Quiet.Steps B img n m d) : At d.core := by
  induction trace with
  | refl => exact h
  | @step n m mid d first rest ih =>
    obtain ⟨e,step,post⟩ := next (B := B) (ram := m.ram) h
    have same := DetRunUnique.steps (Quiet.Steps.single first).det (Quiet.Steps.single step).det
    have coreEq := congrArg Machine.core same
    dsimp only at coreEq
    apply ih
    rw [coreEq]
    exact post
end E5R.Thermostat.PanicLoop
