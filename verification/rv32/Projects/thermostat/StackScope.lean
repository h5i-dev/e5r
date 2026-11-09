import Projects.thermostat.CutBounds
import Projects.thermostat.MainInitWitness
import Projects.thermostat.Blocking
import Projects.thermostat.ResetBootQuiet
set_option autoImplicit false
-- Match the existing ResetBootQuiet kernel recursion setting.
set_option maxRecDepth 3000
namespace E5R.Thermostat.StackScope
open E5R E5R.Thermostat
abbrev B := UartPlatform.board

def InStack (c : Core) : Prop := 0x80ff0000≤(c.get 2).toNat ∧ (c.get 2).toNat≤0x81000000

def initial : Machine := ⟨MainInitWitness.core,MainInitWitness.ram⟩

theorem reset_valid : FirmwareStream.Reset initial :=
  ⟨rfl,rfl,Or.inr rfl,Blocking.stack_available⟩

/-- Concrete non-vacuity and an actual architectural reset prefix. AUIPC
    temporarily sets SP eight bytes above its final top before the next ADDI;
    these instructions perform no RAM/MMIO accesses. -/
theorem boot_prefix : ∃ m,Quiet.Steps B img 3 initial m ∧ m.core.pc=0x8000000c#32 ∧
    m.core.get 2=0x81000008#32 ∧ ¬InStack m.core := by
  let core := Boot.masked MainInitWitness.core
  let next := core.wr 2 0x81000008#32 0x8000000c#32
  have mask := Boot.mask_quiet B MainInitWitness.core MainInitWitness.ram rfl (Or.inr rfl)
  have init : Quiet.Step B img ⟨core,MainInitWitness.ram⟩ ⟨next,MainInitWitness.ram⟩ := by
    refine QuietDet.step_of (by change (0x80000008#32).getLsbD 0=false;decide) bt2147483656 fun o => ?_
    have pc : core.pc=0x80000008#32 := rfl
    rw [exec_auipc,pc]
    rw [show (0x80000008#32)+0x01000000#32=0x81000008#32 by decide +kernel]
    rfl
  refine ⟨⟨next,MainInitWitness.ram⟩,mask.trans (.single init),rfl,?_,?_⟩
  · exact Core.wr_get_self _ _ _ _ (by decide)
  · change ¬(0x80ff0000≤(next.get 2).toNat ∧ (next.get 2).toNat≤0x81000000)
    rw [Core.wr_get_self _ _ _ _ (by decide)]
    decide +kernel

theorem unconditional_sp_bound_false : ¬(∀ m,E5R.Reach B img FirmwareStream.Reset m [] → InStack m.core) := by
  intro bound
  obtain ⟨m,quiet,pc,sp,outside⟩ := boot_prefix
  have reached := quiet.observed.reach (Observed.Reach.init reset_valid)
  have actual : E5R.Reach B img FirmwareStream.Reset m [] := Observed.reach_erase reached
  exact outside (bound m actual)

/-- At all actual reusable UART cuts, both concrete stack pointers are
    within the allocated64KiB arena. Intermediate use is a separate claim. -/
theorem active {m g} (h : FirmwareStream.At m g) : InStack m.core := by
  rcases CutBounds.active_sp h with sp|sp
  all_goals unfold InStack;rw [sp];decide +kernel
end E5R.Thermostat.StackScope
