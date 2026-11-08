import Projects.thermostat.ResetFirstPollQuiet
import Projects.thermostat.MainHeaderFirstPoll
import Projects.thermostat.DetRunUnique
import Projects.thermostat.QuietPrefix
namespace E5R.Thermostat.MainHeaderResetQuiet
open E5R E5R.Thermostat

/-- Actual reset-to-first-receive prefix with an explicitly empty device-read
    log. Generated instruction-local Quiet proofs are stronger than the old
    Det certificate; endpoint uniqueness transfers the extended layout proof. -/
theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8)
    (hp : c.pc=0x80000000#32) (mpp : c.mpp=0 ∨ c.mpp=3) (stack : Memory.Block B 0x80ff0000#32 65536) :
    ∃ d after, Quiet.Steps B img 2550 ⟨c,ram⟩ ⟨d,after⟩ ∧ MainHeaderFirstPoll.Ready B d after := by
  obtain ⟨a,mid,quiet,_⟩ := FirstPoll.reset_contract_quiet B c ram hp mpp stack
  obtain ⟨d,after,det,ready⟩ := MainHeaderFirstPoll.reset_contract B c ram hp mpp stack
  have equal := DetRunUnique.steps quiet.det det
  rw [equal] at quiet
  exact ⟨d,after,quiet,ready⟩

theorem safe_contract (B : Board) (c : Core) (ram : Word → BitVec 8)
    (hp : c.pc=0x80000000#32) (mpp : c.mpp=0 ∨ c.mpp=3) (masked : c.mie_=false)
    (stack : Memory.Block B 0x80ff0000#32 65536) :
    ∃ d after, Quiet.Steps B img 2550 ⟨c,ram⟩ ⟨d,after⟩ ∧ Trace.Closed B img 2550 ⟨c,ram⟩ ⟨d,after⟩ ∧
      MainHeaderFirstPoll.Ready B d after ∧
      (∀ count e reads evs, count<2550 → Observed.Steps B img count ⟨c,ram⟩ e reads evs → reads=[] ∧ evs=[] ∧ ¬Escapes B img e) := by
  obtain ⟨d,after,trace,ready⟩ := contract B c ram hp mpp stack
  exact ⟨d,after,trace,Interrupt.close trace.det masked,ready,fun _ _ _ _ bound actual => QuietPrefix.safe trace masked bound actual⟩
end E5R.Thermostat.MainHeaderResetQuiet
