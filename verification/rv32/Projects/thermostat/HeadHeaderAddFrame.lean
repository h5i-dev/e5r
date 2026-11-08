import Projects.thermostat.HeadHeaderMemoryFrame
import Projects.thermostat.HeadHeaderCommit
namespace E5R.Thermostat.HeadHeaderAddFrame
open E5R E5R.Thermostat HttpRequestSpec

def At (before after : Word → BitVec 8) (sp : Word) : Prop :=
  ∀ off len : Nat, off+len≤4294967296 → (4≤off ∧ off+len≤56 ∨ 327≤off) →
    ViewFrame.Region before after (sp+BitVec.ofNat 32 off) len

theorem of_decision {before after sp} (h : HeadHeaderMemoryFrame.At before after sp) : At before after sp := by
  intro off len bound outside
  exact h off len bound (by omega) (by omega)

theorem commit {before mid : Word → BitVec 8} {sp : Word}
    (h : HeadHeaderMemoryFrame.At before mid sp) (count : Nat) (entry : Field) (room : count<16) :
    At before (HeadHeaderCommitMemory.memory mid sp count entry) sp := by
  intro off len bound outside i
  have stored := HeadHeaderCommitMemory.region mid sp count entry off len room bound (by omega) (by omega)
  exact (stored i).trans (h off len bound (by omega) (by omega) i)
end E5R.Thermostat.HeadHeaderAddFrame
