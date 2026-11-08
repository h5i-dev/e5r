import Projects.thermostat.QuietRam
namespace E5R.Thermostat.QuietBranch
open E5R

/-- A checked branch instruction certificate. Every register, CSR and RAM byte
    is preserved; both target alignment and actual decode are obligations. -/
theorem contract (B : Board) (img : List Segment) (c : Core) (ram : Word → BitVec 8)
    (pc len off : Word) (cond : BrCond) (rs1 rs2 : Reg) (test : Bool)
    (hp : c.pc=pc) (aligned : pc.getLsbD 0=false) (targetAligned : (pc+off).getLsbD 0=false)
    (fetched : fetchDecode img pc=some (.branch cond rs1 rs2 off,len))
    (tested : taken cond (c.get rs1) (c.get rs2)=test) :
    ∃ d, Quiet.Steps B img 1 ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc=(if test then pc+off else pc+len) ∧
      (∀ r : Reg, d.get r=c.get r) ∧ d.sameCsr c := by
  let d := c.goto (if test then pc+off else pc+len)
  have t : Quiet.Step B img ⟨c,ram⟩ ⟨d,ram⟩ := by
    refine Quiet.step_of (by rw [hp];exact aligned) (by rw [hp];exact fetched) fun o => ?_
    rw [exec_branch,tested,hp]
    cases test with
    | false => rfl
    | true => rw [jump_ok _ _ targetAligned];rfl
  exact ⟨d,.single t,rfl,fun _ => rfl,rfl⟩
end E5R.Thermostat.QuietBranch
