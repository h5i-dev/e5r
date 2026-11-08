import Projects.thermostat.HttpParseCode00
import Projects.thermostat.Quiet
namespace E5R.Thermostat.HeadIncompleteBranch
open E5R E5R.Thermostat

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (length : Nat) (hlen : length≤2048)
    (hp : c.pc=0x80002ce6#32) (h12 : c.get 12=BitVec.ofNat 32 length) (h16 : c.get 16=1024#32) :
    ∃ d, Quiet.Steps B img 1 ⟨c,ram⟩ ⟨d,ram⟩ ∧
      d.pc=(if 1024≤length then 0x80002d52#32 else 0x80002cea#32) ∧
      (∀ r : Reg, d.get r=c.get r) ∧ d.sameCsr c := by
  let d := c.goto (if 1024≤length then 0x80002d52#32 else 0x80002cea#32)
  have test : taken .geu (BitVec.ofNat 32 length) 1024#32=decide (1024≤length) := by
    have bound : length<2^32 := by omega
    by_cases full : 1024≤length
    · have noLT : ¬length<1024 := by omega
      simp [taken,BitVec.ult,BitVec.toNat_ofNat,Nat.mod_eq_of_lt bound,full,noLT]
    · have lt : length<1024 := by omega
      simp [taken,BitVec.ult,BitVec.toNat_ofNat,Nat.mod_eq_of_lt bound,full,lt]
  have t : Quiet.Step B img ⟨c,ram⟩ ⟨d,ram⟩ := by
    refine Quiet.step_of (by rw [hp];decide) (by rw [hp];exact hh2147495142) fun o => ?_
    rw [exec_branch,h12,h16,test,hp]
    by_cases full : 1024≤length
    · simp only [d,full,decide_true,ite_true]
      rw [show 0x80002ce6#32+0x6c#32=0x80002d52#32 by decide +kernel,jump_ok _ _ (by decide)]
      rfl
    · simp only [d,full,decide_false,Bool.false_eq_true,ite_false]
      rfl
  exact ⟨d,.single t,rfl,fun _ => rfl,rfl⟩
end E5R.Thermostat.HeadIncompleteBranch
