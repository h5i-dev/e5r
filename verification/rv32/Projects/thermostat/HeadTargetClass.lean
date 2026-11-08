import Projects.thermostat.HttpParseCode
import Projects.thermostat.HttpRequestSpec
import Projects.thermostat.Quiet
namespace E5R.Thermostat.HeadTargetClass
open E5R E5R.Thermostat HttpRequestSpec

theorem byte_test : ∀ byte : BitVec 8,
    taken .geu (BitVec.ofNat 32 byte.toNat+0xffffffdf#32) 94#32= !isTargetByte byte.toNat := by decide +kernel

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (byte : BitVec 8)
    (hp : c.pc=0x80002df0#32) (h21 : c.get 21=BitVec.ofNat 32 byte.toNat+0xffffffdf#32) (h19 : c.get 19=94#32) :
    ∃ d, Quiet.Steps B img 1 ⟨c,ram⟩ ⟨d,ram⟩ ∧
      d.pc=(if isTargetByte byte.toNat then 0x80002df4#32 else 0x80002dfe#32) ∧
      (∀ r : Reg, d.get r=c.get r) ∧ d.sameCsr c := by
  let d := c.goto (if isTargetByte byte.toNat then 0x80002df4#32 else 0x80002dfe#32)
  have t : Quiet.Step B img ⟨c,ram⟩ ⟨d,ram⟩ := by
    refine Quiet.step_of (by rw [hp];decide) (by rw [hp];exact hh2147495408) fun o => ?_
    rw [exec_branch,h21,h19,byte_test,hp]
    cases h : isTargetByte byte.toNat with
    | true => simp only [d,h,Bool.not_true,Bool.false_eq_true,ite_false];rfl
    | false =>
      simp only [d,h,Bool.not_false,Bool.false_eq_true,ite_false,ite_true]
      rw [show 0x80002df0#32+14#32=0x80002dfe#32 by decide +kernel,jump_ok _ _ (by decide)]
      rfl
  exact ⟨d,.single t,rfl,fun _ => rfl,rfl⟩
end E5R.Thermostat.HeadTargetClass
