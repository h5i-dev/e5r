import Projects.thermostat.HttpParseCode
import Projects.thermostat.QuietRam
import Projects.thermostat.Usize
namespace E5R.Thermostat.HeadHeaderWidth
open E5R E5R.Thermostat

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (length : Nat)
    (hp : c.pc=0x80003100#32) (h14 : c.get 14=BitVec.ofNat 32 length) (bound : length≤2048) :
    ∃ d, Quiet.Steps B img 2 ⟨c,ram⟩ ⟨d,ram⟩ ∧
      d.pc=(if length≠4 then 0x80003192#32 else 0x80003106#32) ∧ d.get 10=4#32 ∧
      (∀ r : Reg, r≠10 → d.get r=c.get r) ∧ d.sameCsr c := by
  let c1 := c.wr 10 4#32 0x80003102#32
  let d := c1.goto (if length≠4 then 0x80003192#32 else 0x80003106#32)
  have constant : c1.get 10=4#32 := Core.wr_get_self _ _ _ _ (by decide)
  have input : c1.get 14=BitVec.ofNat 32 length := (Core.wr_get_ne _ _ _ _ _ (by decide)).trans h14
  have test : taken .ne (BitVec.ofNat 32 length) (4#32)=decide (length≠4) := by
    exact Usize.ne length 4 (by omega) (by decide)
  have t0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine Quiet.step_of (by rw [hp];decide) (by rw [hp];exact hh2147496192) fun o => ?_
    change Observed.interp B img o (exec c _ _) ram 0 [] [] = ⟨.ok c1 ram [],[]⟩
    rw [exec_opimm,Core.get_zero,hp];rfl
  have t1 : Quiet.Step B img ⟨c1,ram⟩ ⟨d,ram⟩ := by
    refine Quiet.step_of (by change (0x80003102#32).getLsbD 0=false;decide) hh2147496194 fun o => ?_
    change Observed.interp B img o (exec c1 _ _) ram 0 [] [] = ⟨.ok d ram [],[]⟩
    rw [exec_branch,input,constant,test]
    by_cases selected : length≠4
    · simp [selected]
      change Observed.interp B img o (jump c1 (0x80003102#32+0x90#32)) ram 0 [] [] = _
      rw [show 0x80003102#32+0x90#32=0x80003192#32 by decide +kernel,jump_ok _ _ (by decide)]
      simp [d,selected];rfl
    · simp [selected]
      change Observed.interp B img o (.done (c1.goto 0x80003106#32)) ram 0 [] [] = _
      simp [d,selected];rfl
  exact ⟨d,.step t0 (.single t1),rfl,constant,fun r h10 => Core.wr_get_ne _ _ _ _ _ h10,by rfl⟩
end E5R.Thermostat.HeadHeaderWidth
