import Projects.thermostat.HttpParseCode
import Projects.thermostat.QuietRam
import Projects.thermostat.Usize
namespace E5R.Thermostat.HeadHeaderCapacity
open E5R E5R.Thermostat

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (count : Nat)
    (hp : c.pc=0x800030fa#32) (h9 : c.get 9=BitVec.ofNat 32 count) (bound : count≤16) :
    ∃ d, Quiet.Steps B img 2 ⟨c,ram⟩ ⟨d,ram⟩ ∧
      d.pc=(if 16≤count then 0x800034d4#32 else 0x80003100#32) ∧ d.get 10=15#32 ∧
      (∀ r : Reg, r≠10 → d.get r=c.get r) ∧ d.sameCsr c := by
  let c1 := c.wr 10 15#32 0x800030fc#32
  let d := c1.goto (if 16≤count then 0x800034d4#32 else 0x80003100#32)
  have constant : c1.get 10=15#32 := Core.wr_get_self _ _ _ _ (by decide)
  have input : c1.get 9=BitVec.ofNat 32 count := (Core.wr_get_ne _ _ _ _ _ (by decide)).trans h9
  have test : taken .ltu (15#32) (BitVec.ofNat 32 count)=decide (16≤count) := by
    change decide (15<(BitVec.ofNat 32 count).toNat)=decide (16≤count)
    rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq]
    omega
  have t0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine Quiet.step_of (by rw [hp];decide) (by rw [hp];exact hh2147496186) fun o => ?_
    change Observed.interp B img o (exec c _ _) ram 0 [] [] = ⟨.ok c1 ram [],[]⟩
    rw [exec_opimm,Core.get_zero,hp];rfl
  have t1 : Quiet.Step B img ⟨c1,ram⟩ ⟨d,ram⟩ := by
    refine Quiet.step_of (by change (0x800030fc#32).getLsbD 0=false;decide) hh2147496188 fun o => ?_
    change Observed.interp B img o (exec c1 _ _) ram 0 [] [] = ⟨.ok d ram [],[]⟩
    rw [exec_branch,constant,input,test]
    by_cases selected : 16≤count
    · simp [selected]
      change Observed.interp B img o (jump c1 (0x800030fc#32+0x3d8#32)) ram 0 [] [] = _
      rw [show 0x800030fc#32+0x3d8#32=0x800034d4#32 by decide +kernel,jump_ok _ _ (by decide)]
      simp only [d,selected,ite_true];rfl
    · simp [selected]
      change Observed.interp B img o (.done (c1.goto 0x80003100#32)) ram 0 [] [] = _
      simp only [d,selected,ite_false];rfl
  exact ⟨d,.step t0 (.single t1),rfl,constant,fun r h10 => Core.wr_get_ne _ _ _ _ _ h10,by rfl⟩
end E5R.Thermostat.HeadHeaderCapacity
