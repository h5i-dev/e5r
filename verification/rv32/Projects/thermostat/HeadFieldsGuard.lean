import Projects.thermostat.HttpParseCode
import Projects.thermostat.QuietRam
import Projects.thermostat.Memory
import Projects.thermostat.HeadTargetMath
namespace E5R.Thermostat.HeadFieldsGuard
open E5R E5R.Thermostat

/-- Actual first header-position computation and capacity branch. -/
theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (sp : Word) (j cap : Nat)
    (hp : c.pc=0x80002f1e#32) (h2 : c.get 2=sp) (h9 : c.get 9=BitVec.ofNat 32 j)
    (hcap : ramRead ram (sp+40#32) .w=BitVec.ofNat 32 cap)
    (hm : Memory.Block B sp 56) (ha : sp.toNat%4=0) (hj : j≤1024) (hn : cap≤1024) :
    ∃ d, Quiet.Steps B img 3 ⟨c,ram⟩ ⟨d,ram⟩ ∧
      d.pc=(if cap≤j+2 then 0x800033ea#32 else 0x80002f28#32) ∧
      d.get 24=BitVec.ofNat 32 (j+2) ∧ d.get 10=BitVec.ofNat 32 cap ∧
      (∀ r : Reg, r≠24 → r≠10 → d.get r=c.get r) ∧ d.sameCsr c := by
  let a := c.wr 24 (BitVec.ofNat 32 (j+2)) 0x80002f22#32
  let b := a.wr 10 (BitVec.ofNat 32 cap) 0x80002f24#32
  let d := b.goto (if cap≤j+2 then 0x800033ea#32 else 0x80002f28#32)
  have s0 : Quiet.Step B img ⟨c,ram⟩ ⟨a,ram⟩ := by
    refine Quiet.step_of (by rw [hp];decide) (by rw [hp];exact hh2147495710) fun o => ?_
    rw [exec_opimm,h9,hp]
    rw [show alu .add (BitVec.ofNat 32 j) 2#32=BitVec.ofNat 32 (j+2) from (BitVec.ofNat_add j 2).symm]
    rfl
  have s1 : Quiet.Step B img ⟨a,ram⟩ ⟨b,ram⟩ := by
    refine Quiet.step_of (by change (0x80002f22#32).getLsbD 0=false;decide) hh2147495714 fun o => ?_
    have p2 : a.get 2=sp := by simp [a,Core.wr_get_ne,h2]
    rw [exec_load,p2,Quiet.interp_load_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 10 ha)
      (Memory.block_access hm (off := 40) (by decide) (by decide)),hcap]
    rfl
  have s2 : Quiet.Step B img ⟨b,ram⟩ ⟨d,ram⟩ := by
    refine Quiet.step_of (by change (0x80002f24#32).getLsbD 0=false;decide) hh2147495716 fun o => ?_
    have i24 : b.get 24=BitVec.ofNat 32 (j+2) := by simp [b,a,Core.wr_get_ne,Core.wr_get]
    have i10 : b.get 10=BitVec.ofNat 32 cap := by simp [b,Core.wr_get]
    rw [exec_branch,i24,i10,HeadTargetMath.geu (j+2) cap (by omega) (by omega)]
    by_cases full : cap≤j+2
    · simp only [full,decide_true,ite_true]
      change Observed.interp B img o (jump b (0x80002f24#32+0x4c6#32)) ram 0 [] [] = _
      rw [show 0x80002f24#32+0x4c6#32=0x800033ea#32 by decide +kernel,jump_ok _ _ (by decide)]
      simp only [d,full,ite_true]
      rfl
    · simp only [full,decide_false,Bool.false_eq_true,ite_false,d]
      rfl
  refine ⟨d,.step s0 (.step s1 (.single s2)),rfl,?_,?_,?_,rfl⟩
  · simp [d,b,a,Core.wr_get_ne,Core.wr_get]
  · simp [d,b,Core.wr_get]
  · intro r h24 h10;simp [d,b,a,Core.wr_get_ne,h24,h10]
end E5R.Thermostat.HeadFieldsGuard
