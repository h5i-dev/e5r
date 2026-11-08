import Projects.thermostat.MainCloseCode
import Projects.thermostat.QuietBranch
import Projects.thermostat.MainCloseScanFinishMath
set_option autoImplicit false
set_option maxRecDepth 4000
namespace E5R.Thermostat.MainCloseScanFinish
open E5R E5R.Thermostat

/-- Four actual instructions after finding a comma: complement the token index,
    compute remaining length, advance past the comma, and skip an empty token. -/
theorem comma (B : Board) (c : Core) (ram : Word → BitVec 8) (base : Word) (token total : Nat)
    (inside : token<total) (bound : total<2^32) (hp : c.pc=0x800025a4#32)
    (h10 : c.get 10=base+BitVec.ofNat 32 token) (h23 : c.get 23=BitVec.ofNat 32 token) (h14 : c.get 14=BitVec.ofNat 32 total) :
    ∃ d, Quiet.Steps B img 4 ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc=(if token=0 then 0x800025d4#32 else 0x800025b0#32) ∧
      d.get 10=base+BitVec.ofNat 32 (token+1) ∧ d.get 14=BitVec.ofNat 32 (total-token-1) ∧
      (∀ r : Reg, r≠10 → r≠14 → r≠15 → d.get r=c.get r) ∧ d.sameCsr c := by
  let a := c.wr 15 (~~~(BitVec.ofNat 32 token)) 0x800025a8#32
  let b := a.wr 14 (BitVec.ofNat 32 (total-token-1)) 0x800025aa#32
  let e := b.wr 10 (base+BitVec.ofNat 32 (token+1)) 0x800025ac#32
  have sa : Quiet.Step B img ⟨c,ram⟩ ⟨a,ram⟩ := by
    refine Quiet.step_of (by rw [hp];decide) (by rw [hp];exact re2147493284) fun o => ?_
    change Observed.interp B img o (exec c _ _) ram 0 [] [] = ⟨.ok a ram [],[]⟩
    rw [exec_opimm,h23,hp]
    change Observed.interp B img o (Eff.done (c.wr 15 (BitVec.ofNat 32 token ^^^ BitVec.allOnes 32) 0x800025a8#32)) ram 0 [] [] = _
    rw [BitVec.xor_allOnes];rfl
  have sb : Quiet.Step B img ⟨a,ram⟩ ⟨b,ram⟩ := by
    refine Quiet.step_of (by change (0x800025a8#32).getLsbD 0=false;decide) re2147493288 fun o => ?_
    change Observed.interp B img o (exec a _ _) ram 0 [] [] = ⟨.ok b ram [],[]⟩
    have a14 : a.get 14=BitVec.ofNat 32 total := by simp [a,Core.wr_get,h14]
    have a15 : a.get 15= ~~~(BitVec.ofNat 32 token) := by simp [a,Core.wr_get]
    rw [exec_op,a14,a15]
    change Observed.interp B img o (Eff.done (a.wr 14 (BitVec.ofNat 32 total+~~~(BitVec.ofNat 32 token)) 0x800025aa#32)) ram 0 [] [] = _
    rw [MainCloseScanFinishMath.remaining total token inside bound];rfl
  have se : Quiet.Step B img ⟨b,ram⟩ ⟨e,ram⟩ := by
    refine Quiet.step_of (by change (0x800025aa#32).getLsbD 0=false;decide) re2147493290 fun o => ?_
    change Observed.interp B img o (exec b _ _) ram 0 [] [] = ⟨.ok e ram [],[]⟩
    have b10 : b.get 10=base+BitVec.ofNat 32 token := by simp [b,a,Core.wr_get,h10]
    rw [exec_opimm,b10]
    change Observed.interp B img o (Eff.done (b.wr 10 ((base+BitVec.ofNat 32 token)+1#32) 0x800025ac#32)) ram 0 [] [] = _
    rw [BitVec.add_assoc,←BitVec.ofNat_add];rfl
  have e23 : e.get 23=BitVec.ofNat 32 token := by simp [e,b,a,Core.wr_get,h23]
  obtain ⟨d,sd,pd,dr,dc⟩ := QuietBranch.contract B img e ram 0x800025ac#32 4#32 0x28#32 .eq 23 0 (decide (token=0))
    rfl (by decide) (by decide) re2147493292 (by rw [e23,Core.get_zero];exact MainCloseScanFinishMath.zeroTest token (by omega))
  refine ⟨d,(Quiet.Steps.single sa).trans ((Quiet.Steps.single sb).trans ((Quiet.Steps.single se).trans sd)),?_,?_,?_,?_,dc.trans ((Core.sameCsr_wr b _ _ _).trans ((Core.sameCsr_wr a _ _ _).trans (Core.sameCsr_wr c _ _ _)))⟩
  · simpa only [decide_eq_true_eq,show 0x800025ac#32+0x28#32=0x800025d4#32 by decide +kernel,
      show 0x800025ac#32+4#32=0x800025b0#32 by decide +kernel] using pd
  · exact (dr 10).trans (by simp [e,Core.wr_get])
  · exact (dr 14).trans (by simp [e,b,Core.wr_get])
  · intro r n10 n14 n15
    exact (dr r).trans (by simp only [e,b,a,Core.wr_get_ne _ _ _ _ _ n10,Core.wr_get_ne _ _ _ _ _ n14,Core.wr_get_ne _ _ _ _ _ n15])

/-- Exhaustion without a comma restores the original token base and length. -/
theorem absent (B : Board) (c : Core) (ram : Word → BitVec 8) (base : Word) (total : Nat)
    (positive : 0<total) (bound : total<2^32) (hp : c.pc=0x8000259c#32)
    (h22 : c.get 22=base) (h14 : c.get 14=BitVec.ofNat 32 total) :
    ∃ d, Quiet.Steps B img 3 ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc=0x800025b0#32 ∧ d.get 10=base ∧ d.get 23=BitVec.ofNat 32 total ∧
      (∀ r : Reg, r≠10 → r≠23 → d.get r=c.get r) ∧ d.sameCsr c := by
  let a := c.wr 10 base 0x8000259e#32
  let b := a.wr 23 (BitVec.ofNat 32 total) 0x800025a0#32
  have sa : Quiet.Step B img ⟨c,ram⟩ ⟨a,ram⟩ := by
    refine Quiet.step_of (by rw [hp];decide) (by rw [hp];exact re2147493276) fun o => ?_
    change Observed.interp B img o (exec c _ _) ram 0 [] [] = ⟨.ok a ram [],[]⟩
    rw [exec_op,Core.get_zero,h22,hp]
    simp only [alu,show (0 : Word)=0#32 from rfl,BitVec.zero_add];rfl
  have sb : Quiet.Step B img ⟨a,ram⟩ ⟨b,ram⟩ := by
    refine Quiet.step_of (by change (0x8000259e#32).getLsbD 0=false;decide) re2147493278 fun o => ?_
    change Observed.interp B img o (exec a _ _) ram 0 [] [] = ⟨.ok b ram [],[]⟩
    have a14 : a.get 14=BitVec.ofNat 32 total := by simp [a,Core.wr_get,h14]
    rw [exec_op,Core.get_zero,a14]
    simp only [alu,show (0 : Word)=0#32 from rfl,BitVec.zero_add];rfl
  have b14 : b.get 14=BitVec.ofNat 32 total := by simp [b,a,Core.wr_get,h14]
  have nonzero : BitVec.ofNat 32 total≠(0 : Word) := by
    intro equal
    have numeric := congrArg BitVec.toNat equal
    rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt bound] at numeric
    change total=0 at numeric
    omega
  obtain ⟨d,sd,pd,dr,dc⟩ := QuietBranch.contract B img b ram 0x800025a0#32 2#32 0x10#32 .ne 14 0 true rfl (by decide) (by decide) re2147493280
    (by rw [b14,Core.get_zero];change decide (BitVec.ofNat 32 total≠(0 : Word))=true;exact decide_eq_true nonzero)
  refine ⟨d,(Quiet.Steps.single sa).trans ((Quiet.Steps.single sb).trans sd),?_,?_,?_,?_,dc.trans ((Core.sameCsr_wr a _ _ _).trans (Core.sameCsr_wr c _ _ _))⟩
  · simpa only [ite_true,show 0x800025a0#32+0x10#32=0x800025b0#32 by decide +kernel] using pd
  · exact (dr 10).trans (by simp [b,a,Core.wr_get])
  · exact (dr 23).trans (by simp [b,Core.wr_get])
  · intro r n10 n23
    exact (dr r).trans (by simp only [b,a,Core.wr_get_ne _ _ _ _ _ n23,Core.wr_get_ne _ _ _ _ _ n10])
end E5R.Thermostat.MainCloseScanFinish
