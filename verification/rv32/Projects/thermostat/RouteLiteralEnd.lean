import Projects.thermostat.RouteResult
import Projects.thermostat.QuietBranch
set_option autoImplicit false
namespace E5R.Thermostat.RouteLiteralEnd
open E5R E5R.Thermostat

theorem flag (a b : Word) : alu .sltu (a ^^^ b) 1#32=(if a=b then 1#32 else 0#32) := by
  have small : (a ^^^ b).ult 1#32=decide (a=b) := by
    simp only [BitVec.ult,BitVec.toNat_ofNat]
    have zero : (a ^^^ b).toNat=0 ↔ a=b := by
      rw [←BitVec.xor_eq_zero_iff]
      constructor
      · intro h;exact BitVec.eq_of_toNat_eq h
      · intro h;rw [h];rfl
    have smallNat : (a ^^^ b).toNat<1 ↔ (a ^^^ b).toNat=0 := by omega
    simp only [smallNat,zero]
  change (if (a ^^^ b).ult 1#32 then 1#32 else 0#32)=_
  rw [small];simp

/-- When the pattern ends, the actual matcher accepts exactly simultaneous
    path end and returns the actual capture count. -/
theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (patEnd pathEnd pathLen count : Word)
    (hp : c.pc=0x80002912#32) (h22 : c.get 22=patEnd) (h18 : c.get 18=patEnd)
    (h23 : c.get 23=pathEnd) (h9 : c.get 9=pathLen) (h8 : c.get 8=count) :
    ∃ d, Quiet.Steps B img 5 ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc=0x8000293a#32 ∧
      d.get 10=(if pathEnd=pathLen then 1#32 else 0#32) ∧ d.get 11=count ∧
      (∀ r : Reg, r≠10 → r≠11 → d.get r=c.get r) ∧ d.sameCsr c := by
  have tested : taken .eq (c.get 22) (c.get 18)=true := by rw [h22,h18];simp [taken]
  obtain ⟨a,ta,pa,ar,ac⟩ := QuietBranch.contract B img c ram 0x80002912#32 4#32 28#32 .eq 22 18 true
    hp (by decide) (by decide) rt2147494162 tested
  have ap : a.pc=0x8000292e#32 := by simpa only [ite_true,show 0x80002912#32+28#32=0x8000292e#32 by decide +kernel] using pa
  let b := a.wr 10 (pathEnd ^^^ pathLen) 0x80002932#32
  have tb : Quiet.Step B img ⟨a,ram⟩ ⟨b,ram⟩ := by
    refine Quiet.step_of (by rw [ap];decide) (by rw [ap];exact rt2147494190) fun o => ?_
    change Observed.interp B img o (exec a _ _) ram 0 [] []=⟨.ok b ram [],[]⟩
    rw [exec_op,ar 23,ar 9,h23,h9,ap];rfl
  let e := b.wr 11 (if pathEnd=pathLen then 1#32 else 0#32) 0x80002936#32
  have te : Quiet.Step B img ⟨b,ram⟩ ⟨e,ram⟩ := by
    refine Quiet.step_of (by change (0x80002932#32).getLsbD 0=false;decide) rt2147494194 fun o => ?_
    change Observed.interp B img o (exec b _ _) ram 0 [] []=⟨.ok e ram [],[]⟩
    have b10 : b.get 10=pathEnd ^^^ pathLen := Core.wr_get_self _ _ _ _ (by decide)
    rw [exec_opimm,b10,flag];rfl
  have e11 : e.get 11=(if pathEnd=pathLen then 1#32 else 0#32) := Core.wr_get_self _ _ _ _ (by decide)
  have kept (r : Reg) (n10 : r≠10) (n11 : r≠11) : e.get r=c.get r :=
    (Core.wr_get_ne _ _ _ _ _ n11).trans ((Core.wr_get_ne _ _ _ _ _ n10).trans (ar r))
  obtain ⟨d,td,pd,d10,d11,dr,dc⟩ := RouteResult.contract B e ram (if pathEnd=pathLen then 1#32 else 0#32) count e11
    ((kept 8 (by decide) (by decide)).trans h8) rfl
  refine ⟨d,((ta.trans (.single tb)).trans (.single te)).trans td,pd,d10,d11,?_,dc.trans ac⟩
  intro r n10 n11;exact (dr r n10 n11).trans (kept r n10 n11)

/-- Actual common mismatch return; RAM and captured spans remain untouched. -/
theorem failure (B : Board) (c : Core) (ram : Word → BitVec 8) (count : Word)
    (hp : c.pc=0x8000292a#32) (h8 : c.get 8=count) :
    ∃ d, Quiet.Steps B img 4 ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc=0x8000293a#32 ∧ d.get 10=0#32 ∧ d.get 11=count ∧
      (∀ r : Reg, r≠10 → r≠11 → d.get r=c.get r) ∧ d.sameCsr c := by
  let a := c.wr 11 0#32 0x8000292c#32
  let b := a.goto 0x80002936#32
  have ta : Quiet.Step B img ⟨c,ram⟩ ⟨a,ram⟩ := by
    refine Quiet.step_of (by rw [hp];decide) (by rw [hp];exact rt2147494186) fun o => ?_
    change Observed.interp B img o (exec c _ _) ram 0 [] []=⟨.ok a ram [],[]⟩
    rw [exec_opimm,Core.get_zero,hp];rfl
  have tb : Quiet.Step B img ⟨a,ram⟩ ⟨b,ram⟩ := by
    refine Quiet.step_of (by change (0x8000292c#32).getLsbD 0=false;decide) rt2147494188 fun o => ?_
    change Observed.interp B img o (exec a _ _) ram 0 [] []=⟨.ok b ram [],[]⟩
    rw [exec_jal]
    change Observed.interp B img o (jump (a.set 0 0x8000292e#32) 0x80002936#32) ram 0 [] []=_
    rw [jump_ok _ _ (by decide)];rfl
  have b11 : b.get 11=0#32 := Core.wr_get_self _ _ _ _ (by decide)
  obtain ⟨d,td,pd,d10,d11,dr,dc⟩ := RouteResult.contract B b ram 0#32 count b11
    ((Core.wr_get_ne _ _ _ _ _ (by decide)).trans h8) rfl
  refine ⟨d,(Quiet.Steps.step ta (.single tb)).trans td,pd,d10,d11,?_,dc⟩
  intro r n10 n11;exact (dr r n10 n11).trans (Core.wr_get_ne _ _ _ _ _ n11)
end E5R.Thermostat.RouteLiteralEnd
