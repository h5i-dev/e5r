import Projects.thermostat.MainCloseCode
import Projects.thermostat.AsciiFoldCompare
set_option autoImplicit false
namespace E5R.Thermostat.MainCloseValueTail
open E5R E5R.Thermostat

theorem next (B : Board) (c : Core) (ram : Word → BitVec 8) (delimiter : Word)
    (hp : c.pc=0x800025d4#32) (h11 : c.get 11=delimiter) (h8 : c.get 8=44#32) :
    ∃ d, Quiet.Steps B img 1 ⟨c,ram⟩ ⟨d,ram⟩ ∧
      d.pc=(if delimiter≠44#32 then 0x80002474#32 else 0x800025d8#32) ∧
      (∀ r : Reg, d.get r=c.get r) ∧ d.sameCsr c := by
  obtain ⟨d,trace,pc,regs,csr⟩ := QuietBranch.contract B img c ram 0x800025d4#32 4#32 0xfffffea0#32 .ne 11 8
    (decide (delimiter≠44#32)) hp (by decide) (by decide) re2147493332 (by rw [h11,h8];rfl)
  refine ⟨d,trace,?_,regs,csr⟩
  simpa only [decide_eq_true_eq,show 0x800025d4#32+0xfffffea0#32=0x80002474#32 by decide +kernel,
    show 0x800025d4#32+4#32=0x800025d8#32 by decide +kernel] using pc

theorem delimiter (B : Board) (c : Core) (ram : Word → BitVec 8) (delimiter : Word)
    (hp : c.pc=0x80002672#32) (h11 : c.get 11=delimiter) (h8 : c.get 8=44#32) :
    ∃ d, Quiet.Steps B img 1 ⟨c,ram⟩ ⟨d,ram⟩ ∧
      d.pc=(if delimiter≠44#32 then 0x80002470#32 else 0x80002676#32) ∧
      (∀ r : Reg, d.get r=c.get r) ∧ d.sameCsr c := by
  obtain ⟨d,trace,pc,regs,csr⟩ := QuietBranch.contract B img c ram 0x80002672#32 4#32 0xfffffdfe#32 .ne 11 8
    (decide (delimiter≠44#32)) hp (by decide) (by decide) re2147493490 (by rw [h11,h8];rfl)
  refine ⟨d,trace,?_,regs,csr⟩
  simpa only [decide_eq_true_eq,show 0x80002672#32+0xfffffdfe#32=0x80002470#32 by decide +kernel,
    show 0x80002672#32+4#32=0x80002676#32 by decide +kernel] using pc

theorem lastUnequal (B : Board) (c : Core) (ram : Word → BitVec 8) (byte : BitVec 8)
    (hp : c.pc=0x80002676#32) (h15 : c.get 15=BitVec.ofNat 32 (HeaderSpec.lower byte).toNat) (h29 : c.get 29=101#32) :
    ∃ d, Quiet.Steps B img 1 ⟨c,ram⟩ ⟨d,ram⟩ ∧
      d.pc=(if HeaderSpec.lower byte≠101#8 then 0x800025d8#32 else 0x8000267a#32) ∧
      (∀ r : Reg, d.get r=c.get r) ∧ d.sameCsr c := by
  obtain ⟨d,trace,pc,regs,csr⟩ := QuietBranch.contract B img c ram 0x80002676#32 4#32 0xffffff62#32 .ne 15 29
    (decide (HeaderSpec.lower byte≠101#8)) hp (by decide) (by decide) re2147493494 (by rw [h15,h29];exact AsciiFoldCompare.unequal byte 101#8)
  refine ⟨d,trace,?_,regs,csr⟩
  simpa only [decide_eq_true_eq,show 0x80002676#32+0xffffff62#32=0x800025d8#32 by decide +kernel,
    show 0x80002676#32+4#32=0x8000267a#32 by decide +kernel] using pc

theorem lastEqual (B : Board) (c : Core) (ram : Word → BitVec 8) (byte : BitVec 8)
    (hp : c.pc=0x80002470#32) (h15 : c.get 15=BitVec.ofNat 32 (HeaderSpec.lower byte).toNat) (h29 : c.get 29=101#32) :
    ∃ d, Quiet.Steps B img 1 ⟨c,ram⟩ ⟨d,ram⟩ ∧
      d.pc=(if HeaderSpec.lower byte=101#8 then 0x800026bc#32 else 0x80002474#32) ∧
      (∀ r : Reg, d.get r=c.get r) ∧ d.sameCsr c := by
  obtain ⟨d,trace,pc,regs,csr⟩ := QuietBranch.contract B img c ram 0x80002470#32 4#32 0x24c#32 .eq 15 29
    (decide (HeaderSpec.lower byte=101#8)) hp (by decide) (by decide) re2147492976 (by rw [h15,h29];change decide (BitVec.ofNat 32 (HeaderSpec.lower byte).toNat=BitVec.ofNat 32 (101#8).toNat)=_;simp only [Literal.byte_injective])
  refine ⟨d,trace,?_,regs,csr⟩
  simpa only [decide_eq_true_eq,show 0x80002470#32+0x24c#32=0x800026bc#32 by decide +kernel,
    show 0x80002470#32+4#32=0x80002474#32 by decide +kernel] using pc

theorem lastJump (B : Board) (c : Core) (ram : Word → BitVec 8) (hp : c.pc=0x8000267a#32) :
    ∃ d, Quiet.Steps B img 1 ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc=0x80002470#32 ∧
      (∀ r : Reg, d.get r=c.get r) ∧ d.sameCsr c := by
  let d := c.goto 0x80002470#32
  have step : Quiet.Step B img ⟨c,ram⟩ ⟨d,ram⟩ := by
    refine Quiet.step_of (by rw [hp];decide) (by rw [hp];exact re2147493498) fun o => ?_
    change Observed.interp B img o (exec c _ _) ram 0 [] [] = ⟨.ok d ram [],[]⟩
    rw [exec_jal,Core.set_zero,hp,show 0x8000267a#32+0xfffffdf6#32=0x80002470#32 by decide +kernel,jump_ok _ _ (by decide)]
    rfl
  exact ⟨d,.single step,rfl,fun _ => rfl,rfl⟩

/-- Final character and delimiter control, including the real compressed jump.
    Rejected tokens continue at the actual next-token/header test. -/
theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (delimiterWord : Word) (byte : BitVec 8)
    (hp : c.pc=0x80002672#32) (h11 : c.get 11=delimiterWord) (h8 : c.get 8=44#32)
    (h15 : c.get 15=BitVec.ofNat 32 (HeaderSpec.lower byte).toNat) (h29 : c.get 29=101#32) :
    ∃ n d, n≤4 ∧ Quiet.Steps B img n ⟨c,ram⟩ ⟨d,ram⟩ ∧
      d.pc=(if HeaderSpec.lower byte=101#8 then 0x800026bc#32 else if delimiterWord=44#32 then 0x800025d8#32 else 0x80002474#32) ∧
      (∀ r : Reg, d.get r=c.get r) ∧ d.sameCsr c := by
  obtain ⟨a,sa,pa,ar,ac⟩ := delimiter B c ram delimiterWord hp h11 h8
  by_cases comma : delimiterWord=44#32
  · have pa' : a.pc=0x80002676#32 := by simpa [comma] using pa
    obtain ⟨b,sb,pb,br,bc⟩ := lastUnequal B a ram byte pa' ((ar 15).trans h15) ((ar 29).trans h29)
    by_cases equal : HeaderSpec.lower byte=101#8
    · have pb' : b.pc=0x8000267a#32 := by simpa [equal] using pb
      obtain ⟨e,se,pe,er,ec⟩ := lastJump B b ram pb'
      obtain ⟨d,sd,pd,dr,dc⟩ := lastEqual B e ram byte pe ((er 15).trans ((br 15).trans ((ar 15).trans h15)))
        ((er 29).trans ((br 29).trans ((ar 29).trans h29)))
      refine ⟨4,d,by omega,((sa.trans sb).trans se).trans sd,?_,fun r => (dr r).trans ((er r).trans ((br r).trans (ar r))),dc.trans (ec.trans (bc.trans ac))⟩
      simpa [equal] using pd
    · refine ⟨2,b,by omega,sa.trans sb,?_,fun r => (br r).trans (ar r),bc.trans ac⟩
      simpa [equal,comma] using pb
  · have pa' : a.pc=0x80002470#32 := by simpa [comma] using pa
    obtain ⟨d,sd,pd,dr,dc⟩ := lastEqual B a ram byte pa' ((ar 15).trans h15) ((ar 29).trans h29)
    refine ⟨2,d,by omega,sa.trans sd,?_,fun r => (dr r).trans (ar r),dc.trans ac⟩
    simpa [comma] using pd
end E5R.Thermostat.MainCloseValueTail
