import Projects.thermostat.MainCloseCode
import Projects.thermostat.QuietByteLoad
import Projects.thermostat.QuietBranch
import Projects.thermostat.Literal
set_option autoImplicit false
namespace E5R.Thermostat.MainCloseScanHead
open E5R E5R.Thermostat

/-- Actual current-pointer addition, byte load and comma comparison. -/
theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (base : Word) (i : Nat) (byte : BitVec 8)
    (hp : c.pc=0x80002586#32) (h22 : c.get 22=base) (h23 : c.get 23=BitVec.ofNat 32 i) (h8 : c.get 8=44#32)
    (memory : B.inRam (base+BitVec.ofNat 32 i) 1=true) (data : ram (base+BitVec.ofNat 32 i)=byte) :
    ∃ d, Quiet.Steps B img 3 ⟨c,ram⟩ ⟨d,ram⟩ ∧
      d.pc=(if byte=44#8 then 0x800025a4#32 else 0x80002592#32) ∧
      d.get 10=base+BitVec.ofNat 32 i ∧ d.get 11=BitVec.ofNat 32 byte.toNat ∧
      (∀ r : Reg, r≠10 → r≠11 → d.get r=c.get r) ∧ d.sameCsr c := by
  let a := c.wr 10 (base+BitVec.ofNat 32 i) 0x8000258a#32
  have sa : Quiet.Step B img ⟨c,ram⟩ ⟨a,ram⟩ := by
    refine Quiet.step_of (by rw [hp];decide) (by rw [hp];exact re2147493254) fun o => ?_
    change Observed.interp B img o (exec c _ _) ram 0 [] [] = ⟨.ok a ram [],[]⟩
    rw [exec_op,h22,h23,hp];rfl
  have a10 : a.get 10=base+BitVec.ofNat 32 i := by simp [a,Core.wr_get]
  obtain ⟨b,sb,pb,b11,br,bc⟩ := QuietByteLoad.contract B img a ram 0x8000258a#32 (base+BitVec.ofNat 32 i) 0#32 11 10 byte
    rfl (by decide) (by decide) re2147493258 a10 (by simpa only [BitVec.add_zero] using memory) (by simpa only [BitVec.add_zero] using data)
  have pb' : b.pc=0x8000258e#32 := by simpa only [show 0x8000258a#32+4#32=0x8000258e#32 by decide +kernel] using pb
  have b8 : b.get 8=44#32 := (br 8 (by decide)).trans (by simpa [a,Core.wr_get] using h8)
  obtain ⟨d,sd,pd,dr,dc⟩ := QuietBranch.contract B img b ram 0x8000258e#32 4#32 0x16#32 .eq 11 8 (decide (byte=44#8)) pb'
    (by decide) (by decide) re2147493262
    (by rw [b11,b8];change decide (BitVec.ofNat 32 byte.toNat=BitVec.ofNat 32 (44#8).toNat)=_;simp only [Literal.byte_injective])
  refine ⟨d,(Quiet.Steps.single sa).trans (sb.trans sd),?_,(dr 10).trans ((br 10 (by decide)).trans a10),(dr 11).trans b11,?_,dc.trans (bc.trans (Core.sameCsr_wr c _ _ _))⟩
  · simpa only [decide_eq_true_eq,show 0x8000258e#32+0x16#32=0x800025a4#32 by decide +kernel,
      show 0x8000258e#32+4#32=0x80002592#32 by decide +kernel] using pd
  · intro r n10 n11
    exact (dr r).trans ((br r n11).trans (Core.wr_get_ne _ _ _ _ _ n10))
end E5R.Thermostat.MainCloseScanHead
