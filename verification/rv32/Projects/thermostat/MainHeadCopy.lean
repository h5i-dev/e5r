import Projects.thermostat.MainHeadCopyCall
import Projects.thermostat.MainHeadCopy304
import Projects.thermostat.HeadSaved
namespace E5R.Thermostat.MainHeadCopy
open E5R E5R.Thermostat

def values (c : Core) (r : Reg) : Word := if r=1 then 0x80000c14#32 else c.get r

/-- Actual success-path main call and complete304-byte copy into the live
    future Head object. All parser fields and callee-saved registers survive. -/
theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (sp : Word) (head : HttpRequestSpec.Head)
    (hp : c.pc=0x80000bf6#32) (h2 : c.get 2=sp) (stack : Memory.Block B sp 4928) (aligned : sp.toNat%4=0)
    (view : HeadCompletedView.At ram (sp+4520#32) head) :
    ∃ d, Quiet.Steps B img 412 ⟨c,ram⟩ ⟨d,MainHeadCopy304.memory ram sp⟩ ∧ d.pc=0x80000c14#32 ∧ d.get 2=sp ∧
      HeadSaved.CoreAt d (values c) ∧ HeadCompletedView.At (MainHeadCopy304.memory ram sp) (sp+3320#32) head ∧ d.sameCsr c := by
  obtain ⟨a,ta,apc,a10,a11,a12,a1,ar,ac⟩ := MainHeadCopyCall.contract B c ram sp h2 hp
  have asp : a.get 2=sp := (ar 2 (by decide) (by decide) (by decide) (by decide)).trans h2
  obtain ⟨d,td,ret,_⟩ := MainHeadCopy304.contract B a ram sp apc asp a10 a11 a12 stack aligned
  have pc : d.pc=0x80000c14#32 := by rw [ret.pc,a1];decide +kernel
  have regs : HeadSaved.CoreAt d (values c) := by
    constructor
    · simpa only [values,ite_true] using ret.x1.trans a1
    · simpa only [values,show ¬((8 : Reg)=1) by decide,ite_false] using ret.x8.trans (ar 8 (by decide) (by decide) (by decide) (by decide))
    · simpa only [values,show ¬((9 : Reg)=1) by decide,ite_false] using ret.x9.trans (ar 9 (by decide) (by decide) (by decide) (by decide))
    · simpa only [values,show ¬((18 : Reg)=1) by decide,ite_false] using ret.x18.trans (ar 18 (by decide) (by decide) (by decide) (by decide))
    · simpa only [values,show ¬((19 : Reg)=1) by decide,ite_false] using ret.x19.trans (ar 19 (by decide) (by decide) (by decide) (by decide))
    · simpa only [values,show ¬((20 : Reg)=1) by decide,ite_false] using ret.x20.trans (ar 20 (by decide) (by decide) (by decide) (by decide))
    · simpa only [values,show ¬((21 : Reg)=1) by decide,ite_false] using ret.x21.trans (ar 21 (by decide) (by decide) (by decide) (by decide))
    · simpa only [values,show ¬((22 : Reg)=1) by decide,ite_false] using ret.x22.trans (ar 22 (by decide) (by decide) (by decide) (by decide))
    · simpa only [values,show ¬((23 : Reg)=1) by decide,ite_false] using ret.x23.trans (ar 23 (by decide) (by decide) (by decide) (by decide))
    · simpa only [values,show ¬((24 : Reg)=1) by decide,ite_false] using ret.x24.trans (ar 24 (by decide) (by decide) (by decide) (by decide))
    · simpa only [values,show ¬((25 : Reg)=1) by decide,ite_false] using ret.x25.trans (ar 25 (by decide) (by decide) (by decide) (by decide))
    · simpa only [values,show ¬((26 : Reg)=1) by decide,ite_false] using ret.x26.trans (ar 26 (by decide) (by decide) (by decide) (by decide))
    · simpa only [values,show ¬((27 : Reg)=1) by decide,ite_false] using ret.x27.trans (ar 27 (by decide) (by decide) (by decide) (by decide))
  exact ⟨d,ta.trans td,pc,ret.sp.trans asp,regs,MainHeadCopy304.head ram sp head stack view,ret.csr.trans ac⟩
end E5R.Thermostat.MainHeadCopy
