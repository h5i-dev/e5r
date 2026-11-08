import Projects.thermostat.MainRamCopy264
import Projects.thermostat.HeadSaved
namespace E5R.Thermostat.MainRamCall264
open E5R E5R.Thermostat

def values (c : Core) (ret : Word) (rr : Reg) : Word := if rr=1 then ret else c.get rr

/-- Sound composition of an actual eight-instruction call certificate with
    the independently proved real264-byte memcpy and complete saved-register
    return. The caller certificate is a proof premise, never a semantic stub. -/
theorem contract (B : Board) (c a : Core) (ram : Word → BitVec 8) (sp retPC : Word) (src dst : Nat)
    (sourceBound : 4*src+264≤5232) (destinationBound : 4*dst+264<5232)
    (apart : 4*src+264≤4*dst ∨ 4*dst+264≤4*src)
    (call : Quiet.Steps B img 8 ⟨c,ram⟩ ⟨a,ram⟩) (hp : a.pc=0x80005182#32)
    (h2 : c.get 2=sp) (h10 : a.get 10=MainRamCopy264.addr sp dst)
    (h11 : a.get 11=MainRamCopy264.addr sp src) (h12 : a.get 12=264#32) (h1 : a.get 1=retPC)
    (regs : ∀ rr : Reg, rr≠1 → rr≠10 → rr≠11 → rr≠12 → a.get rr=c.get rr) (csr : a.sameCsr c)
    (mask : retPC &&& ~~~1=retPC) (stack : Memory.Block B sp 5232) (aligned : sp.toNat%4=0) :
    ∃ d, Quiet.Steps B img 362 ⟨c,ram⟩ ⟨d,MainRamCopy264.memory ram sp src dst⟩ ∧ d.pc=retPC ∧ d.get 2=sp ∧
      HeadSaved.CoreAt d (values c retPC) ∧ d.sameCsr c := by
  have a2 : a.get 2=sp := (regs 2 (by decide) (by decide) (by decide) (by decide)).trans h2
  obtain ⟨d,copy,ret,_⟩ := MainRamCopy264.contract B a ram sp src dst sourceBound destinationBound apart hp a2 h10 h11 h12 stack aligned
  have pc : d.pc=retPC := by rw [ret.pc,h1,mask]
  have saved : HeadSaved.CoreAt d (values c retPC) := by
    constructor
    · simpa only [values,ite_true] using ret.x1.trans h1
    · simpa only [values,show ¬((8 : Reg)=1) by decide,ite_false] using ret.x8.trans (regs 8 (by decide) (by decide) (by decide) (by decide))
    · simpa only [values,show ¬((9 : Reg)=1) by decide,ite_false] using ret.x9.trans (regs 9 (by decide) (by decide) (by decide) (by decide))
    · simpa only [values,show ¬((18 : Reg)=1) by decide,ite_false] using ret.x18.trans (regs 18 (by decide) (by decide) (by decide) (by decide))
    · simpa only [values,show ¬((19 : Reg)=1) by decide,ite_false] using ret.x19.trans (regs 19 (by decide) (by decide) (by decide) (by decide))
    · simpa only [values,show ¬((20 : Reg)=1) by decide,ite_false] using ret.x20.trans (regs 20 (by decide) (by decide) (by decide) (by decide))
    · simpa only [values,show ¬((21 : Reg)=1) by decide,ite_false] using ret.x21.trans (regs 21 (by decide) (by decide) (by decide) (by decide))
    · simpa only [values,show ¬((22 : Reg)=1) by decide,ite_false] using ret.x22.trans (regs 22 (by decide) (by decide) (by decide) (by decide))
    · simpa only [values,show ¬((23 : Reg)=1) by decide,ite_false] using ret.x23.trans (regs 23 (by decide) (by decide) (by decide) (by decide))
    · simpa only [values,show ¬((24 : Reg)=1) by decide,ite_false] using ret.x24.trans (regs 24 (by decide) (by decide) (by decide) (by decide))
    · simpa only [values,show ¬((25 : Reg)=1) by decide,ite_false] using ret.x25.trans (regs 25 (by decide) (by decide) (by decide) (by decide))
    · simpa only [values,show ¬((26 : Reg)=1) by decide,ite_false] using ret.x26.trans (regs 26 (by decide) (by decide) (by decide) (by decide))
    · simpa only [values,show ¬((27 : Reg)=1) by decide,ite_false] using ret.x27.trans (regs 27 (by decide) (by decide) (by decide) (by decide))
  exact ⟨d,call.trans copy,pc,ret.sp.trans a2,saved,ret.csr.trans csr⟩
end E5R.Thermostat.MainRamCall264
