import Projects.thermostat.HeadVersionBoundsRaw
import Projects.thermostat.HeadTargetMath
namespace E5R.Thermostat.HeadVersionBounds
open E5R E5R.Thermostat

/-- The three actual digit-index panic branches are excluded by the available
    complete version span; the saved input length is read from real RAM. -/
theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (sp : Word) (te length : Nat)
    (hp : c.pc=0x80002e8c#32) (h7 : c.get 7=BitVec.ofNat 32 (te-1)) (h2 : c.get 2=sp)
    (hword : ramRead ram (sp+48#32) .w=BitVec.ofNat 32 length)
    (hm : Memory.Block B sp 56) (ha : sp.toNat%4=0)
    (ht : 0<te) (hw : te+9≤length) (hlen : length≤2048) :
    ∃ d, Quiet.Steps B img 9 ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc=0x80002eaa#32 ∧
      d.get 10=BitVec.ofNat 32 (te+8) ∧ d.get 11=BitVec.ofNat 32 length ∧
      (∀ r : Reg, r≠10 → r≠11 → d.get r=c.get r) ∧ d.sameCsr c := by
  have index (k : Nat) : BitVec.ofNat 32 (te-1)+BitVec.ofNat 32 (k+1)=BitVec.ofNat 32 (te+k) := by
    rw [←BitVec.ofNat_add]
    congr 1
    omega
  have test (k : Nat) (hk : 6≤k ∧ k≤8) :
      taken .geu (BitVec.ofNat 32 (te-1)+BitVec.ofNat 32 (k+1)) (BitVec.ofNat 32 length)=false := by
    rw [index k,HeadTargetMath.geu (te+k) length (by omega) hlen]
    simp only [show ¬length≤te+k by omega,decide_false]
  obtain ⟨d,trace,pc,last,len,frame,csr⟩ := HeadVersionBoundsRaw.contract B c ram sp (BitVec.ofNat 32 (te-1)) (BitVec.ofNat 32 length)
    h7 h2 hword hm ha (test 6 (by decide)) (test 7 (by decide)) (test 8 (by decide)) hp
  exact ⟨d,trace,pc,last.trans (index 8),len,frame,csr⟩
end E5R.Thermostat.HeadVersionBounds
