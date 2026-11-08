import Projects.thermostat.MainMethodGuards
import Projects.thermostat.MainMethodStart
import Projects.thermostat.MainMethodBody
set_option autoImplicit false
namespace E5R.Thermostat.MainMethodDecode
open E5R E5R.Thermostat

def Frame (c d : Core) : Prop := ∀ r : Reg, r≠6 → r≠14 → r≠15 → r≠16 → r≠17 → d.get r=c.get r

/-- Every actual instruction of Method::from_bytes, both panic guards, length
    dispatch and all case-sensitive strings, including Other for every mismatch. -/
theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (rx : Word) (bytes : Nat → BitVec 8)
    (start finish used : Nat) (ordered : start≤finish) (available : finish≤used) (bound : used≤2048)
    (hp : c.pc=0x80000d50#32) (h7 : c.get 7=BitVec.ofNat 32 start)
    (h11 : c.get 11=BitVec.ofNat 32 finish) (h24 : c.get 24=BitVec.ofNat 32 used)
    (h21 : c.get 21=rx) (h26 : c.get 26=3#32) (h17 : c.get 17=5#32) (h5 : c.get 5=6#32)
    (memory : ∀ k, k<finish-start → B.inRam ((rx+BitVec.ofNat 32 start)+BitVec.ofNat 32 k) 1=true)
    (data : ∀ k, k<finish-start → ram ((rx+BitVec.ofNat 32 start)+BitVec.ofNat 32 k)=bytes k) :
    ∃ n d, n≤34 ∧ Quiet.Steps B img n ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc=0x80001160#32 ∧
      d.get 14=BitVec.ofNat 32 (MainMethodSpec.tag (MainMethodSpec.classify (finish-start) (fun i => (bytes i).toNat))) ∧
      Frame c d ∧ d.sameCsr c := by
  obtain ⟨a,guards,pa,ar,ac⟩ := MainMethodGuards.contract B c ram start finish used hp h7 h11 h24 ordered available bound
  obtain ⟨b,setup,pb,b16,b15,b14,b6,br,bc⟩ := MainMethodStart.contract B a ram rx (BitVec.ofNat 32 start) (BitVec.ofNat 32 finish)
    ((ar 21).trans h21) ((ar 7).trans h7) ((ar 11).trans h11) pa
  have len : b.get 16=BitVec.ofNat 32 (finish-start) := b16.trans (BitVec.ofNat_sub_ofNat_of_le finish start (by omega) ordered)
  obtain ⟨middle,e,mb,dispatch,pe,er,ec⟩ := MainMethodLength.contract B b ram (finish-start) (by omega) pb b6 len
    ((br 26 (by decide) (by decide) (by decide) (by decide)).trans ((ar 26).trans h26))
    ((br 17 (by decide) (by decide) (by decide) (by decide)).trans ((ar 17).trans h17))
    ((br 5 (by decide) (by decide) (by decide) (by decide)).trans ((ar 5).trans h5))
  obtain ⟨last,d,lb,body,pd,d14,dr,dc⟩ := MainMethodBody.contract B e ram (rx+BitVec.ofNat 32 start) bytes (finish-start) pe
    ((er 15 (by decide)).trans b15) ((er 14 (by decide)).trans b14) memory data
  refine ⟨2+4+middle+last,d,by omega,((guards.trans setup).trans dispatch).trans body,pd,d14,?_,dc.trans (ec.trans (bc.trans ac))⟩
  intro r h6 h14 h15 h16 h17
  exact (dr r h14 h15 h16 h17).trans ((er r h17).trans ((br r h16 h15 h14 h6).trans (ar r)))
end E5R.Thermostat.MainMethodDecode
