import Projects.thermostat.HeadNameScan
import Projects.thermostat.HeadNameColon
namespace E5R.Thermostat.HeadNameChecked
open E5R E5R.Thermostat HttpRequestSpec HeadLineScanSpec

def good (g : Nat → Nat) (start k finish : Nat) : Prop := start<k ∧ k<finish ∧ g k=58
instance (g : Nat → Nat) (start k finish : Nat) : Decidable (good g start k finish) :=
  inferInstanceAs (Decidable (start<k ∧ k<finish ∧ g k=58))

/-- All actual name-token and exact-colon checks, including the real name-end
    scratch store. The resulting value-parser entry has byte-derived bounds. -/
theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (sp buf : Word) (start finish length : Nat)
    (hp : c.pc=0x80002ff0#32) (state : HeadNameState.At c sp buf start start finish length)
    (h24 : c.get 24=BitVec.ofNat 32 start) (h26 : c.get 26=BitVec.ofNat 32 finish)
    (hmask : ramRead ram (sp+32#32) .w=9409#32) (stack : Memory.Block B sp 56) (ha : sp.toNat%4=0)
    (hi : start<finish) (hn : finish≤length) (hlen : length≤2048) (mem : Memory.Block B buf length) :
    let g := bytes ram buf
    let k := scan isTchar g start finish
    ∃ n d after, 0<n ∧ n≤5+25*(finish-start) ∧ Quiet.Steps B img n ⟨c,ram⟩ ⟨d,after⟩ ∧
      d.pc=(if good g start k finish then 0x80003068#32 else 0x8000342c#32) ∧
      (after=ram ∨ after=ramWrite ram (sp+4#32) (BitVec.ofNat 32 k) .w) ∧
      (good g start k finish → after=ramWrite ram (sp+4#32) (BitVec.ofNat 32 k) .w ∧ HeadNameState.At d sp buf start k finish length) ∧
      (∀ r : Reg, r≠30 → r≠19 → r≠12 → r≠14 → r≠10 → r≠25 → r≠31 → d.get r=c.get r) ∧ d.sameCsr c := by
  let g := bytes ram buf
  let k := scan isTchar g start finish
  change ∃ n d after, 0<n ∧ n≤5+25*(finish-start) ∧ Quiet.Steps B img n ⟨c,ram⟩ ⟨d,after⟩ ∧
      d.pc=(if good g start k finish then 0x80003068#32 else 0x8000342c#32) ∧
      (after=ram ∨ after=ramWrite ram (sp+4#32) (BitVec.ofNat 32 k) .w) ∧
      (good g start k finish → after=ramWrite ram (sp+4#32) (BitVec.ofNat 32 k) .w ∧ HeadNameState.At d sp buf start k finish length) ∧
      (∀ r : Reg, r≠30 → r≠19 → r≠12 → r≠14 → r≠10 → r≠25 → r≠31 → d.get r=c.get r) ∧ d.sameCsr c
  have lower : start≤k := scan_ge isTchar g start finish
  obtain ⟨n,a,nlo,nhi,scan,pc,aState,byte,frame,csr⟩ := HeadNameScan.contract B c ram sp buf start start finish length hp state hmask stack ha (by omega) hi hn hlen mem
  change a.pc=HeadNameScan.endpoint g k finish at pc
  by_cases candidate : k<finish ∧ HeadNameScan.candidate (g k)
  · have atColon : a.pc=0x80003056#32 := by simpa [HeadNameScan.endpoint,candidate] using pc
    obtain ⟨m,d,mlo,mhi,colon,pc2,state2,frame2,csr2⟩ := HeadNameColon.contract B a ram sp buf start k finish length (ram (buf+BitVec.ofNat 32 k))
      atColon (aState candidate.1) ((frame 24 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h24)
      ((frame 26 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h26)
      (byte atColon) lower candidate.1 hn hlen stack ha
    refine ⟨n+m,d,HeadNameColon.memory ram sp start k,by omega,by omega,scan.trans colon,?_,?_,?_,?_,csr2.trans csr⟩
    · change d.pc=(if start<k ∧ g k=58 then 0x80003068#32 else 0x8000342c#32) at pc2
      change d.pc=(if good g start k finish then 0x80003068#32 else 0x8000342c#32)
      simpa only [good,candidate.1,and_true,true_and] using pc2
    · unfold HeadNameColon.memory
      split
      · exact Or.inl rfl
      · exact Or.inr rfl
    · intro accepted
      exact ⟨by simp [HeadNameColon.memory,show k≠start by have := accepted.1;omega],state2⟩
    · intro r h30 h19 h12 h14 h10 h25 h31
      exact (frame2 r h12).trans (frame r h30 h19 h12 h14 h10 h25 h31)
  · have rejected : ¬good g start k finish := by
      intro accepted
      apply candidate
      exact ⟨accepted.2.1,by simp only [HeadNameScan.candidate,accepted.2.2];decide⟩
    refine ⟨n,a,ram,nlo,by omega,scan,?_,Or.inl rfl,fun h => False.elim (rejected h),frame,csr⟩
    simpa only [HeadNameScan.endpoint,candidate,rejected,ite_false] using pc
end E5R.Thermostat.HeadNameChecked
