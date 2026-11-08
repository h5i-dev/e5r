import Projects.thermostat.HeadValueInit
import Projects.thermostat.HeadValueScan
namespace E5R.Thermostat.HeadValueBytes
open E5R E5R.Thermostat HttpRequestSpec HeadLineScanSpec

/-- Actual complete field_bytes validation, including the empty-value path,
    ending at the real OWS/trim entry or the actual rejection block. -/
theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (sp buf : Word) (start k finish length : Nat)
    (hp : c.pc=0x80003068#32) (state : HeadNameState.At c sp buf start k finish length)
    (h26 : c.get 26=BitVec.ofNat 32 finish) (hword : ramRead ram (sp+4#32) .w=BitVec.ofNat 32 k)
    (hi : k<finish) (hn : finish≤length) (hlen : length≤2048) (stack : Memory.Block B sp 56) (ha : sp.toNat%4=0) (mem : Memory.Block B buf length) :
    let g := bytes ram buf
    ∃ n d, 3≤n ∧ n≤5+13*(finish-(k+1)) ∧ Quiet.Steps B img n ⟨c,ram⟩ ⟨d,ram⟩ ∧
      d.pc=(if allIn isFieldByte g (k+1) finish then (if k+1=finish then 0x800030c0#32 else 0x800030a4#32) else 0x8000342c#32) ∧
      d.get 15=BitVec.ofNat 32 (k+1) ∧ d.get 25=BitVec.ofNat 32 (finish-(k+1)) ∧
      (∀ r : Reg, r≠15 → r≠13 → r≠30 → r≠12 → r≠10 → r≠31 → d.get r=c.get r) ∧ d.sameCsr c := by
  let g := bytes ram buf
  obtain ⟨n,a,nlo,nhi,setup,pc,index,slice,frame,csr⟩ := HeadValueInit.contract B c ram sp buf start k finish length hp state h26 hword hi hn hlen stack ha
  have inverse : a.get 25=BitVec.ofNat 32 (finish-(k+1)) := by
    simpa only [Nat.sub_sub] using (frame 25 (by decide) (by decide)).trans state.inverse
  by_cases last : k+1=finish
  · have done : allIn isFieldByte g (k+1) finish=true := allIn_end (by omega)
    refine ⟨n,a,nlo,by omega,setup,?_,index,inverse,fun r h15 h13 _ _ _ _ => frame r h15 h13,csr⟩
    change a.pc=(if allIn isFieldByte g (k+1) finish then (if k+1=finish then 0x800030c0#32 else 0x800030a4#32) else 0x8000342c#32)
    rw [done]
    simpa only [last,ite_true] using pc
  · have more : k+1<finish := by omega
    have atLoop : a.pc=0x8000307c#32 := by simpa only [last,ite_false] using pc
    obtain ⟨m,d,mlo,mhi,scan,pc2,finished,frame2,csr2⟩ := HeadValueScan.contract B a ram buf (k+1) finish length atLoop (slice more) more hn hlen mem
    refine ⟨n+m,d,by omega,by omega,setup.trans scan,?_,(frame2 15 (by decide) (by decide) (by decide) (by decide) (by decide)).trans index,
      (frame2 25 (by decide) (by decide) (by decide) (by decide) (by decide)).trans inverse,?_,csr2.trans csr⟩
    · change d.pc=(if allIn isFieldByte g (k+1) finish then (if k+1=finish then 0x800030c0#32 else 0x800030a4#32) else 0x8000342c#32)
      simpa only [last,ite_false] using pc2
    · intro r h15 h13 h30 h12 h10 h31
      exact (frame2 r h30 h12 h13 h10 h31).trans (frame r h15 h13)
end E5R.Thermostat.HeadValueBytes
