import Projects.thermostat.HeadValueBytes
import Projects.thermostat.HeadOws
namespace E5R.Thermostat.HeadHeaderValue
open E5R E5R.Thermostat HttpRequestSpec HeadLineScanSpec

/-- Actual complete field-byte validation and leading/trailing OWS processing.
    Success yields exact trimmed value spans, not a postulated typed field. -/
theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (sp buf : Word) (start k finish length : Nat)
    (hp : c.pc=0x80003068#32) (state : HeadNameState.At c sp buf start k finish length)
    (h26 : c.get 26=BitVec.ofNat 32 finish) (hword : ramRead ram (sp+4#32) .w=BitVec.ofNat 32 k)
    (hraw : ramRead ram (sp+48#32) .w=BitVec.ofNat 32 length) (hbuf : ramRead ram (sp+44#32) .w=buf)
    (hi : k<finish) (hn : finish≤length) (hlen : length≤2048) (stack : Memory.Block B sp 56) (ha : sp.toNat%4=0) (mem : Memory.Block B buf length) :
    let g := bytes ram buf
    let vs := scan isOws g (k+1) finish
    ∃ n d, 3≤n ∧ n≤9+39*(finish-(k+1)) ∧ Quiet.Steps B img n ⟨c,ram⟩ ⟨d,ram⟩ ∧
      d.pc=(if allIn isFieldByte g (k+1) finish then 0x800030fa#32 else 0x8000342c#32) ∧
      (allIn isFieldByte g (k+1) finish=true → d.get 15=BitVec.ofNat 32 vs ∧ d.get 25=BitVec.ofNat 32 (trimEnd g vs finish)) ∧
      (∀ r : Reg, r≠15 → r≠13 → r≠30 → r≠12 → r≠10 → r≠31 → r≠25 → d.get r=c.get r) ∧ d.sameCsr c := by
  let g := bytes ram buf
  let vs := scan isOws g (k+1) finish
  obtain ⟨n,a,nlo,nhi,validate,pc,index,remaining,frame,csr⟩ := HeadValueBytes.contract B c ram sp buf start k finish length hp state h26 hword hi hn hlen stack ha mem
  have stackA : a.get 2=sp := (frame 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans state.stack
  have finishA : a.get 26=BitVec.ofNat 32 finish := (frame 26 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h26
  change a.pc=(if allIn isFieldByte g (k+1) finish then (if k+1=finish then 0x800030c0#32 else 0x800030a4#32) else 0x8000342c#32) at pc
  cases valid : allIn isFieldByte g (k+1) finish with
  | false =>
    refine ⟨n,a,nlo,by omega,validate,?_,?_,fun r h15 h13 h30 h12 h10 h31 _ => frame r h15 h13 h30 h12 h10 h31,csr⟩
    · change a.pc=(if allIn isFieldByte g (k+1) finish then 0x800030fa#32 else 0x8000342c#32)
      simpa only [valid,Bool.false_eq_true,ite_false] using pc
    · change allIn isFieldByte g (k+1) finish=true → _
      rw [valid];intro impossible;contradiction
  | true =>
    by_cases last : k+1=finish
    · have atTrim : a.pc=0x800030c0#32 := by
        rw [valid] at pc
        simpa only [last,ite_true] using pc
      obtain ⟨m,d,mlo,mhi,trim,endPC,valueEnd,frame2,csr2⟩ := HeadOwsTrim.contract B a ram sp buf (k+1) finish length atTrim stackA index finishA hraw hbuf (by omega) hn hlen mem stack ha
      have atEnd : vs=k+1 := scan_end (by omega)
      refine ⟨n+m,d,by omega,by omega,validate.trans trim,?_,?_,?_,csr2.trans csr⟩
      · change d.pc=(if allIn isFieldByte g (k+1) finish then 0x800030fa#32 else 0x8000342c#32)
        simpa only [valid,ite_true] using endPC
      · intro _
        change d.get 15=BitVec.ofNat 32 vs ∧ d.get 25=BitVec.ofNat 32 (trimEnd g vs finish)
        rw [atEnd]
        exact ⟨(frame2 15 (by decide) (by decide) (by decide) (by decide)).trans index,valueEnd⟩
      · intro r h15 h13 h30 h12 h10 h31 h25
        exact (frame2 r h10 h13 h12 h25).trans (frame r h15 h13 h30 h12 h10 h31)
    · have atOWS : a.pc=0x800030a4#32 := by simpa only [valid,last,ite_true,ite_false] using pc
      obtain ⟨m,d,mlo,mhi,ows,endPC,valueStart,valueEnd,frame2,csr2⟩ := HeadOws.contract B a ram sp buf (k+1) finish length atOWS stackA index remaining finishA hraw hbuf (by omega) hn hlen mem stack ha
      refine ⟨n+m,d,by omega,by omega,validate.trans ows,?_,fun _ => ⟨valueStart,valueEnd⟩,?_,csr2.trans csr⟩
      · change d.pc=(if allIn isFieldByte g (k+1) finish then 0x800030fa#32 else 0x8000342c#32)
        simpa only [valid,ite_true] using endPC
      · intro r h15 h13 h30 h12 h10 h31 h25
        exact (frame2 r h10 h12 h25 h15 h13).trans (frame r h15 h13 h30 h12 h10 h31)
end E5R.Thermostat.HeadHeaderValue
