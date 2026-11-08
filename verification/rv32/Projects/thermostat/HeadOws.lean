import Projects.thermostat.HeadOwsForwardScan
import Projects.thermostat.HeadOwsAllFinish
import Projects.thermostat.HeadOwsTrim
namespace E5R.Thermostat.HeadOws
open E5R E5R.Thermostat HttpRequestSpec HeadLineScanSpec

/-- Complete actual leading/trailing OWS processing for a nonempty raw value.
    All-OWS values follow the ELF's direct empty-value path. -/
theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (sp buf : Word) (start finish length : Nat)
    (hp : c.pc=0x800030a4#32) (h2 : c.get 2=sp) (h15 : c.get 15=BitVec.ofNat 32 start) (h25 : c.get 25=BitVec.ofNat 32 (finish-start))
    (h26 : c.get 26=BitVec.ofNat 32 finish) (hraw : ramRead ram (sp+48#32) .w=BitVec.ofNat 32 length) (hbuf : ramRead ram (sp+44#32) .w=buf)
    (hi : start<finish) (hn : finish≤length) (hlen : length≤2048) (mem : Memory.Block B buf length) (stack : Memory.Block B sp 56) (ha : sp.toNat%4=0) :
    let g := bytes ram buf
    let vs := scan isOws g start finish
    ∃ n d, 0<n ∧ n≤4+26*(finish-start) ∧ Quiet.Steps B img n ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc=0x800030fa#32 ∧
      d.get 15=BitVec.ofNat 32 vs ∧ d.get 25=BitVec.ofNat 32 (trimEnd g vs finish) ∧
      (∀ r : Reg, r≠10 → r≠12 → r≠25 → r≠15 → r≠13 → d.get r=c.get r) ∧ d.sameCsr c := by
  let g := bytes ram buf
  let vs := scan isOws g start finish
  have lower : start≤vs := scan_ge isOws g start finish
  have upper : vs≤finish := scan_le isOws g start finish (by omega)
  obtain ⟨n,a,nlo,nhi,forward,pc,index,remaining,frame,csr⟩ := HeadOwsForwardScan.contract B c ram sp buf start finish length hp h2 h15 h25 hraw hbuf hi hn hlen mem stack ha
  change a.pc=HeadOwsForwardScan.endpoint vs finish at pc
  by_cases inside : vs<finish
  · have atTrim : a.pc=0x800030c0#32 := by simpa only [HeadOwsForwardScan.endpoint,inside,ite_true] using pc
    obtain ⟨m,d,mlo,mhi,backward,endPC,valueEnd,frame2,csr2⟩ := HeadOwsTrim.contract B a ram sp buf vs finish length atTrim
      ((frame 2 (by decide) (by decide) (by decide) (by decide)).trans h2) index
      ((frame 26 (by decide) (by decide) (by decide) (by decide)).trans h26) hraw hbuf (by omega) hn hlen mem stack ha
    refine ⟨n+m,d,by omega,by omega,forward.trans backward,endPC,(frame2 15 (by decide) (by decide) (by decide) (by decide)).trans index,valueEnd,?_,csr2.trans csr⟩
    intro r h10 h12 h25 h15 h13
    exact (frame2 r h10 h13 h12 h25).trans (frame r h10 h12 h25 h15)
  · have last : vs=finish := by omega
    have atFinish : a.pc=0x800030f2#32 := by simpa only [HeadOwsForwardScan.endpoint,inside,ite_false] using pc
    obtain ⟨d,finishTrace,endPC,valueEnd,valueStart,frame2,csr2⟩ := HeadOwsAllFinish.contract B a ram (BitVec.ofNat 32 finish)
      ((frame 26 (by decide) (by decide) (by decide) (by decide)).trans h26) atFinish
    refine ⟨n+3,d,by omega,by omega,forward.trans finishTrace,endPC,?_,?_,?_,csr2.trans csr⟩
    · change d.get 15=BitVec.ofNat 32 vs
      rw [last];exact valueStart
    · change d.get 25=BitVec.ofNat 32 (trimEnd g vs finish)
      have done : trimEnd g vs finish=finish := by rw [last,trimEnd];simp
      rw [done];exact valueEnd
    · intro r h10 h12 h25 h15 _
      exact (frame2 r h25 h15).trans (frame r h10 h12 h25 h15)
end E5R.Thermostat.HeadOws
