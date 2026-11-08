import Projects.thermostat.HeadOwsBackStep
import Projects.thermostat.HeadOwsBackAdvance
import Projects.thermostat.HeadOwsBackFinish
import Projects.thermostat.HeadLineScanSpec
namespace E5R.Thermostat.HeadOwsBackScan
open E5R E5R.Thermostat HttpRequestSpec HeadLineScanSpec

/-- The complete actual backward OWS loop, exactly refining trimEnd. -/
theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (sp buf : Word) (start pos length : Nat)
    (hp : c.pc=0x800030d0#32) (h2 : c.get 2=sp) (h15 : c.get 15=BitVec.ofNat 32 start) (h25 : c.get 25=BitVec.ofNat 32 pos)
    (hraw : ramRead ram (sp+48#32) .w=BitVec.ofNat 32 length) (hbuf : ramRead ram (sp+44#32) .w=buf)
    (hi : start<pos) (hn : pos≤length) (hlen : length≤2048) (mem : Memory.Block B buf length) (stack : Memory.Block B sp 56) (ha : sp.toNat%4=0) :
    let g := bytes ram buf
    ∃ n d, 0<n ∧ n≤14*(pos-start) ∧ Quiet.Steps B img n ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc=0x800030fa#32 ∧
      d.get 25=BitVec.ofNat 32 (trimEnd g start pos) ∧
      (∀ r : Reg, r≠10 → r≠13 → r≠12 → r≠25 → d.get r=c.get r) ∧ d.sameCsr c := by
  let g := bytes ram buf
  obtain ⟨n,a,nlo,nhi,read,pc,previous,frame,csr⟩ := HeadOwsBackStep.contract B c ram sp buf pos length hp h2 h25 hraw hbuf (by omega) hn hlen mem stack ha
  change a.pc=(if isOws (g (pos-1)) then 0x800030ca#32 else 0x800030fa#32) at pc
  cases token : isOws (g (pos-1)) with
  | false =>
    have stop : trimEnd g start pos=pos := by rw [trimEnd];simp only [hi,token,ite_true,Bool.false_eq_true,ite_false]
    refine ⟨n,a,by omega,by omega,read,?_,?_,fun r h10 h13 h12 _ => frame r h10 h13 h12,csr⟩
    · simpa only [token,Bool.false_eq_true,ite_false] using pc
    · change a.get 25=BitVec.ofNat 32 (trimEnd g start pos)
      rw [stop];exact (frame 25 (by decide) (by decide) (by decide)).trans h25
  | true =>
    have atAdvance : a.pc=0x800030ca#32 := by simpa only [token,ite_true] using pc
    obtain ⟨d,advance,pc2,index,frame2,csr2⟩ := HeadOwsBackAdvance.contract B a ram start pos atAdvance
      ((frame 15 (by decide) (by decide) (by decide)).trans h15) previous hi (by omega)
    have source (r : Reg) (h10 : r≠10) (h13 : r≠13) (h12 : r≠12) (h25 : r≠25) : d.get r=c.get r :=
      (frame2 r h25).trans (frame r h10 h13 h12)
    have next : trimEnd g start pos=trimEnd g start (pos-1) := by rw [trimEnd];simp only [hi,token,ite_true]
    by_cases more : start<pos-1
    · have atLoop : d.pc=0x800030d0#32 := by simpa [show start≠pos-1 by omega] using pc2
      obtain ⟨rest,e,positive,bound,tail,endPC,result,frame3,csr3⟩ := contract B d ram sp buf start (pos-1) length atLoop
        ((source 2 (by decide) (by decide) (by decide) (by decide)).trans h2) ((source 15 (by decide) (by decide) (by decide) (by decide)).trans h15)
        index hraw hbuf more (by omega) hlen mem stack ha
      refine ⟨n+2+rest,e,by omega,by omega,(read.trans advance).trans tail,endPC,?_,?_,csr3.trans (csr2.trans csr)⟩
      · change e.get 25=BitVec.ofNat 32 (trimEnd g start pos)
        rw [next];exact result
      · intro r h10 h13 h12 h25
        exact (frame3 r h10 h13 h12 h25).trans (source r h10 h13 h12 h25)
    · have last : start=pos-1 := by omega
      have atFinish : d.pc=0x800030f8#32 := by simpa only [last,ite_true] using pc2
      obtain ⟨e,finish,endPC,result,frame3,csr3⟩ := HeadOwsBackFinish.contract B d ram (BitVec.ofNat 32 start)
        ((source 15 (by decide) (by decide) (by decide) (by decide)).trans h15) atFinish
      have done : trimEnd g start pos=start := by
        rw [next,←last,trimEnd];simp
      refine ⟨n+2+1,e,by omega,by omega,(read.trans advance).trans finish,endPC,?_,?_,csr3.trans (csr2.trans csr)⟩
      · change e.get 25=BitVec.ofNat 32 (trimEnd g start pos)
        rw [done];exact result
      · intro r h10 h13 h12 h25
        exact (frame3 r h25).trans (source r h10 h13 h12 h25)
termination_by pos
 decreasing_by omega
end E5R.Thermostat.HeadOwsBackScan
