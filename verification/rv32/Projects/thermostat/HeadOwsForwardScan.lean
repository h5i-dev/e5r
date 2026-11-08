import Projects.thermostat.HeadOwsForwardStep
import Projects.thermostat.HeadOwsForwardAdvance
import Projects.thermostat.HeadLineScanSpec
namespace E5R.Thermostat.HeadOwsForwardScan
open E5R E5R.Thermostat HttpRequestSpec HeadLineScanSpec

def endpoint (k finish : Nat) : Word := if k<finish then 0x800030c0#32 else 0x800030f2#32

/-- The entire real leading OWS loop, preserving the exact trimmed start. -/
theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (sp buf : Word) (pos finish length : Nat)
    (hp : c.pc=0x800030a4#32) (h2 : c.get 2=sp) (h15 : c.get 15=BitVec.ofNat 32 pos) (h25 : c.get 25=BitVec.ofNat 32 (finish-pos))
    (hraw : ramRead ram (sp+48#32) .w=BitVec.ofNat 32 length) (hbuf : ramRead ram (sp+44#32) .w=buf)
    (hi : pos<finish) (hn : finish≤length) (hlen : length≤2048) (mem : Memory.Block B buf length) (stack : Memory.Block B sp 56) (ha : sp.toNat%4=0) :
    let g := bytes ram buf
    let k := scan isOws g pos finish
    ∃ n d, 0<n ∧ n≤12*(finish-pos) ∧ Quiet.Steps B img n ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc=endpoint k finish ∧
      d.get 15=BitVec.ofNat 32 k ∧ d.get 25=BitVec.ofNat 32 (finish-k) ∧
      (∀ r : Reg, r≠10 → r≠12 → r≠25 → r≠15 → d.get r=c.get r) ∧ d.sameCsr c := by
  let g := bytes ram buf
  obtain ⟨n,a,nlo,nhi,read,pc,frame,csr⟩ := HeadOwsForwardStep.contract B c ram sp buf pos length hp h2 h15 hraw hbuf (by omega) hlen mem stack ha
  change a.pc=(if isOws (g pos) then 0x8000309c#32 else 0x800030c0#32) at pc
  cases token : isOws (g pos) with
  | false =>
    have stop : scan isOws g pos finish=pos := scan_stop hi token
    change ∃ n d, _
    rw [stop]
    refine ⟨n,a,by omega,by omega,read,?_,(frame 15 (by decide) (by decide)).trans h15,(frame 25 (by decide) (by decide)).trans h25,
      fun r h10 h12 _ _ => frame r h10 h12,csr⟩
    simpa only [endpoint,hi,token,Bool.false_eq_true,ite_true,ite_false] using pc
  | true =>
    have atAdvance : a.pc=0x8000309c#32 := by simpa only [token,ite_true] using pc
    obtain ⟨d,advance,pc2,index,remaining,frame2,csr2⟩ := HeadOwsForwardAdvance.contract B a ram pos finish atAdvance
      ((frame 15 (by decide) (by decide)).trans h15) ((frame 25 (by decide) (by decide)).trans h25) hi (by omega)
    have source (r : Reg) (h10 : r≠10) (h12 : r≠12) (h25 : r≠25) (h15 : r≠15) : d.get r=c.get r :=
      (frame2 r h25 h15).trans (frame r h10 h12)
    have next : scan isOws g pos finish=scan isOws g (pos+1) finish := scan_cont hi token
    by_cases more : pos+1<finish
    · have atLoop : d.pc=0x800030a4#32 := by simpa [show pos+1≠finish by omega] using pc2
      obtain ⟨rest,e,positive,bound,tail,endPC,endIndex,endRemaining,frame3,csr3⟩ := contract B d ram sp buf (pos+1) finish length atLoop
        ((source 2 (by decide) (by decide) (by decide) (by decide)).trans h2) index remaining hraw hbuf more hn hlen mem stack ha
      change ∃ n d, _
      rw [next]
      refine ⟨n+3+rest,e,by omega,by omega,(read.trans advance).trans tail,endPC,endIndex,endRemaining,?_,csr3.trans (csr2.trans csr)⟩
      intro r h10 h12 h25 h15
      exact (frame3 r h10 h12 h25 h15).trans (source r h10 h12 h25 h15)
    · have last : pos+1=finish := by omega
      have done : scan isOws g pos finish=finish := by rw [next,last];exact scan_end (Nat.le_refl finish)
      change ∃ n d, _
      rw [done]
      refine ⟨n+3,d,by omega,by omega,read.trans advance,?_,?_,?_,source,csr2.trans csr⟩
      · simpa only [endpoint,Nat.lt_irrefl,last,ite_true,ite_false] using pc2
      · simpa only [last] using index
      · simpa only [last] using remaining
termination_by finish-pos
 decreasing_by omega
end E5R.Thermostat.HeadOwsForwardScan
