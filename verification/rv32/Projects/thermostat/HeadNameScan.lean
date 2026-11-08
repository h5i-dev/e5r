import Projects.thermostat.HeadNameStep
import Projects.thermostat.HeadNameAdvance
import Projects.thermostat.HeadMethodSpec
namespace E5R.Thermostat.HeadNameScan
open E5R E5R.Thermostat HttpRequestSpec HeadLineScanSpec

def candidate (v : Nat) : Prop := 58≤v ∧ v<65
instance (v : Nat) : Decidable (candidate v) := inferInstanceAs (Decidable (58≤v ∧ v<65))

def endpoint (g : Nat → Nat) (k finish : Nat) : Word :=
  if k<finish ∧ candidate (g k) then 0x80003056#32 else 0x8000342c#32

theorem candidate_not_token : ∀ b : BitVec 8, isTchar b.toNat=true → ¬candidate b.toNat := by decide +kernel

/-- The complete actual header-name token scan. Exhaustion rejects at the
    last token byte; no byte beyond the bounded line is needed. -/
theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (sp buf : Word) (start pos finish length : Nat)
    (hp : c.pc=0x80002ff0#32) (state : HeadNameState.At c sp buf start pos finish length)
    (hmask : ramRead ram (sp+32#32) .w=9409#32) (stack : Memory.Block B sp 56) (ha : sp.toNat%4=0)
    (hs : start≤pos) (hi : pos<finish) (hn : finish≤length) (hlen : length≤2048) (mem : Memory.Block B buf length) :
    let g := bytes ram buf
    let k := scan isTchar g pos finish
    ∃ n d, 0<n ∧ n≤25*(finish-pos) ∧ Quiet.Steps B img n ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc=endpoint g k finish ∧
      (k<finish → HeadNameState.At d sp buf start k finish length) ∧
      (d.pc=0x80003056#32 → d.get 30=BitVec.ofNat 32 (g k)) ∧
      (∀ r : Reg, r≠30 → r≠19 → r≠12 → r≠14 → r≠10 → r≠25 → r≠31 → d.get r=c.get r) ∧ d.sameCsr c := by
  let g := bytes ram buf
  let byte := ram (buf+BitVec.ofNat 32 pos)
  obtain ⟨n,a,nlo,nhi,read,pc,aState,colon,frame,csr⟩ := HeadNameStep.contract B c ram sp buf start pos finish length hp state hmask stack ha hs hi hn hlen mem
  change a.pc=(if candidate (g pos) then 0x80003056#32 else if isTchar (g pos) ∧ pos+1≠finish then 0x80002fe0#32 else 0x8000342c#32) at pc
  cases token : isTchar (g pos) with
  | false =>
    have stop := HeadMethodSpec.stop g pos finish hi token
    change ∃ n d, _
    rw [stop]
    refine ⟨n,a,by omega,by omega,read,?_,fun _ => aState,colon,fun r h30 h19 h12 _ _ _ _ => frame r h30 h19 h12,csr⟩
    simpa only [endpoint,hi,true_and,token,Bool.false_eq_true,false_and,ite_false] using pc
  | true =>
    have notCandidate : ¬candidate (g pos) := candidate_not_token byte token
    have scanNext := HeadMethodSpec.advance g pos finish hi token
    by_cases more : pos+1<finish
    · have atAdvance : a.pc=0x80002fe0#32 := by
        simpa [notCandidate,token,show pos+1≠finish by omega] using pc
      obtain ⟨d,advance,pc2,dState,frame2,csr2⟩ := HeadNameAdvance.contract B a ram sp buf start pos finish length atAdvance aState hs more hn hlen
      have source (r : Reg) (h30 : r≠30) (h19 : r≠19) (h12 : r≠12) (h14 : r≠14) (h10 : r≠10) (h25 : r≠25) (h31 : r≠31) : d.get r=c.get r :=
        (frame2 r h14 h30 h10 h25 h31).trans (frame r h30 h19 h12)
      obtain ⟨rest,e,positive,bound,tail,endPC,state3,colon3,frame3,csr3⟩ := contract B d ram sp buf start (pos+1) finish length pc2 dState hmask stack ha (by omega) more hn hlen mem
      change ∃ n d, _
      rw [scanNext]
      refine ⟨n+6+rest,e,by omega,by omega,(read.trans advance).trans tail,endPC,state3,colon3,?_,csr3.trans (csr2.trans csr)⟩
      intro r h30 h19 h12 h14 h10 h25 h31
      exact (frame3 r h30 h19 h12 h14 h10 h25 h31).trans (source r h30 h19 h12 h14 h10 h25 h31)
    · have last : pos+1=finish := by omega
      have atReject : a.pc=0x8000342c#32 := by
        simpa only [notCandidate,token,last,ne_eq,not_true_eq_false,and_false,ite_false] using pc
      have result : scan isTchar g pos finish=finish := by rw [scanNext,last,HeadMethodSpec.end_at]
      change ∃ n d, _
      rw [result]
      refine ⟨n,a,by omega,by omega,read,?_,by intro inside;omega,?_,fun r h30 h19 h12 _ _ _ _ => frame r h30 h19 h12,csr⟩
      · simpa only [endpoint,Nat.lt_irrefl,false_and,ite_false] using atReject
      · intro impossible
        exact False.elim ((by decide : 0x8000342c#32≠0x80003056#32) (atReject.symm.trans impossible))
termination_by finish-pos
 decreasing_by omega
end E5R.Thermostat.HeadNameScan
