import Projects.thermostat.HeadValueStep
import Projects.thermostat.HeadValueAdvance
import Projects.thermostat.HeadLineScanSpec
import Projects.thermostat.QuietPrefix
namespace E5R.Thermostat.HeadValueScan
open E5R E5R.Thermostat HttpRequestSpec HeadLineScanSpec

/-- The complete ELF field_bytes loop. Rejection or the exact allIn result
    comes from actual RAM bytes, with the raw-slice panic guard derived. -/
theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (buf : Word) (pos finish length : Nat)
    (hp : c.pc=0x8000307c#32) (state : HeadValueState.At c buf pos finish length)
    (hi : pos<finish) (hn : finish≤length) (hlen : length≤2048) (mem : Memory.Block B buf length) :
    let g := bytes ram buf
    ∃ n d, 0<n ∧ n≤13*(finish-pos) ∧ Quiet.Steps B img n ⟨c,ram⟩ ⟨d,ram⟩ ∧
      d.pc=(if allIn isFieldByte g pos finish then 0x800030a4#32 else 0x8000342c#32) ∧
      (allIn isFieldByte g pos finish=true → HeadValueState.At d buf finish finish length) ∧
      (∀ r : Reg, r≠30 → r≠12 → r≠13 → r≠10 → r≠31 → d.get r=c.get r) ∧ d.sameCsr c := by
  let g := bytes ram buf
  change ∃ n d, 0<n ∧ n≤13*(finish-pos) ∧ Quiet.Steps B img n ⟨c,ram⟩ ⟨d,ram⟩ ∧
      d.pc=(if allIn isFieldByte g pos finish then 0x800030a4#32 else 0x8000342c#32) ∧
      (allIn isFieldByte g pos finish=true → HeadValueState.At d buf finish finish length) ∧
      (∀ r : Reg, r≠30 → r≠12 → r≠13 → r≠10 → r≠31 → d.get r=c.get r) ∧ d.sameCsr c
  obtain ⟨n,a,nlo,nhi,read,pc,state2,frame,csr⟩ := HeadValueStep.contract B c ram buf pos finish length hp state hi hn hlen mem
  change a.pc=(if isFieldByte (g pos) then 0x80003074#32 else 0x8000342c#32) at pc
  cases token : isFieldByte (g pos) with
  | false =>
    have result : allIn isFieldByte g pos finish=false := allIn_stop hi token
    refine ⟨n,a,by omega,by omega,read,?_,?_,fun r h30 h12 _ _ _ => frame r h30 h12,csr⟩
    · simpa only [token,result,Bool.false_eq_true,ite_false] using pc
    · change allIn isFieldByte g pos finish=true → _
      rw [result];intro impossible;contradiction
  | true =>
    have accepted : a.pc=0x80003074#32 := by simpa only [token,ite_true] using pc
    obtain ⟨d,advance,pc2,state3,frame2,csr2⟩ := HeadValueAdvance.contract B a ram buf pos finish length accepted state2 hi hn hlen
    have source (r : Reg) (h30 : r≠30) (h12 : r≠12) (h13 : r≠13) (h10 : r≠10) (h31 : r≠31) : d.get r=c.get r :=
      (frame2 r h13 h10 h31).trans (frame r h30 h12)
    have next : allIn isFieldByte g pos finish=allIn isFieldByte g (pos+1) finish := allIn_cont hi token
    by_cases more : pos+1<finish
    · have atLoop : d.pc=0x8000307c#32 := by simpa [show pos+1≠finish by omega] using pc2
      obtain ⟨rest,e,positive,bound,tail,endPC,endState,frame3,csr3⟩ := contract B d ram buf (pos+1) finish length atLoop state3 more hn hlen mem
      refine ⟨n+4+rest,e,by omega,by omega,(read.trans advance).trans tail,?_,?_,?_,csr3.trans (csr2.trans csr)⟩
      · change e.pc=(if allIn isFieldByte g pos finish then 0x800030a4#32 else 0x8000342c#32)
        rw [next];exact endPC
      · change allIn isFieldByte g pos finish=true → _
        rw [next];exact endState
      · intro r h30 h12 h13 h10 h31
        exact (frame3 r h30 h12 h13 h10 h31).trans (source r h30 h12 h13 h10 h31)
    · have last : pos+1=finish := by omega
      have result : allIn isFieldByte g pos finish=true := by rw [next];exact allIn_end (by omega)
      refine ⟨n+4,d,by omega,by omega,read.trans advance,?_,?_,source,csr2.trans csr⟩
      · simpa only [result,last,ite_true] using pc2
      · intro _;simpa only [last] using state3
termination_by finish-pos
 decreasing_by omega
end E5R.Thermostat.HeadValueScan
