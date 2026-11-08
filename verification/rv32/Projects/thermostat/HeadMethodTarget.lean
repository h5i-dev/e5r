import Projects.thermostat.HeadMethodStrong
import Projects.thermostat.HeadTargetChecked
namespace E5R.Thermostat.HeadMethodTarget
open E5R E5R.Thermostat HttpRequestSpec HeadLineScanSpec

def Good (g : Nat → Nat) (j : Nat) : Prop :=
  let m := scan isTchar g 0 j
  let te := scan isTargetByte g (m+1) j
  HeadMethodPrefix.Good g j ∧ HeadTargetValidationSpec.Good g m te j

instance (g : Nat → Nat) (j : Nat) : Decidable (Good g j) := by unfold Good;infer_instance

/-- Actual normal request-line prefix from the first-line boundary through
    method, target and version-width validation, with all version-entry inputs
    derived from original RAM bytes and real register setup. -/
theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (buf : Word) (j length : Nat)
    (hp : c.pc=0x80002cba#32) (h9 : c.get 9=BitVec.ofNat 32 j) (h12 : c.get 12=BitVec.ofNat 32 length)
    (h11 : c.get 11=buf) (hj : j≤length) (hlen : length≤2048) (hm : Memory.Block B buf length) :
    let g := bytes ram buf
    let m := scan isTchar g 0 j
    let te := scan isTargetByte g (m+1) j
    ∃ steps d, 0<steps ∧ steps≤37+29*j ∧ Quiet.Steps B img steps ⟨c,ram⟩ ⟨d,ram⟩ ∧
      d.pc=(if Good g j then 0x80002e20#32 else 0x80002efc#32) ∧ d.get 15=400#32 ∧
      (Good g j → d.get 5=9409#32 ∧ d.get 17=BitVec.ofNat 32 m ∧ d.get 18=BitVec.ofNat 32 te ∧
        d.get 29=BitVec.ofNat 32 (m+1) ∧ d.get 30=BitVec.ofNat 32 (te-m-1) ∧
        d.get 7=BitVec.ofNat 32 (te-1) ∧ d.get 6=buf+BitVec.ofNat 32 (te-1)) ∧
      (∀ r : Reg, r≠5 → r≠6 → r≠7 → r≠8 → r≠15 → r≠17 → r≠18 → r≠19 → r≠20 → r≠21 → r≠28 → r≠29 → r≠30 → r≠31 → d.get r=c.get r) ∧ d.sameCsr c := by
  let g := bytes ram buf
  let m := scan isTchar g 0 j
  let te := scan isTargetByte g (m+1) j
  obtain ⟨n,a,positive,bound,method,pc,status,cursor,cache,mask,frame,csr⟩ := HeadMethodStrong.contract B c ram buf j length hp h9 h12 h11 hj hlen hm
  by_cases methodGood : HeadMethodPrefix.Good g j
  · have nonempty : 0<j := by have : m<j := methodGood.2.1;omega
    have atTarget : a.pc=0x80002dc0#32 := by
      change a.pc=(if HeadMethodPrefix.Good g j then _ else _) at pc
      simpa only [methodGood,ite_true] using pc
    obtain ⟨k,d,klo,khi,target,pc2,targetCache,frame2,csr2⟩ := HeadTargetChecked.contract B a ram buf m j length atTarget (cursor nonempty)
      ((frame 9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h9) ((frame 12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h12) (cache methodGood) methodGood.2.1 hj hlen hm
    refine ⟨n+k,d,by omega,by omega,method.trans target,?_,(frame2 15 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans status,?_,?_,csr2.trans csr⟩
    · change d.pc=(if Good g j then _ else _)
      change d.pc=(if HeadTargetValidationSpec.Good g m te j then _ else _) at pc2
      simpa only [Good,methodGood,true_and] using pc2
    · intro good
      obtain ⟨endIndex,ptr,start,off,pos⟩ := targetCache good.2
      exact ⟨(frame2 5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans (mask methodGood),(frame2 17 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans (cursor nonempty),endIndex,start,off,pos,ptr⟩
    · intro r h5 h6 h7 h8 h15 h17 h18 h19 h20 h21 h28 h29 h30 h31
      exact (frame2 r h29 h30 h31 h8 h19 h7 h18 h6 h20 h21 h28).trans (frame r h5 h6 h7 h8 h15 h17 h18 h19 h28 h29 h30 h31)
  · have bad : ¬Good g j := fun good => methodGood good.1
    refine ⟨n,a,positive,by omega,method,?_,status,fun good => False.elim (bad good),?_,csr⟩
    · change a.pc=(if Good g j then _ else _)
      change a.pc=(if HeadMethodPrefix.Good g j then _ else _) at pc
      simpa only [methodGood,bad,ite_false] using pc
    · intro r h5 h6 h7 h8 h15 h17 h18 h19 h20 h21 h28 h29 h30 h31
      exact frame r h5 h6 h7 h8 h15 h17 h18 h19 h28 h29 h30 h31
end E5R.Thermostat.HeadMethodTarget
