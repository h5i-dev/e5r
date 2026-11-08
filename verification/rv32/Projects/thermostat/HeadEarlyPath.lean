import Projects.thermostat.HeadIncompleteBranch
import Projects.thermostat.HeadEarlyFinish
import Projects.thermostat.HeadLineTerm
namespace E5R.Thermostat.HeadEarlyPath
open E5R E5R.Thermostat HttpRequestSpec

def kind (length term : Nat) : HeadEarlyFinish.Kind :=
  if term=1 then if 1024≤length then .tooLong else .incomplete else .bad

/-- First-line byte classification selects the genuine incomplete/400/414
    result and executes the full ABI return. No desired reply is postulated. -/
theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (sp : Word) (values : Reg → Word) (length term : Nat)
    (hp : c.pc=HeadLineTerm.pc term) (ht : term=1 ∨ term=2)
    (h2 : c.get 2=sp) (h10 : c.get 10=sp+4904#32)
    (h12 : c.get 12=BitVec.ofNat 32 length) (h16 : c.get 16=1024#32) (hlen : length≤2048)
    (hm : Memory.Block B sp 5312) (ha : sp.toNat%4=0) (saved : HeadSaved.At ram sp values) :
    ∃ n d, 20≤n ∧ n≤22 ∧
      Quiet.Steps B img n ⟨c,ram⟩ ⟨d,HeadEarlyFinish.memory ram sp (kind length term)⟩ ∧
      d.pc=values 1 &&& ~~~1 ∧ d.get 2=sp+384#32 ∧ HeadSaved.CoreAt d values ∧
      HeadResultView.At (HeadEarlyFinish.memory ram sp (kind length term)) (sp+4904#32) (HeadEarlyFinish.out (kind length term)) ∧
      d.sameCsr c := by
  rcases ht with rfl|rfl
  · have start : c.pc=0x80002ce6#32 := by simpa [HeadLineTerm.pc] using hp
    obtain ⟨a,branch,pc,frame,csr⟩ := HeadIncompleteBranch.contract B c ram length hlen start h12 h16
    have entry : a.pc=HeadEarlyFinish.entry (kind length 1) := by
      by_cases full : 1024≤length
      all_goals simpa only [kind,full,ite_true,ite_false,HeadEarlyFinish.entry] using pc
    obtain ⟨n,d,hlo,hi,finish,endPC,endSP,abi,csr2⟩ := HeadEarlyFinish.contract B a ram sp values (kind length 1) entry
      ((frame 2).trans h2) ((frame 10).trans h10) hm ha saved
    exact ⟨1+n,d,by omega,by omega,branch.trans finish,endPC,endSP,abi,HeadEarlyFinish.result _ _ _,csr2.trans csr⟩
  · have start : c.pc=HeadEarlyFinish.entry .bad := by simpa [HeadLineTerm.pc,HeadEarlyFinish.entry] using hp
    obtain ⟨a,setup,pc,tag,status,frame,csr⟩ := HeadReject400.contract B c ram start
    obtain ⟨b,emit,pc2,frame2,csr2⟩ := HeadResultStore.contract B a ram (sp+4904#32) 4#32 400#32
      ((frame 10 (by decide) (by decide)).trans h10) tag status
      (Memory.sub_block hm (off := 4904) (by decide) (by decide)) (Memory.word_aligned sp 1226 ha) pc
    obtain ⟨d,ret,endPC,endSP,abi,rest,csr3⟩ := HeadReturn.contract B b (HeadEarlyFinish.memory ram sp .bad) sp values pc2
      ((frame2 2).trans ((frame 2 (by decide) (by decide)).trans h2))
      (by simpa only [BitVec.add_zero] using Memory.sub_block hm (off := 0) (m := 384) (by decide) (by decide)) ha
      (HeadEarlyFinish.saved saved)
    exact ⟨20,d,by decide,by decide,(setup.trans emit).trans ret,endPC,endSP,abi,HeadEarlyFinish.result _ _ _,csr3.trans (csr2.trans csr)⟩
end E5R.Thermostat.HeadEarlyPath
