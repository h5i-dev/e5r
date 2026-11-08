import Projects.thermostat.HeadNameNonempty
import Projects.thermostat.HeadNameColonCalc
import Projects.thermostat.HeadNameColonBounds
import Projects.thermostat.HeadNameColonByte
import Projects.thermostat.HeadNameState
namespace E5R.Thermostat.HeadNameColon
open E5R E5R.Thermostat

def memory (ram : Word → BitVec 8) (sp : Word) (start k : Nat) :=
  if k=start then ram else ramWrite ram (sp+4#32) (BitVec.ofNat 32 k) .w

theorem byte_test : ∀ b : BitVec 8,
    taken .ne (BitVec.ofNat 32 b.toNat) 58#32=decide (b.toNat≠58) := by decide +kernel

/-- Real empty-name rejection, name-end scratch store, range guard and
    exact-colon check. Character classification alone is insufficient. -/
theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (sp buf : Word) (start k finish length : Nat) (b : BitVec 8)
    (hp : c.pc=0x80003056#32) (state : HeadNameState.At c sp buf start k finish length)
    (h24 : c.get 24=BitVec.ofNat 32 start) (h26 : c.get 26=BitVec.ofNat 32 finish) (h30 : c.get 30=BitVec.ofNat 32 b.toNat)
    (hs : start≤k) (hi : k<finish) (hn : finish≤length) (hlen : length≤2048) (stack : Memory.Block B sp 56) (ha : sp.toNat%4=0) :
    ∃ n d, 1≤n ∧ n≤5 ∧ Quiet.Steps B img n ⟨c,ram⟩ ⟨d,memory ram sp start k⟩ ∧
      d.pc=(if start<k ∧ b.toNat=58 then 0x80003068#32 else 0x8000342c#32) ∧
      HeadNameState.At d sp buf start k finish length ∧
      (∀ r : Reg, r≠12 → d.get r=c.get r) ∧ d.sameCsr c := by
  have emptyTest : taken .eq (BitVec.ofNat 32 (k-start)) (0 : Word)=decide (k=start) := by
    by_cases same : k=start
    · simp [same,taken]
    · simpa only [same,decide_false] using HeadMethodMath.nonzero (k-start) (by omega) (by omega)
  obtain ⟨a,check,pc,frame,csr⟩ := HeadNameNonempty.contract B c ram (BitVec.ofNat 32 (k-start)) (decide (k=start)) hp state.count emptyTest
  by_cases same : k=start
  · refine ⟨1,a,by decide,by decide,?_,?_,HeadNameState.preserve state (fun r _ _ _ => frame r),fun r _ => frame r,csr⟩
    · simpa only [memory,same,ite_true] using check
    · simpa only [same,decide_true,ite_true,Nat.lt_irrefl,false_and,ite_false] using pc
  · have atCalc : a.pc=0x8000305a#32 := by simpa only [same,decide_false,Bool.false_eq_true,ite_false] using pc
    obtain ⟨e,store,pc2,index,frame2,csr2⟩ := HeadNameColonCalc.contract B a ram sp (BitVec.ofNat 32 start) (BitVec.ofNat 32 (k-start))
      ((frame 2).trans state.stack) ((frame 24).trans h24) ((frame 14).trans state.count) stack ha atCalc
    have mem : HeadNameColonCalc.memory ram sp (BitVec.ofNat 32 start) (BitVec.ofNat 32 (k-start))=memory ram sp start k := by
      simp only [HeadNameColonCalc.memory,HeadNameState.index start k hs,memory,same,ite_false]
    rw [mem] at store
    have idx : e.get 12=BitVec.ofNat 32 k := index.trans (HeadNameState.index start k hs)
    have ge : taken .geu (BitVec.ofNat 32 k) (BitVec.ofNat 32 finish)=false := by
      simpa only [show ¬finish≤k by omega,decide_false] using HeadTargetMath.geu k finish (by omega) (by omega)
    obtain ⟨f,bounds,pc3,frame3,csr3⟩ := HeadNameColonBounds.contract B e (memory ram sp start k) (BitVec.ofNat 32 k) (BitVec.ofNat 32 finish) false pc2 idx
      ((frame2 26 (by decide)).trans ((frame 26).trans h26)) ge
    have source (r : Reg) (h12 : r≠12) : f.get r=c.get r := (frame3 r).trans ((frame2 r h12).trans (frame r))
    obtain ⟨d,colon,pc4,frame4,csr4⟩ := HeadNameColonByte.contract B f (memory ram sp start k) (BitVec.ofNat 32 b.toNat) 58#32 (decide (b.toNat≠58))
      pc3 ((source 30 (by decide)).trans h30) ((source 28 (by decide)).trans state.constants.x28) (byte_test b)
    have finalFrame (r : Reg) (h12 : r≠12) : d.get r=c.get r := (frame4 r).trans (source r h12)
    refine ⟨5,d,by decide,by decide,((check.trans store).trans bounds).trans colon,?_,HeadNameState.preserve state (fun r _ _ h12 => finalFrame r h12),finalFrame,
      csr4.trans (csr3.trans (csr2.trans csr))⟩
    by_cases eq : b.toNat=58
    · simpa [eq,show start<k by omega] using pc4
    · simpa [eq] using pc4
end E5R.Thermostat.HeadNameColon
