import Projects.thermostat.MainCloseScanLoop
import Projects.thermostat.MainCloseScanSetup
import Projects.thermostat.MainCloseScanFinish
set_option autoImplicit false
set_option maxRecDepth 4000
namespace E5R.Thermostat.MainCloseScan
open E5R E5R.Thermostat

def Frame (c d : Core) : Prop := ∀ r : Reg, r≠10 → r≠11 → r≠14 → r≠15 → r≠23 → d.get r=c.get r

/-- Actual scanner setup, loop and both finishing paths. The slice partition
    determines the token length and the next pointer/remaining count in RAM
    independent registers; an empty token takes its real skip continuation. -/
theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (base : Word) (xs : List (BitVec 8))
    (span : Bytes.Span B ram base xs) (positive : 0<xs.length) (hp : c.pc=0x80002584#32)
    (h22 : c.get 22=base) (h14 : c.get 14=BitVec.ofNat 32 xs.length)
    (h15 : c.get 15=base+BitVec.ofNat 32 xs.length) (h8 : c.get 8=44#32) :
    ∃ n d, n≤6*(MainCloseScanSpec.token xs).length+11 ∧ Quiet.Steps B img n ⟨c,ram⟩ ⟨d,ram⟩ ∧
      d.pc=(if MainCloseScanSpec.token xs=[] then 0x800025d4#32 else 0x800025b0#32) ∧
      d.get 22=base ∧ d.get 23=BitVec.ofNat 32 (MainCloseScanSpec.token xs).length ∧
      (d.get 11=44#32 ↔ (MainCloseScanSpec.rest xs).isSome=true) ∧
      (∀ ys, MainCloseScanSpec.rest xs=some ys →
        d.get 10=base+BitVec.ofNat 32 ((MainCloseScanSpec.token xs).length+1) ∧ d.get 14=BitVec.ofNat 32 ys.length) ∧
      Frame c d ∧ d.sameCsr c := by
  obtain ⟨u,su,pu,u23,ur,uc⟩ := MainCloseScanSetup.contract B c ram hp
  obtain ⟨n,a,nb,sa,pa,a23,a10,delimiter,ar,ac⟩ := MainCloseScanLoop.contract B u ram base 0 xs
    (by simpa only [BitVec.add_zero] using span) positive (by simpa only [Nat.zero_add] using span.length) pu
    ((ur 22 (by decide)).trans h22) u23
    (by simpa only [Nat.zero_add] using (ur 15 (by decide)).trans h15) ((ur 8 (by decide)).trans h8)
  have a14 : a.get 14=BitVec.ofNat 32 xs.length := (ar 14 (by decide) (by decide) (by decide)).trans ((ur 14 (by decide)).trans h14)
  have a22 : a.get 22=base := (ar 22 (by decide) (by decide) (by decide)).trans ((ur 22 (by decide)).trans h22)
  cases found : MainCloseScanSpec.rest xs with
  | none =>
    have token : MainCloseScanSpec.token xs=xs := MainCloseScanSpec.absent xs found
    have nonempty : MainCloseScanSpec.token xs≠[] := by rw [token];exact List.ne_nil_of_length_pos positive
    have pa' : a.pc=0x8000259c#32 := by simpa only [found,Option.isSome_none,Bool.false_eq_true,ite_false] using pa
    obtain ⟨d,sd,pd,d10,d23,dr,dc⟩ := MainCloseScanFinish.absent B a ram base xs.length positive span.length pa' a22 a14
    have frame : Frame c d := fun r n10 n11 _ _ n23 =>
      (dr r n10 n23).trans ((ar r n10 n11 n23).trans (ur r n23))
    refine ⟨1+n+3,d,by omega,(su.trans sa).trans sd,?_,(frame 22 (by decide) (by decide) (by decide) (by decide) (by decide)).trans h22,?_,?_,?_,frame,dc.trans (ac.trans uc)⟩
    · simpa only [nonempty,ite_false] using pd
    · simpa only [token] using d23
    · rw [dr 11 (by decide) (by decide)]
      simpa only [found] using delimiter
    · intro ys impossible
      contradiction
  | some ys =>
    have sizes := MainCloseScanSpec.remaining xs ys found
    have inside : (MainCloseScanSpec.token xs).length<xs.length := by omega
    have pa' : a.pc=0x800025a4#32 := by simpa only [found,Option.isSome_some,ite_true] using pa
    have count : a.get 23=BitVec.ofNat 32 (MainCloseScanSpec.token xs).length := by simpa only [Nat.zero_add] using a23
    have pointer : a.get 10=base+BitVec.ofNat 32 (MainCloseScanSpec.token xs).length := by simpa only [Nat.zero_add] using a10
    obtain ⟨d,sd,pd,d10,d14,dr,dc⟩ := MainCloseScanFinish.comma B a ram base (MainCloseScanSpec.token xs).length xs.length inside span.length pa' pointer count a14
    have frame : Frame c d := fun r n10 n11 n14 n15 n23 =>
      (dr r n10 n14 n15).trans ((ar r n10 n11 n23).trans (ur r n23))
    refine ⟨1+n+4,d,by omega,(su.trans sa).trans sd,?_,(frame 22 (by decide) (by decide) (by decide) (by decide) (by decide)).trans h22,
      (dr 23 (by decide) (by decide) (by decide)).trans count,?_,?_,frame,dc.trans (ac.trans uc)⟩
    · simpa only [List.length_eq_zero_iff] using pd
    · rw [dr 11 (by decide) (by decide) (by decide)]
      simpa only [found] using delimiter
    · intro zs same
      have equal : zs=ys := by exact (Option.some.inj same).symm
      subst zs
      refine ⟨d10,?_⟩
      have remaining : xs.length-(MainCloseScanSpec.token xs).length-1=ys.length := by omega
      simpa only [remaining] using d14
end E5R.Thermostat.MainCloseScan
