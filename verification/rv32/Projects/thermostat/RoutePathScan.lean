import Projects.thermostat.MainRelaySegment
set_option autoImplicit false
namespace E5R.Thermostat.RoutePathScan
open E5R E5R.Thermostat
abbrev Frame := MainRelaySegment.Frame

/-- First slash or the end, independently of the instruction representation. -/
def length : List (BitVec 8) → Nat
  | [] => 0
  | b::bs => if b=47#8 then 0 else 1+length bs

theorem bounded (xs : List (BitVec 8)) : length xs≤xs.length := by
  induction xs with
  | nil => exact Nat.le_refl _
  | cons b bs ih => simp only [length,List.length_cons];split <;> omega

theorem slash (B : Board) (c : Core) (ram : Word → BitVec 8) (base : Word) (i : Nat)
    (hp : c.pc=0x80002894#32) (h20 : c.get 20=base) (h23 : c.get 23=BitVec.ofNat 32 i)
    (h24 : c.get 24=47#32) (memory : B.inRam (base+BitVec.ofNat 32 i) 1=true)
    (data : ram (base+BitVec.ofNat 32 i)=47#8) :
    ∃ d, Quiet.Steps B img 3 ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc=0x800028a8#32 ∧
      (∀ r : Reg, r≠12 → d.get r=c.get r) ∧ d.sameCsr c := by
  let a := c.wr 12 (base+BitVec.ofNat 32 i) 0x80002898#32
  have sa : Quiet.Step B img ⟨c,ram⟩ ⟨a,ram⟩ := by
    refine Quiet.step_of (by rw [hp];decide) (by rw [hp];exact rt2147494036) fun o => ?_
    change Observed.interp B img o (exec c _ _) ram 0 [] []=⟨.ok a ram [],[]⟩
    rw [exec_op,h20,h23,hp];rfl
  have a12 : a.get 12=base+BitVec.ofNat 32 i := by simp [a,Core.wr_get]
  obtain ⟨b,sb,pb,b12,br,bc⟩ := QuietByteLoad.contract B img a ram 0x80002898#32 (base+BitVec.ofNat 32 i) 0#32 12 12 47#8
    rfl (by decide) (by decide) rt2147494040 a12
    (by simpa only [BitVec.add_zero] using memory) (by simpa only [BitVec.add_zero] using data)
  have bpc : b.pc=0x8000289c#32 := by simpa only [show 0x80002898#32+4#32=0x8000289c#32 by decide +kernel] using pb
  have b24 : b.get 24=47#32 := (br 24 (by decide)).trans (by simp [a,Core.wr_get,h24])
  have tested : taken .eq (b.get 12) (b.get 24)=true := by rw [b12,b24];decide +kernel
  obtain ⟨d,sd,pd,dr,dc⟩ := QuietBranch.contract B img b ram 0x8000289c#32 4#32 12#32 .eq 12 24 true
    bpc (by decide) (by decide) rt2147494044 tested
  refine ⟨d,(Quiet.Steps.single sa).trans (sb.trans sd),?_,?_,dc.trans (bc.trans (Core.sameCsr_wr c _ _ _))⟩
  · simpa only [ite_true,show 0x8000289c#32+12#32=0x800028a8#32 by decide +kernel] using pd
  · intro r nr
    exact (dr r).trans ((br r nr).trans (Core.wr_get_ne _ _ _ _ _ nr))

/-- Every nonempty arbitrary path suffix is scanned to its first slash or
    end by the real matcher loop. All lengths/content cases are included;
    the RAM allocation and index bound are independent caller obligations. -/
theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (base : Word) (i : Nat) (xs : List (BitVec 8))
    (span : Bytes.Span B ram (base+BitVec.ofNat 32 i) xs) (nonempty : xs≠[]) (bound : i+xs.length<2^32)
    (hp : c.pc=0x80002894#32) (h20 : c.get 20=base) (h23 : c.get 23=BitVec.ofNat 32 i)
    (h9 : c.get 9=BitVec.ofNat 32 (i+xs.length)) (h24 : c.get 24=47#32) :
    ∃ n d, n≤5*xs.length+1 ∧ Quiet.Steps B img n ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc=0x800028a8#32 ∧
      d.get 23=BitVec.ofNat 32 (i+length xs) ∧ Frame c d ∧ d.sameCsr c := by
  induction xs generalizing c i with
  | nil => exact False.elim (nonempty rfl)
  | cons byte xs ih =>
    by_cases firstSlash : byte=47#8
    · subst byte
      obtain ⟨d,trace,pc,regs,csr⟩ := slash B c ram base i hp h20 h23 h24 (Bytes.head span).2 (Bytes.head span).1
      refine ⟨3,d,by simp only [List.length_cons];omega,trace,pc,?_,(fun r nr _ => regs r nr),csr⟩
      simpa only [length,ite_true,Nat.add_zero] using (regs 23 (by decide)).trans h23
    · obtain ⟨a,ta,pa,ar,ac⟩ := MainRelaySegment.head B c ram base i byte hp h20 h23 h24
        (Bytes.head span).2 (Bytes.head span).1 firstSlash
      obtain ⟨e,te,pe,e23,er,ec⟩ := MainRelaySegment.advance B a ram i (i+(byte::xs).length)
        (by simp only [List.length_cons];omega) bound pa ((ar 23 (by decide)).trans h23) ((ar 9 (by decide)).trans h9)
      have frame : Frame c e := fun r n12 n23 => (er r n23).trans (ar r n12)
      cases xs with
      | nil =>
        have endPc : e.pc=0x800028a6#32 := by simpa only [List.length_cons,List.length_nil,Nat.zero_add,ite_true] using pe
        obtain ⟨d,td,pd,d23,dr,dc⟩ := MainRelaySegment.finish B e ram (BitVec.ofNat 32 (i+1)) endPc
          (by simpa only [List.length_cons,List.length_nil,Nat.zero_add] using (frame 9 (by decide) (by decide)).trans h9)
        refine ⟨6,d,by simp,((ta.trans te).trans td),pd,?_,?_,dc.trans (ec.trans ac)⟩
        · simpa only [length,firstSlash,ite_false,Nat.add_zero] using d23
        · intro r n12 n23
          exact (dr r n23).trans (frame r n12 n23)
      | cons byte' rest =>
        have more : i+1≠i+(byte::byte'::rest).length := by simp only [List.length_cons];omega
        have again : e.pc=0x80002894#32 := by simpa only [more,ite_false] using pe
        have spanNext : Bytes.Span B ram (base+BitVec.ofNat 32 (i+1)) (byte'::rest) := by
          simpa only [BitVec.add_assoc,←BitVec.ofNat_add] using Bytes.tail span
        have endEq : i+(byte::byte'::rest).length=(i+1)+(byte'::rest).length := by simp only [List.length_cons];omega
        obtain ⟨n,d,hn,trace,pc,d23,regs,csr⟩ := ih e (i+1) spanNext (by simp) (by rw [←endEq];exact bound) again
          ((frame 20 (by decide) (by decide)).trans h20) e23
          (by rw [←endEq];exact (frame 9 (by decide) (by decide)).trans h9) ((frame 24 (by decide) (by decide)).trans h24)
        refine ⟨5+n,d,by simp only [List.length_cons] at hn ⊢;omega,((ta.trans te).trans trace),pc,?_,?_,csr.trans (ec.trans ac)⟩
        · simpa only [length,firstSlash,ite_false,Nat.add_assoc] using d23
        · intro r n12 n23
          exact (regs r n12 n23).trans (frame r n12 n23)
end E5R.Thermostat.RoutePathScan
