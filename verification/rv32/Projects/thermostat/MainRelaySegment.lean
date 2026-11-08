import Projects.thermostat.MainRouterCode
import Projects.thermostat.QuietByteLoad
import Projects.thermostat.QuietBranch
import Projects.thermostat.Literal
import Projects.thermostat.Bytes
set_option autoImplicit false
namespace E5R.Thermostat.MainRelaySegment
open E5R E5R.Thermostat

def Frame (c d : Core) : Prop := ∀ r : Reg, r≠12 → r≠23 → d.get r=c.get r

private theorem head (B : Board) (c : Core) (ram : Word → BitVec 8) (base : Word) (i : Nat) (byte : BitVec 8)
    (hp : c.pc=0x80002894#32) (h20 : c.get 20=base) (h23 : c.get 23=BitVec.ofNat 32 i)
    (h24 : c.get 24=47#32) (memory : B.inRam (base+BitVec.ofNat 32 i) 1=true)
    (data : ram (base+BitVec.ofNat 32 i)=byte) (notSlash : byte≠47#8) :
    ∃ d, Quiet.Steps B img 3 ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc=0x800028a0#32 ∧
      (∀ r : Reg, r≠12 → d.get r=c.get r) ∧ d.sameCsr c := by
  let a := c.wr 12 (base+BitVec.ofNat 32 i) 0x80002898#32
  have sa : Quiet.Step B img ⟨c,ram⟩ ⟨a,ram⟩ := by
    refine Quiet.step_of (by rw [hp];decide) (by rw [hp];exact rt2147494036) fun o => ?_
    change Observed.interp B img o (exec c _ _) ram 0 [] []=⟨.ok a ram [],[]⟩
    rw [exec_op,h20,h23,hp];rfl
  have a12 : a.get 12=base+BitVec.ofNat 32 i := by simp [a,Core.wr_get]
  obtain ⟨b,sb,pb,b12,br,bc⟩ := QuietByteLoad.contract B img a ram 0x80002898#32 (base+BitVec.ofNat 32 i) 0#32 12 12 byte
    rfl (by decide) (by decide) rt2147494040 a12
    (by simpa only [BitVec.add_zero] using memory) (by simpa only [BitVec.add_zero] using data)
  have bpc : b.pc=0x8000289c#32 := by simpa only [show 0x80002898#32+4#32=0x8000289c#32 by decide +kernel] using pb
  have b24 : b.get 24=47#32 := (br 24 (by decide)).trans (by simp [a,Core.wr_get,h24])
  have tested : taken .eq (b.get 12) (b.get 24)=false := by
    rw [b12,b24]
    change decide (BitVec.ofNat 32 byte.toNat=BitVec.ofNat 32 (47#8).toNat)=false
    simpa only [Literal.byte_injective] using decide_eq_false notSlash
  obtain ⟨d,sd,pd,dr,dc⟩ := QuietBranch.contract B img b ram 0x8000289c#32 4#32 12#32 .eq 12 24 false
    bpc (by decide) (by decide) rt2147494044 tested
  refine ⟨d,(Quiet.Steps.single sa).trans (sb.trans sd),?_,?_,dc.trans (bc.trans (Core.sameCsr_wr c _ _ _))⟩
  · simpa only [Bool.false_eq_true,ite_false,show 0x8000289c#32+4#32=0x800028a0#32 by decide +kernel] using pd
  · intro r nr
    exact (dr r).trans ((br r nr).trans (Core.wr_get_ne _ _ _ _ _ nr))

private theorem advance (B : Board) (c : Core) (ram : Word → BitVec 8) (i finish : Nat)
    (inside : i<finish) (bound : finish<2^32) (hp : c.pc=0x800028a0#32)
    (h23 : c.get 23=BitVec.ofNat 32 i) (h9 : c.get 9=BitVec.ofNat 32 finish) :
    ∃ d, Quiet.Steps B img 2 ⟨c,ram⟩ ⟨d,ram⟩ ∧
      d.pc=(if i+1=finish then 0x800028a6#32 else 0x80002894#32) ∧
      d.get 23=BitVec.ofNat 32 (i+1) ∧ (∀ r : Reg, r≠23 → d.get r=c.get r) ∧ d.sameCsr c := by
  let a := c.wr 23 (BitVec.ofNat 32 (i+1)) 0x800028a2#32
  have sa : Quiet.Step B img ⟨c,ram⟩ ⟨a,ram⟩ := by
    refine Quiet.step_of (by rw [hp];decide) (by rw [hp];exact rt2147494048) fun o => ?_
    change Observed.interp B img o (exec c _ _) ram 0 [] []=⟨.ok a ram [],[]⟩
    rw [exec_opimm,h23,hp]
    change Observed.interp B img o (.done (c.wr 23 (BitVec.ofNat 32 i+1#32) 0x800028a2#32)) ram 0 [] []=_
    rw [←BitVec.ofNat_add];rfl
  have a9 : a.get 9=BitVec.ofNat 32 finish := by simp [a,Core.wr_get,h9]
  have a23 : a.get 23=BitVec.ofNat 32 (i+1) := by simp [a,Core.wr_get]
  have tested : taken .ne (BitVec.ofNat 32 finish) (BitVec.ofNat 32 (i+1))=decide (i+1≠finish) := by
    change decide (BitVec.ofNat 32 finish≠BitVec.ofNat 32 (i+1))=_
    by_cases same : i+1=finish
    · simp only [same,ne_eq,not_true_eq_false,decide_false]
    · have apart := Bytes.offset_ne 0#32 finish (i+1) bound (by omega) (Ne.symm same)
      have ne : BitVec.ofNat 32 finish≠BitVec.ofNat 32 (i+1) := by simpa only [BitVec.zero_add] using apart
      simp only [ne_eq,ne,same,not_false_eq_true,decide_true]
  obtain ⟨d,sd,pd,dr,dc⟩ := QuietBranch.contract B img a ram 0x800028a2#32 4#32 0xfffffff2#32 .ne 9 23
    (decide (i+1≠finish)) rfl (by decide) (by decide) rt2147494050 (by rw [a9,a23];exact tested)
  refine ⟨d,(Quiet.Steps.single sa).trans sd,?_,(dr 23).trans a23,?_,dc.trans (Core.sameCsr_wr c _ _ _)⟩
  · by_cases same : i+1=finish <;> simpa [same] using pd
  · intro r nr
    exact (dr r).trans (Core.wr_get_ne _ _ _ _ _ nr)

private theorem finish (B : Board) (c : Core) (ram : Word → BitVec 8) (endWord : Word)
    (hp : c.pc=0x800028a6#32) (h9 : c.get 9=endWord) :
    ∃ d, Quiet.Steps B img 1 ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc=0x800028a8#32 ∧ d.get 23=endWord ∧
      (∀ r : Reg, r≠23 → d.get r=c.get r) ∧ d.sameCsr c := by
  let d := c.wr 23 endWord 0x800028a8#32
  have step : Quiet.Step B img ⟨c,ram⟩ ⟨d,ram⟩ := by
    refine Quiet.step_of (by rw [hp];decide) (by rw [hp];exact rt2147494054) fun o => ?_
    change Observed.interp B img o (exec c _ _) ram 0 [] []=⟨.ok d ram [],[]⟩
    rw [exec_op,Core.get_zero,h9,hp]
    change Observed.interp B img o (.done (c.wr 23 (0#32+endWord) 0x800028a8#32)) ram 0 [] []=_
    rw [BitVec.zero_add];rfl
  exact ⟨d,.single step,rfl,Core.wr_get_self _ _ _ _ (by decide),fun r nr => Core.wr_get_ne _ _ _ _ _ nr,rfl⟩

/-- Actual arbitrary-length final relay segment scan. No slash, readable RAM
    and bounded indices imply exactly5*length+1 instructions and no MMIO. -/
theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (base : Word) (i : Nat) (xs : List (BitVec 8))
    (span : Bytes.Span B ram (base+BitVec.ofNat 32 i) xs) (nonempty : xs≠[])
    (bound : i+xs.length<2^32) (noSlash : ∀ b∈xs, b≠47#8)
    (hp : c.pc=0x80002894#32) (h20 : c.get 20=base) (h23 : c.get 23=BitVec.ofNat 32 i)
    (h9 : c.get 9=BitVec.ofNat 32 (i+xs.length)) (h24 : c.get 24=47#32) :
    ∃ d, Quiet.Steps B img (5*xs.length+1) ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc=0x800028a8#32 ∧
      d.get 23=BitVec.ofNat 32 (i+xs.length) ∧ Frame c d ∧ d.sameCsr c := by
  induction xs generalizing c i with
  | nil => exact False.elim (nonempty rfl)
  | cons byte xs ih =>
    have byteGood : byte≠47#8 := noSlash byte (by simp)
    obtain ⟨a,ta,pa,ar,ac⟩ := head B c ram base i byte hp h20 h23 h24
      (Bytes.head span).2 (Bytes.head span).1 byteGood
    obtain ⟨e,te,pe,e23,er,ec⟩ := advance B a ram i (i+(byte::xs).length)
      (by simp only [List.length_cons];omega) bound pa ((ar 23 (by decide)).trans h23) ((ar 9 (by decide)).trans h9)
    have frame : Frame c e := fun r n12 n23 => (er r n23).trans (ar r n12)
    cases xs with
    | nil =>
      have endPc : e.pc=0x800028a6#32 := by simpa only [List.length_cons,List.length_nil,Nat.zero_add,ite_true] using pe
      obtain ⟨d,td,pd,d23,dr,dc⟩ := finish B e ram (BitVec.ofNat 32 (i+1)) endPc (by simpa only [List.length_cons,List.length_nil,Nat.zero_add] using (frame 9 (by decide) (by decide)).trans h9)
      refine ⟨d,(ta.trans te).trans td,pd,d23,?_,dc.trans (ec.trans ac)⟩
      intro r n12 n23
      exact (dr r n23).trans (frame r n12 n23)
    | cons byte' rest =>
      have more : i+1≠i+(byte::byte'::rest).length := by simp only [List.length_cons];omega
      have again : e.pc=0x80002894#32 := by simpa only [more,ite_false] using pe
      have spanNext : Bytes.Span B ram (base+BitVec.ofNat 32 (i+1)) (byte'::rest) := by
        simpa only [BitVec.add_assoc,←BitVec.ofNat_add] using Bytes.tail span
      have endEq : i+(byte::byte'::rest).length=(i+1)+(byte'::rest).length := by simp only [List.length_cons];omega
      obtain ⟨d,td,pd,d23,dr,dc⟩ := ih e (i+1) spanNext (by simp) (by rw [←endEq];exact bound)
        (by intro b hb;exact noSlash b (List.mem_cons_of_mem byte hb)) again
        ((frame 20 (by decide) (by decide)).trans h20) e23
        (by rw [←endEq];exact (frame 9 (by decide) (by decide)).trans h9)
        ((frame 24 (by decide) (by decide)).trans h24)
      have count : 3+2+(5*(byte'::rest).length+1)=5*(byte::byte'::rest).length+1 := by simp only [List.length_cons];omega
      refine ⟨d,?_,pd,?_,?_,dc.trans (ec.trans ac)⟩
      · simpa only [count] using (ta.trans te).trans td
      · rw [endEq];exact d23
      · intro r n12 n23
        exact (dr r n12 n23).trans (frame r n12 n23)
end E5R.Thermostat.MainRelaySegment
