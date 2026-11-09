import Projects.thermostat.RoutePathScan
import Projects.thermostat.ReadBytes
import Projects.thermostat.QuietDet
set_option autoImplicit false
namespace E5R.Thermostat.RoutePatternScan
open E5R E5R.Thermostat

def Frame (c d : Core) : Prop := ∀ r : Reg, r≠12 → r≠22 → d.get r=c.get r

/-- The pattern scan uses a deterministic RAM-or-ROM byte certificate; no
    arbitrary device read or unverified ROM load is summarized here. -/
theorem head (B : Board) (c : Core) (ram : Word → BitVec 8) (base : Word) (i : Nat) (byte : BitVec 8)
    (hp : c.pc=0x8000287a#32) (h21 : c.get 21=base) (h22 : c.get 22=BitVec.ofNat 32 i)
    (h24 : c.get 24=47#32) (data : ReadBytes.Byte B img ram (base+BitVec.ofNat 32 i) byte) :
    ∃ d, Quiet.Steps B img 3 ⟨c,ram⟩ ⟨d,ram⟩ ∧
      d.pc=(if byte=47#8 then 0x8000288e#32 else 0x80002886#32) ∧
      (∀ r : Reg, r≠12 → d.get r=c.get r) ∧ d.sameCsr c := by
  let a := c.wr 12 (base+BitVec.ofNat 32 i) 0x8000287e#32
  let b := a.wr 12 (BitVec.ofNat 32 byte.toNat) 0x80002882#32
  have sa : Quiet.Step B img ⟨c,ram⟩ ⟨a,ram⟩ := by
    refine Quiet.step_of (by rw [hp];decide) (by rw [hp];exact rt2147494010) fun o => ?_
    change Observed.interp B img o (exec c _ _) ram 0 [] []=⟨.ok a ram [],[]⟩
    rw [exec_op,h21,h22,hp];rfl
  have sb : Quiet.Step B img ⟨a,ram⟩ ⟨b,ram⟩ := by
    refine QuietDet.step_of (by change (0x8000287e#32).getLsbD 0=false;decide) rt2147494014 fun o => ?_
    have addr : a.get 12=base+BitVec.ofNat 32 i := by simp [a,Core.wr_get]
    rw [exec_load,addr,BitVec.add_zero,ReadBytes.load data,ReadBytes.extend_byte,←Memory.ofNat_width];rfl
  have b12 : b.get 12=BitVec.ofNat 32 byte.toNat := by simp [b,Core.wr_get]
  have b24 : b.get 24=47#32 := by simp [b,a,Core.wr_get_ne,h24]
  have test : taken .eq (b.get 12) (b.get 24)=decide (byte=47#8) := by
    rw [b12,b24]
    change decide (BitVec.ofNat 32 byte.toNat=BitVec.ofNat 32 (47#8).toNat)=_
    simp only [Literal.byte_injective]
  obtain ⟨d,branch,pc,regs,csr⟩ := QuietBranch.contract B img b ram 0x80002882#32 4#32 12#32 .eq 12 24 (decide (byte=47#8))
    rfl (by decide) (by decide) rt2147494018 test
  refine ⟨d,((Quiet.Steps.single sa).trans (.single sb)).trans branch,?_,?_,csr⟩
  · by_cases slash : byte=47#8 <;> simpa only [slash,decide_true,decide_false,ite_true,Bool.false_eq_true,ite_false,
      show 0x80002882#32+12#32=0x8000288e#32 by decide +kernel,show 0x80002882#32+4#32=0x80002886#32 by decide +kernel] using pc
  · intro r ne
    exact (regs r).trans ((Core.wr_get_ne _ _ _ _ _ ne).trans (Core.wr_get_ne _ _ _ _ _ ne))

theorem advance (B : Board) (c : Core) (ram : Word → BitVec 8) (i finish : Nat)
    (inside : i<finish) (bound : finish<2^32) (hp : c.pc=0x80002886#32)
    (h22 : c.get 22=BitVec.ofNat 32 i) (h18 : c.get 18=BitVec.ofNat 32 finish) :
    ∃ d, Quiet.Steps B img 2 ⟨c,ram⟩ ⟨d,ram⟩ ∧
      d.pc=(if i+1=finish then 0x8000288c#32 else 0x8000287a#32) ∧
      d.get 22=BitVec.ofNat 32 (i+1) ∧ (∀ r : Reg, r≠22 → d.get r=c.get r) ∧ d.sameCsr c := by
  let a := c.wr 22 (BitVec.ofNat 32 (i+1)) 0x80002888#32
  have sa : Quiet.Step B img ⟨c,ram⟩ ⟨a,ram⟩ := by
    refine Quiet.step_of (by rw [hp];decide) (by rw [hp];exact rt2147494022) fun o => ?_
    change Observed.interp B img o (exec c _ _) ram 0 [] []=⟨.ok a ram [],[]⟩
    rw [exec_opimm,h22,hp]
    change Observed.interp B img o (.done (c.wr 22 (BitVec.ofNat 32 i+1#32) 0x80002888#32)) ram 0 [] []=_
    rw [←BitVec.ofNat_add];rfl
  have a18 : a.get 18=BitVec.ofNat 32 finish := by simp [a,Core.wr_get,h18]
  have a22 : a.get 22=BitVec.ofNat 32 (i+1) := by simp [a,Core.wr_get]
  have tested : taken .ne (BitVec.ofNat 32 finish) (BitVec.ofNat 32 (i+1))=decide (i+1≠finish) := by
    change decide (BitVec.ofNat 32 finish≠BitVec.ofNat 32 (i+1))=_
    by_cases same : i+1=finish
    · simp only [same,ne_eq,not_true_eq_false,decide_false]
    · have apart := Bytes.offset_ne 0#32 finish (i+1) bound (by omega) (Ne.symm same)
      have ne : BitVec.ofNat 32 finish≠BitVec.ofNat 32 (i+1) := by simpa only [BitVec.zero_add] using apart
      simp only [ne_eq,ne,same,not_false_eq_true,decide_true]
  obtain ⟨d,sd,pd,dr,dc⟩ := QuietBranch.contract B img a ram 0x80002888#32 4#32 0xfffffff2#32 .ne 18 22
    (decide (i+1≠finish)) rfl (by decide) (by decide) rt2147494024 (by rw [a18,a22];exact tested)
  refine ⟨d,(Quiet.Steps.single sa).trans sd,?_,(dr 22).trans a22,?_,dc.trans (Core.sameCsr_wr c _ _ _)⟩
  · by_cases same : i+1=finish <;> simpa [same] using pd
  · intro r nr
    exact (dr r).trans (Core.wr_get_ne _ _ _ _ _ nr)

theorem finish (B : Board) (c : Core) (ram : Word → BitVec 8) (endWord : Word)
    (hp : c.pc=0x8000288c#32) (h18 : c.get 18=endWord) :
    ∃ d, Quiet.Steps B img 1 ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc=0x8000288e#32 ∧ d.get 22=endWord ∧
      (∀ r : Reg, r≠22 → d.get r=c.get r) ∧ d.sameCsr c := by
  let d := c.wr 22 endWord 0x8000288e#32
  have step : Quiet.Step B img ⟨c,ram⟩ ⟨d,ram⟩ := by
    refine Quiet.step_of (by rw [hp];decide) (by rw [hp];exact rt2147494028) fun o => ?_
    change Observed.interp B img o (exec c _ _) ram 0 [] []=⟨.ok d ram [],[]⟩
    rw [exec_op,Core.get_zero,h18,hp]
    change Observed.interp B img o (.done (c.wr 22 (0#32+endWord) 0x8000288e#32)) ram 0 [] []=_
    rw [BitVec.zero_add];rfl
  exact ⟨d,.single step,rfl,Core.wr_get_self _ _ _ _ (by decide),fun r nr => Core.wr_get_ne _ _ _ _ _ nr,rfl⟩

/-- Every nonempty arbitrary path suffix is scanned to its first slash or
    end by the real matcher loop. All lengths/content cases are included;
    the RAM allocation and index bound are independent caller obligations. -/
theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (base : Word) (i : Nat) (xs : List (BitVec 8))
    (span : ReadBytes.Span B img ram (base+BitVec.ofNat 32 i) xs) (nonempty : xs≠[]) (bound : i+xs.length<2^32)
    (hp : c.pc=0x8000287a#32) (h21 : c.get 21=base) (h22 : c.get 22=BitVec.ofNat 32 i)
    (h18 : c.get 18=BitVec.ofNat 32 (i+xs.length)) (h24 : c.get 24=47#32) :
    ∃ n d, n≤5*xs.length+1 ∧ Quiet.Steps B img n ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc=0x8000288e#32 ∧
      d.get 22=BitVec.ofNat 32 (i+RoutePathScan.length xs) ∧ Frame c d ∧ d.sameCsr c := by
  induction xs generalizing c i with
  | nil => exact False.elim (nonempty rfl)
  | cons byte xs ih =>
    by_cases firstSlash : byte=47#8
    · subst byte
      obtain ⟨d,trace,pc,regs,csr⟩ := head B c ram base i 47#8 hp h21 h22 h24 (ReadBytes.head span)
      have pc' : d.pc=0x8000288e#32 := by simpa only [ite_true] using pc
      refine ⟨3,d,by simp only [List.length_cons];omega,trace,pc',?_,(fun r nr _ => regs r nr),csr⟩
      simpa only [RoutePathScan.length,ite_true,Nat.add_zero] using (regs 22 (by decide)).trans h22
    · obtain ⟨a,ta,pa0,ar,ac⟩ := head B c ram base i byte hp h21 h22 h24 (ReadBytes.head span)
      have pa : a.pc=0x80002886#32 := by simpa only [firstSlash,ite_false] using pa0
      obtain ⟨e,te,pe,e22,er,ec⟩ := advance B a ram i (i+(byte::xs).length)
        (by simp only [List.length_cons];omega) bound pa ((ar 22 (by decide)).trans h22) ((ar 18 (by decide)).trans h18)
      have frame : Frame c e := fun r n12 n23 => (er r n23).trans (ar r n12)
      cases xs with
      | nil =>
        have endPc : e.pc=0x8000288c#32 := by simpa only [List.length_cons,List.length_nil,Nat.zero_add,ite_true] using pe
        obtain ⟨d,td,pd,d22,dr,dc⟩ := finish B e ram (BitVec.ofNat 32 (i+1)) endPc
          (by simpa only [List.length_cons,List.length_nil,Nat.zero_add] using (frame 18 (by decide) (by decide)).trans h18)
        refine ⟨6,d,by simp,((ta.trans te).trans td),pd,?_,?_,dc.trans (ec.trans ac)⟩
        · simpa only [RoutePathScan.length,firstSlash,ite_false,Nat.add_zero] using d22
        · intro r n12 n23
          exact (dr r n23).trans (frame r n12 n23)
      | cons byte' rest =>
        have more : i+1≠i+(byte::byte'::rest).length := by simp only [List.length_cons];omega
        have again : e.pc=0x8000287a#32 := by simpa only [more,ite_false] using pe
        have spanNext : ReadBytes.Span B img ram (base+BitVec.ofNat 32 (i+1)) (byte'::rest) := by
          simpa only [BitVec.add_assoc,←BitVec.ofNat_add] using ReadBytes.tail span
        have endEq : i+(byte::byte'::rest).length=(i+1)+(byte'::rest).length := by simp only [List.length_cons];omega
        obtain ⟨n,d,hn,trace,pc,d22,regs,csr⟩ := ih e (i+1) spanNext (by simp) (by rw [←endEq];exact bound) again
          ((frame 21 (by decide) (by decide)).trans h21) e22
          (by rw [←endEq];exact (frame 18 (by decide) (by decide)).trans h18) ((frame 24 (by decide) (by decide)).trans h24)
        refine ⟨5+n,d,by simp only [List.length_cons] at hn ⊢;omega,((ta.trans te).trans trace),pc,?_,?_,csr.trans (ec.trans ac)⟩
        · simpa only [RoutePathScan.length,firstSlash,ite_false,Nat.add_assoc] using d22
        · intro r n12 n23
          exact (regs r n12 n23).trans (frame r n12 n23)
end E5R.Thermostat.RoutePatternScan
