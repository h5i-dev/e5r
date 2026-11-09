import Projects.thermostat.RouteSliceGuards
import Projects.thermostat.HeadTargetMath
import Projects.thermostat.ReadBytes
import Projects.thermostat.QuietDet
import Projects.thermostat.Literal
set_option autoImplicit false
namespace E5R.Thermostat.RouteLiteralStages
open E5R E5R.Thermostat

/-- The real pattern-slice length and pointer operations after the guards. -/
theorem slice (B : Board) (c : Core) (ram : Word → BitVec 8) (base : Word) (first last : Nat)
    (ordered : first≤last) (bound : last≤2048) (hp : c.pc=0x800028b8#32) (h22 : c.get 22=BitVec.ofNat 32 last)
    (h11 : c.get 11=BitVec.ofNat 32 first) (h21 : c.get 21=base) :
    ∃ d, Quiet.Steps B img 2 ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc=0x800028c0#32 ∧
      d.get 12=BitVec.ofNat 32 (last-first) ∧ d.get 13=base+BitVec.ofNat 32 first ∧
      (∀ r : Reg, r≠12 → r≠13 → d.get r=c.get r) ∧ d.sameCsr c := by
  let a := c.wr 12 (BitVec.ofNat 32 (last-first)) 0x800028bc#32
  let d := a.wr 13 (base+BitVec.ofNat 32 first) 0x800028c0#32
  have sa : Quiet.Step B img ⟨c,ram⟩ ⟨a,ram⟩ := by
    refine Quiet.step_of (by rw [hp];decide) (by rw [hp];exact rt2147494072) fun o => ?_
    change Observed.interp B img o (exec c _ _) ram 0 [] []=⟨.ok a ram [],[]⟩
    rw [exec_op,h22,h11,hp]
    change Observed.interp B img o (.done (c.wr 12 (BitVec.ofNat 32 last-BitVec.ofNat 32 first) 0x800028bc#32)) ram 0 [] []=_
    rw [BitVec.ofNat_sub_ofNat_of_le last first (by omega) ordered];rfl
  have sd : Quiet.Step B img ⟨a,ram⟩ ⟨d,ram⟩ := by
    refine Quiet.step_of (by change (0x800028bc#32).getLsbD 0=false;decide) rt2147494076 fun o => ?_
    change Observed.interp B img o (exec a _ _) ram 0 [] []=⟨.ok d ram [],[]⟩
    have a21 : a.get 21=base := (Core.wr_get_ne _ _ _ _ _ (by decide)).trans h21
    have a11 : a.get 11=BitVec.ofNat 32 first := (Core.wr_get_ne _ _ _ _ _ (by decide)).trans h11
    rw [exec_op,a21,a11];rfl
  refine ⟨d,.step sa (.single sd),rfl,?_,?_,?_,rfl⟩
  · simp [d,a,Core.wr_get_ne,Core.wr_get]
  · simp [d,Core.wr_get]
  · intro r n12 n13
    exact (Core.wr_get_ne _ _ _ _ _ n13).trans (Core.wr_get_ne _ _ _ _ _ n12)

/-- Empty/one-byte segments skip placeholder detection; longer literal
    segments load their actual first byte and take the non-brace branch. -/
theorem select (B : Board) (c : Core) (ram : Word → BitVec 8) (ptr : Word) (len : Nat) (byte : BitVec 8)
    (bound : len≤2048) (hp : c.pc=0x800028c0#32) (h25 : c.get 25=1#32)
    (h12 : c.get 12=BitVec.ofNat 32 len) (h13 : c.get 13=ptr) (h26 : c.get 26=123#32)
    (readable : 2≤len → ReadBytes.Byte B img ram ptr byte) (literal : byte≠123#8) :
    ∃ n d, n≤3 ∧ Quiet.Steps B img n ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc=0x800028fa#32 ∧
      (∀ r : Reg, r≠11 → d.get r=c.get r) ∧ d.sameCsr c := by
  have cmp : taken .geu (c.get 25) (c.get 12)=decide (len≤1) := by
    rw [h25,h12];exact HeadTargetMath.geu 1 len (by decide) bound
  obtain ⟨a,branch,pa,ar,ac⟩ := QuietBranch.contract B img c ram 0x800028c0#32 4#32 58#32 .geu 25 12 (decide (len≤1))
    hp (by decide) (by decide) rt2147494080 cmp
  by_cases small : len≤1
  · have pc : a.pc=0x800028fa#32 := by simpa only [small,decide_true,ite_true,show 0x800028c0#32+58#32=0x800028fa#32 by decide +kernel] using pa
    exact ⟨1,a,by decide,branch,pc,fun r _ => ar r,ac⟩
  · have apc : a.pc=0x800028c4#32 := by simpa only [small,decide_false,Bool.false_eq_true,ite_false,show 0x800028c0#32+4#32=0x800028c4#32 by decide +kernel] using pa
    let b := a.wr 11 (BitVec.ofNat 32 byte.toNat) 0x800028c8#32
    have load : Quiet.Step B img ⟨a,ram⟩ ⟨b,ram⟩ := by
      refine QuietDet.step_of (by rw [apc];decide) (by rw [apc];exact rt2147494084) fun o => ?_
      have ptrA : a.get 13=ptr := (ar 13).trans h13
      rw [exec_load,ptrA,BitVec.add_zero,ReadBytes.load (readable (by omega)),ReadBytes.extend_byte,←Memory.ofNat_width,apc];rfl
    have b11 : b.get 11=BitVec.ofNat 32 byte.toNat := by simp [b,Core.wr_get]
    have b26 : b.get 26=123#32 := (Core.wr_get_ne _ _ _ _ _ (by decide)).trans ((ar 26).trans h26)
    have cmp : taken .ne (b.get 11) (b.get 26)=true := by
      rw [b11,b26]
      change decide (BitVec.ofNat 32 byte.toNat≠BitVec.ofNat 32 (123#8).toNat)=true
      simpa only [ne_eq,Literal.byte_injective] using decide_eq_true literal
    obtain ⟨d,skip,pd,dr,dc⟩ := QuietBranch.contract B img b ram 0x800028c8#32 4#32 50#32 .ne 11 26 true
      rfl (by decide) (by decide) rt2147494088 cmp
    refine ⟨3,d,by decide,(branch.trans (.single load)).trans skip,?_,?_,dc.trans ac⟩
    · simpa only [ite_true,show 0x800028c8#32+50#32=0x800028fa#32 by decide +kernel] using pd
    · intro r ne
      exact (dr r).trans ((Core.wr_get_ne _ _ _ _ _ ne).trans (ar r))

/-- The actual path-slice length comparison chooses the real literal
    memcmp call or the failure return, preserving all other registers/RAM. -/
theorem compare_length (B : Board) (c : Core) (ram : Word → BitVec 8) (first last plen : Nat)
    (ordered : first≤last) (bound : last≤2048) (patBound : plen≤2048)
    (hp : c.pc=0x800028fa#32) (h23 : c.get 23=BitVec.ofNat 32 last)
    (h10 : c.get 10=BitVec.ofNat 32 first) (h12 : c.get 12=BitVec.ofNat 32 plen) :
    ∃ d, Quiet.Steps B img 2 ⟨c,ram⟩ ⟨d,ram⟩ ∧
      d.pc=(if plen=last-first then 0x80002902#32 else 0x8000292a#32) ∧
      d.get 11=BitVec.ofNat 32 (last-first) ∧ (∀ r : Reg, r≠11 → d.get r=c.get r) ∧ d.sameCsr c := by
  let a := c.wr 11 (BitVec.ofNat 32 (last-first)) 0x800028fe#32
  have sub : Quiet.Step B img ⟨c,ram⟩ ⟨a,ram⟩ := by
    refine Quiet.step_of (by rw [hp];decide) (by rw [hp];exact rt2147494138) fun o => ?_
    change Observed.interp B img o (exec c _ _) ram 0 [] []=⟨.ok a ram [],[]⟩
    rw [exec_op,h23,h10,hp]
    change Observed.interp B img o (.done (c.wr 11 (BitVec.ofNat 32 last-BitVec.ofNat 32 first) 0x800028fe#32)) ram 0 [] []=_
    rw [BitVec.ofNat_sub_ofNat_of_le last first (by omega) ordered];rfl
  have a11 : a.get 11=BitVec.ofNat 32 (last-first) := Core.wr_get_self _ _ _ _ (by decide)
  have a12 : a.get 12=BitVec.ofNat 32 plen := (Core.wr_get_ne _ _ _ _ _ (by decide)).trans h12
  have cmp : taken .ne (a.get 12) (a.get 11)=decide (plen≠last-first) := by
    rw [a12,a11]
    change decide (BitVec.ofNat 32 plen≠BitVec.ofNat 32 (last-first))=_
    have injective : BitVec.ofNat 32 plen=BitVec.ofNat 32 (last-first) ↔ plen=last-first := by
      constructor
      · intro equal
        have nat := congrArg BitVec.toNat equal
        simpa only [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (show plen<2^32 by omega),Nat.mod_eq_of_lt (show last-first<2^32 by omega)] using nat
      · intro equal;rw [equal]
    simp only [ne_eq,injective]
  obtain ⟨d,branch,pc,regs,csr⟩ := QuietBranch.contract B img a ram 0x800028fe#32 4#32 44#32 .ne 12 11 (decide (plen≠last-first))
    rfl (by decide) (by decide) rt2147494142 cmp
  refine ⟨d,(Quiet.Steps.single sub).trans branch,?_,(regs 11).trans a11,fun r ne => (regs r).trans (Core.wr_get_ne _ _ _ _ _ ne),csr⟩
  by_cases equal : plen=last-first <;> simpa [equal] using pc
end E5R.Thermostat.RouteLiteralStages
