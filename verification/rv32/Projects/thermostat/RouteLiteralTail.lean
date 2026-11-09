import Projects.thermostat.RoutePatternScan
import Projects.thermostat.RoutePathEntry
import Projects.thermostat.RouteLiteralSegment
import Projects.thermostat.RouteLiteralEnd
set_option autoImplicit false
namespace E5R.Thermostat.RouteLiteralTail
open E5R E5R.Thermostat

theorem noSlash_length (xs : List (BitVec 8)) (plain : ∀ b∈xs,b≠47#8) : RoutePathScan.length xs=xs.length := by
  induction xs with
  | nil => rfl
  | cons b bs ih =>
    simp only [RoutePathScan.length,ite_eq_right (plain b (by simp)),List.length_cons]
    rw [ih (fun x hx => plain x (by simp [hx]))];omega

theorem take_span {B : Board} {ram : Word → BitVec 8} {p : Word} {xs : List (BitVec 8)}
    (span : Bytes.Span B ram p xs) (n : Nat) (bound : n≤xs.length) : ReadBytes.Span B img ram p (xs.take n) := by
  have len : (xs.take n).length=n := List.length_take_of_le bound
  refine ⟨by rw [len];have := span.length;omega,by rw [len];have := span.nowrap;omega,?_⟩
  intro i
  have index : i.val<xs.length := by have := i.isLt;omega
  have data := span.bytes ⟨i.val,index⟩
  have inside := span.memory ⟨i.val,index⟩
  apply ReadBytes.Byte.ram inside
  change ram (p+BitVec.ofNat 32 i.val)=(xs.take n)[i.val]
  rw [List.getElem_take]
  exact data

/-- Final literal segment: arbitrary path suffix is scanned at the actual PCs,
    compared byte-for-byte, then simultaneous end determines the real boolean.
    This is the nonempty final segment of each fixed literal route. -/
theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8)
    (pattern path : Word) (ps ss : Nat) (first : BitVec 8) (rest ys : List (BitVec 8)) (count : Word)
    (patSpan : ReadBytes.Span B img ram (pattern+BitVec.ofNat 32 ps) (first::rest))
    (pathSpan : Bytes.Span B ram (path+BitVec.ofNat 32 ss) ys)
    (plain : ∀ b∈first::rest,b≠47#8) (literal : first≠123#8)
    (patBound : ps+(first::rest).length≤2048) (pathBound : ss+ys.length≤2048)
    (hp : c.pc=0x8000287a#32) (h21 : c.get 21=pattern) (h22 : c.get 22=BitVec.ofNat 32 ps)
    (h18 : c.get 18=BitVec.ofNat 32 (ps+(first::rest).length)) (h11 : c.get 11=BitVec.ofNat 32 ps)
    (h20 : c.get 20=path) (h10 : c.get 10=BitVec.ofNat 32 ss) (h9 : c.get 9=BitVec.ofNat 32 (ss+ys.length))
    (h24 : c.get 24=47#32) (h25 : c.get 25=1#32) (h26 : c.get 26=123#32) (h8 : c.get 8=count) :
    ∃ n d, n≤12*(first::rest).length+5*ys.length+28 ∧ Quiet.Steps B img n ⟨c,ram⟩ ⟨d,ram⟩ ∧
      d.pc=0x8000293a#32 ∧ d.get 10=(if first::rest=ys then 1#32 else 0#32) ∧ d.get 11=count ∧
      (∀ r : Reg, r≠1 → r≠22 → r≠23 → (r.val<10 ∨ 14<r.val) → d.get r=c.get r) ∧ d.sameCsr c := by
  let xs := first::rest
  let used := RoutePathScan.length ys
  have xsEq : xs=first::rest := rfl
  have xsLength : xs.length=(first::rest).length := rfl
  have xsBound : ps+xs.length≤2048 := patBound
  have usedBound : used≤ys.length := RoutePathScan.bounded ys
  obtain ⟨np,a,npb,ta,pa,a22,ar,ac⟩ := RoutePatternScan.contract B c ram pattern ps xs patSpan (by simp [xs])
    (by have := xsBound;omega) hp h21 h22 h18 h24
  have a22' : a.get 22=BitVec.ofNat 32 (ps+xs.length) := by
    simpa only [xs,noSlash_length _ plain] using a22
  obtain ⟨ns,b,nsb,tb,pb,b23,br,bc⟩ := RoutePathEntry.contract B a ram path ss ys pathSpan pathBound pa
    ((ar 20 (by decide) (by decide)).trans h20) ((ar 10 (by decide) (by decide)).trans h10)
    ((ar 9 (by decide) (by decide)).trans h9) ((ar 24 (by decide) (by decide)).trans h24)
  have keptB (r : Reg) (n12 : r≠12) (n22 : r≠22) (n23 : r≠23) : b.get r=c.get r :=
    (br r n12 n23).trans (ar r n12 n22)
  have b22 : b.get 22=BitVec.ofNat 32 (ps+xs.length) := (br 22 (by decide) (by decide)).trans a22'
  have sliceLength : (ys.take used).length=used := List.length_take_of_le usedBound
  obtain ⟨nk,e,nkb,te,pe,er,ec⟩ := RouteLiteralSegment.contract B b ram pattern path ps (ps+xs.length) (ps+xs.length)
    ss (ss+used) (ss+ys.length) xs (ys.take used) first ⟨by omega,by omega,patBound⟩ ⟨by omega,by omega,pathBound⟩
    (by omega) (by rw [sliceLength];omega) patSpan (take_span pathSpan used usedBound)
    (fun _ => ReadBytes.head patSpan) literal pb b22
    ((keptB 11 (by decide) (by decide) (by decide)).trans h11)
    ((keptB 18 (by decide) (by decide) (by decide)).trans h18) b23
    ((keptB 10 (by decide) (by decide) (by decide)).trans h10)
    ((keptB 9 (by decide) (by decide) (by decide)).trans h9)
    ((keptB 21 (by decide) (by decide) (by decide)).trans h21)
    ((keptB 20 (by decide) (by decide) (by decide)).trans h20)
    ((keptB 25 (by decide) (by decide) (by decide)).trans h25)
    ((keptB 26 (by decide) (by decide) (by decide)).trans h26)
  have csrE : e.sameCsr c := ec.trans (bc.trans ac)
  have stable (r : Reg) (n1 : r≠1) (n22 : r≠22) (n23 : r≠23) (out : r.val<10 ∨ 14<r.val) : e.get r=c.get r :=
    (er r n1 out).trans (keptB r (by intro equal;subst r;omega) n22 n23)
  have e8 : e.get 8=count := (stable 8 (by decide) (by decide) (by decide) (by decide)).trans h8
  by_cases equal : xs=ys.take used
  · have ep : e.pc=0x80002912#32 := by simpa only [equal,ite_true] using pe
    have e22 : e.get 22=BitVec.ofNat 32 (ps+xs.length) := (er 22 (by decide) (by decide)).trans b22
    have e18 : e.get 18=BitVec.ofNat 32 (ps+xs.length) :=
      (er 18 (by decide) (by decide)).trans ((keptB 18 (by decide) (by decide) (by decide)).trans h18)
    have e23 : e.get 23=BitVec.ofNat 32 (ss+used) := (er 23 (by decide) (by decide)).trans b23
    have e9 : e.get 9=BitVec.ofNat 32 (ss+ys.length) :=
      (er 9 (by decide) (by decide)).trans ((keptB 9 (by decide) (by decide) (by decide)).trans h9)
    obtain ⟨d,td,pd,d10,d11,dr,dc⟩ := RouteLiteralEnd.contract B e ram (BitVec.ofNat 32 (ps+xs.length))
      (BitVec.ofNat 32 (ss+used)) (BitVec.ofNat 32 (ss+ys.length)) count ep e22 e18 e23 e9 e8
    have iffEnd : BitVec.ofNat 32 (ss+used)=BitVec.ofNat 32 (ss+ys.length) ↔ xs=ys := by
      constructor
      · intro h
        have hn := congrArg BitVec.toNat h
        simp only [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (show ss+used<2^32 by omega),Nat.mod_eq_of_lt (show ss+ys.length<2^32 by omega)] at hn
        have whole : used=ys.length := by omega
        simpa only [whole,List.take_length] using equal
      · intro same
        have lengths := congrArg List.length equal
        rw [same,sliceLength] at lengths
        rw [lengths]
    refine ⟨np+ns+nk+5,d,by rw [xsLength] at npb nkb;omega,((ta.trans tb).trans te).trans td,pd,?_,d11,?_,dc.trans csrE⟩
    · simpa only [iffEnd] using d10
    · intro r n1 n22 n23 out
      exact (dr r (by intro equal;subst r;omega) (by intro equal;subst r;omega)).trans (stable r n1 n22 n23 out)
  · have ep : e.pc=0x8000292a#32 := by simpa only [equal,ite_false] using pe
    obtain ⟨d,td,pd,d10,d11,dr,dc⟩ := RouteLiteralEnd.failure B e ram count ep e8
    have different : xs≠ys := by
      intro same
      have noSlashY : RoutePathScan.length ys=ys.length := by rw [←same];exact noSlash_length _ plain
      apply equal
      simpa only [used,noSlashY,List.take_length] using same
    refine ⟨np+ns+nk+4,d,by rw [xsLength] at npb nkb;omega,((ta.trans tb).trans te).trans td,pd,?_,d11,?_,dc.trans csrE⟩
    · simpa only [←xsEq,different,ite_false] using d10
    · intro r n1 n22 n23 out
      exact (dr r (by intro equal;subst r;omega) (by intro equal;subst r;omega)).trans (stable r n1 n22 n23 out)
end E5R.Thermostat.RouteLiteralTail
