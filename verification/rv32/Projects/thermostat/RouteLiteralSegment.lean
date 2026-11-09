import Projects.thermostat.RouteLiteralStages
import Projects.thermostat.RouteLiteralCompare
set_option autoImplicit false
namespace E5R.Thermostat.RouteLiteralSegment
open E5R E5R.Thermostat

/-- One actual literal segment, including all panic guards, literal detection,
    size refusal, real memcmp and its result branch. No equality premise. -/
theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8)
    (pattern path : Word) (ps pe plen ss se slen : Nat) (xs ys : List (BitVec 8)) (first : BitVec 8)
    (patBound : ps≤pe ∧ pe≤plen ∧ plen≤2048) (pathBound : ss≤se ∧ se≤slen ∧ slen≤2048)
    (xsLength : xs.length=pe-ps) (ysLength : ys.length=se-ss)
    (xsSpan : ReadBytes.Span B img ram (pattern+BitVec.ofNat 32 ps) xs)
    (ysSpan : ReadBytes.Span B img ram (path+BitVec.ofNat 32 ss) ys)
    (literalRead : 2≤xs.length → ReadBytes.Byte B img ram (pattern+BitVec.ofNat 32 ps) first)
    (literal : first≠123#8) (hp : c.pc=0x800028a8#32)
    (h22 : c.get 22=BitVec.ofNat 32 pe) (h11 : c.get 11=BitVec.ofNat 32 ps)
    (h18 : c.get 18=BitVec.ofNat 32 plen) (h23 : c.get 23=BitVec.ofNat 32 se)
    (h10 : c.get 10=BitVec.ofNat 32 ss) (h9 : c.get 9=BitVec.ofNat 32 slen)
    (h21 : c.get 21=pattern) (h20 : c.get 20=path) (h25 : c.get 25=1#32) (h26 : c.get 26=123#32) :
    ∃ n d, n≤7*xs.length+19 ∧ Quiet.Steps B img n ⟨c,ram⟩ ⟨d,ram⟩ ∧
      d.pc=(if xs=ys then 0x80002912#32 else 0x8000292a#32) ∧
      (∀ r : Reg, r≠1 → (r.val<10 ∨ 14<r.val) → d.get r=c.get r) ∧ d.sameCsr c := by
  obtain ⟨a,ta,pa,ar,ac⟩ := RouteSliceGuards.contract B c ram ps pe plen ss se slen patBound pathBound hp h22 h11 h18 h23 h10 h9
  obtain ⟨b,tb,pb,b12,b13,br,bc⟩ := RouteLiteralStages.slice B a ram pattern ps pe patBound.1 (by omega)
    pa ((ar 22).trans h22) ((ar 11).trans h11) ((ar 21).trans h21)
  have b12' : b.get 12=BitVec.ofNat 32 xs.length := by rw [xsLength];exact b12
  have b25 : b.get 25=1#32 := (br 25 (by decide) (by decide)).trans ((ar 25).trans h25)
  have b26 : b.get 26=123#32 := (br 26 (by decide) (by decide)).trans ((ar 26).trans h26)
  obtain ⟨m,d,mb,td,pd,dr,dc⟩ := RouteLiteralStages.select B b ram (pattern+BitVec.ofNat 32 ps) xs.length first
    (by omega) pb b25 b12' b13 b26 literalRead literal
  have frameD (r : Reg) (n11 : r≠11) (n12 : r≠12) (n13 : r≠13) : d.get r=c.get r :=
    (dr r n11).trans ((br r n12 n13).trans (ar r))
  have d12 : d.get 12=BitVec.ofNat 32 xs.length := (dr 12 (by decide)).trans b12'
  obtain ⟨e,te,pePC,e11,er,ec⟩ := RouteLiteralStages.compare_length B d ram ss se xs.length pathBound.1 (by omega) (by omega)
    pd ((frameD 23 (by decide) (by decide) (by decide)).trans h23)
    ((frameD 10 (by decide) (by decide) (by decide)).trans h10) d12
  have kept (r : Reg) (n11 : r≠11) (n12 : r≠12) (n13 : r≠13) : e.get r=c.get r :=
    (er r n11).trans (frameD r n11 n12 n13)
  have csrE : e.sameCsr c := ec.trans (dc.trans (bc.trans ac))
  by_cases sizes : xs.length=ys.length
  · have epc : e.pc=0x80002902#32 := by simpa only [←ysLength,sizes,ite_true] using pePC
    have e13 : e.get 13=pattern+BitVec.ofNat 32 ps := (er 13 (by decide)).trans ((dr 13 (by decide)).trans b13)
    have e12 : e.get 12=BitVec.ofNat 32 xs.length := (er 12 (by decide)).trans d12
    obtain ⟨k,f,kb,tf,pf,f10,fr,fc⟩ := RouteLiteralCompare.contract B e ram path (BitVec.ofNat 32 ss) (pattern+BitVec.ofNat 32 ps) xs ys
      xsSpan ysSpan sizes epc ((kept 20 (by decide) (by decide) (by decide)).trans h20)
      ((kept 10 (by decide) (by decide) (by decide)).trans h10) e13 e12
    refine ⟨4+2+m+2+k,f,by omega,(((ta.trans tb).trans td).trans te).trans tf,pf,?_,fc.trans csrE⟩
    intro r n1 out
    exact (fr r n1 out).trans (kept r (by intro equal;subst r;omega) (by intro equal;subst r;omega) (by intro equal;subst r;omega))
  · have unequal : xs≠ys := by intro equal;exact sizes (congrArg List.length equal)
    refine ⟨4+2+m+2,e,by omega,((ta.trans tb).trans td).trans te,?_,?_,csrE⟩
    · simpa only [←ysLength,sizes,ite_false,unequal] using pePC
    · intro r _ out
      exact kept r (by intro equal;subst r;omega) (by intro equal;subst r;omega) (by intro equal;subst r;omega)
end E5R.Thermostat.RouteLiteralSegment
