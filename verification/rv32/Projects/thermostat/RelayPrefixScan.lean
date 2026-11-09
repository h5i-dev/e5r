import Projects.thermostat.RouteLiteralLeading
import Projects.thermostat.RouteScanSpec
set_option autoImplicit false
namespace E5R.Thermostat.RelayPrefixScan
open E5R E5R.Thermostat

def Frame (c d : Core) : Prop :=
  ∀ r : Reg,r≠1 → r≠10 → r≠11 → r≠12 → r≠13 → r≠14 → r≠22 → r≠23 → d.get r=c.get r

/-- Actual literal relay prefix test, including mismatch and missing final
    delimiter. Success reaches the suffix scan with derived indices7. -/
theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (path : Word) (ys : List (BitVec 8))
    (pattern : ReadBytes.Span B img ram 0x80005b9c#32 (WireSpec.ascii "/relay/{i}"))
    (span : Bytes.Span B ram (path+1#32) ys) (bound : 1+ys.length≤2048)
    (pc : c.pc=0x8000287a#32) (h21 : c.get 21=0x80005b9c#32) (h22 : c.get 22=1#32)
    (h18 : c.get 18=10#32) (h11 : c.get 11=1#32) (h20 : c.get 20=path) (h10 : c.get 10=1#32)
    (h9 : c.get 9=BitVec.ofNat 32 (1+ys.length)) (h24 : c.get 24=47#32) (h25 : c.get 25=1#32)
    (h26 : c.get 26=123#32) (h8 : c.get 8=0#32) :
    ∃ n d,n≤5*ys.length+112 ∧ Quiet.Steps B img n ⟨c,ram⟩ ⟨d,ram⟩ ∧
      (if (47#8::ys).take 7=WireSpec.ascii "/relay/" then
        d.pc=0x8000287a#32 ∧ d.get 22=7#32 ∧ d.get 11=7#32 ∧ d.get 10=7#32
       else d.pc=0x8000293a#32 ∧ d.get 10=0#32 ∧ d.get 11=0#32) ∧
      Frame c d ∧ d.sameCsr c := by
  have tailSpan : ReadBytes.Span B img ram (0x80005b9c#32+1#32) (WireSpec.ascii "relay/{i}") := ReadBytes.tail pattern
  have literalSpan : ReadBytes.Span B img ram (0x80005b9c#32+1#32) (WireSpec.ascii "relay") := by
    refine ⟨by decide,?_,?_⟩
    · have hn := tailSpan.nowrap;change (0x80005b9c#32+1#32).toNat+9≤2^32 at hn
      change (0x80005b9c#32+1#32).toNat+5≤2^32;omega
    · intro i
      have data := tailSpan.bytes ⟨i.val,by have hi := i.isLt;change i.val<5 at hi;change i.val<9;omega⟩
      have part : WireSpec.ascii "relay"=(WireSpec.ascii "relay/{i}").take 5 := rfl
      change ReadBytes.Byte B img ram (0x80005b9c#32+1#32+BitVec.ofNat 32 i.val) ((WireSpec.ascii "relay/{i}").take 5)[i.val]
      rw [List.getElem_take]
      exact data
  obtain ⟨np,a,npb,ta,pa,a22,ar,ac⟩ := RoutePatternScan.contract B c ram 0x80005b9c#32 1 (WireSpec.ascii "relay/{i}") tailSpan
    (by decide) (by decide) pc h21 h22 h18 h24
  have ae : a.get 22=6#32 := by simpa only [show RoutePathScan.length (WireSpec.ascii "relay/{i}")=5 by rfl] using a22
  obtain ⟨ns,b,nsb,tb,pb,b23,br,bc⟩ := RoutePathEntry.contract B a ram path 1 ys span bound pa
    ((ar 20 (by decide) (by decide)).trans h20) ((ar 10 (by decide) (by decide)).trans h10)
    ((ar 9 (by decide) (by decide)).trans h9) ((ar 24 (by decide) (by decide)).trans h24)
  let used := RoutePathScan.length ys
  have usedBound : used≤ys.length := RoutePathScan.bounded ys
  have keepB (r : Reg) (n12 : r≠12) (n22 : r≠22) (n23 : r≠23) : b.get r=c.get r :=
    (br r n12 n23).trans (ar r n12 n22)
  have b22 : b.get 22=6#32 := (br 22 (by decide) (by decide)).trans ae
  obtain ⟨nk,e,nkb,te,pe,er,ec⟩ := RouteLiteralSegment.contract B b ram 0x80005b9c#32 path 1 6 10 1 (1+used) (1+ys.length)
    (WireSpec.ascii "relay") (ys.take used) 114#8 ⟨by decide,by decide,by decide⟩ ⟨by omega,by omega,bound⟩
    rfl (by rw [List.length_take_of_le usedBound];omega) literalSpan (RouteLiteralTail.take_span span used usedBound)
    (fun _ => ReadBytes.head literalSpan) (by decide) pb b22
    ((keepB 11 (by decide) (by decide) (by decide)).trans h11)
    ((keepB 18 (by decide) (by decide) (by decide)).trans h18) b23
    ((keepB 10 (by decide) (by decide) (by decide)).trans h10)
    ((keepB 9 (by decide) (by decide) (by decide)).trans h9)
    ((keepB 21 (by decide) (by decide) (by decide)).trans h21)
    ((keepB 20 (by decide) (by decide) (by decide)).trans h20)
    ((keepB 25 (by decide) (by decide) (by decide)).trans h25)
    ((keepB 26 (by decide) (by decide) (by decide)).trans h26)
  have frameE : Frame c e := by
    intro r n1 n10 n11 n12 n13 n14 n22 n23
    have v10 : r.val≠10 := fun h => n10 (Fin.ext h)
    have v11 : r.val≠11 := fun h => n11 (Fin.ext h)
    have v12 : r.val≠12 := fun h => n12 (Fin.ext h)
    have v13 : r.val≠13 := fun h => n13 (Fin.ext h)
    have v14 : r.val≠14 := fun h => n14 (Fin.ext h)
    exact (er r n1 (by omega)).trans (keepB r n12 n22 n23)
  have e8 : e.get 8=0#32 := (frameE 8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h8
  have csrE : e.sameCsr c := ec.trans (bc.trans ac)
  have costP : np≤46 := npb
  have costK : nk≤57 := by change nk≤7*5+19 at nkb;omega
  by_cases equal : WireSpec.ascii "relay"=ys.take used
  · have e22 : e.get 22=6#32 := (er 22 (by decide) (by decide)).trans b22
    have e18 : e.get 18=10#32 := (er 18 (by decide) (by decide)).trans ((keepB 18 (by decide) (by decide) (by decide)).trans h18)
    have e23 : e.get 23=BitVec.ofNat 32 (1+used) := (er 23 (by decide) (by decide)).trans b23
    have e9 : e.get 9=BitVec.ofNat 32 (1+ys.length) := (er 9 (by decide) (by decide)).trans ((keepB 9 (by decide) (by decide) (by decide)).trans h9)
    have lengthUsed : used=5 := by
      have lengths := congrArg List.length equal
      rw [List.length_take_of_le usedBound] at lengths
      change 5=used at lengths;omega
    have ep : e.pc=0x80002912#32 := by simpa only [equal,ite_true] using pe
    obtain ⟨f,tf,pf,fr,fc⟩ := QuietBranch.contract B img e ram 0x80002912#32 4#32 28#32 .eq 22 18 false
      ep (by decide) (by decide) rt2147494162 (by rw [e22,e18];decide)
    have fp : f.pc=0x80002916#32 := by simpa only [Bool.false_eq_true,ite_false,show 0x80002912#32+4#32=0x80002916#32 by decide +kernel] using pf
    by_cases more : used<ys.length
    · have neq : BitVec.ofNat 32 (1+used)≠BitVec.ofNat 32 (1+ys.length) := by
        intro same;have numeric := congrArg BitVec.toNat same
        simp only [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (show 1+used<2^32 by omega),Nat.mod_eq_of_lt (show 1+ys.length<2^32 by omega)] at numeric;omega
      obtain ⟨g,tg,pg,gr,gc⟩ := QuietBranch.contract B img f ram 0x80002916#32 4#32 20#32 .eq 23 9 false
        fp (by decide) (by decide) rt2147494166 (by rw [fr 23,fr 9,e23,e9];exact decide_eq_false neq)
      have gp : g.pc=0x8000291a#32 := by simpa only [Bool.false_eq_true,ite_false,show 0x80002916#32+4#32=0x8000291a#32 by decide +kernel] using pg
      obtain ⟨d,td,pd,d11,d10,d22,dr,dc⟩ := RouteNextIndex.contract B g ram 6 6 10
        ((gr 22).trans ((fr 22).trans e22))
        (by simpa only [lengthUsed] using (gr 23).trans ((fr 23).trans e23))
        ((gr 18).trans ((fr 18).trans e18)) (by decide) (by decide) gp
      have yes : (47#8::ys).take 7=WireSpec.ascii "/relay/" := by
        obtain ⟨rest,whole,_⟩ := RouteScanSpec.relay_decompose ys equal more
        rw [whole];rfl
      refine ⟨np+ns+nk+1+1+4,d,by omega,(((((ta.trans tb).trans te).trans tf).trans tg).trans td),?_,?_,dc.trans (gc.trans (fc.trans csrE))⟩
      · simpa only [yes,ite_true] using And.intro pd (And.intro d22 (And.intro d11 d10))
      · intro r n1 n10 n11 n12 n13 n14 n22 n23
        exact (dr r n11 n10 n22).trans ((gr r).trans ((fr r).trans (frameE r n1 n10 n11 n12 n13 n14 n22 n23)))
    · have ended : used=ys.length := by omega
      obtain ⟨g,tg,pg,gr,gc⟩ := QuietBranch.contract B img f ram 0x80002916#32 4#32 20#32 .eq 23 9 true
        fp (by decide) (by decide) rt2147494166 (by rw [fr 23,fr 9,e23,e9,ended];exact decide_eq_true rfl)
      have gp : g.pc=0x8000292a#32 := by simpa only [ite_true,show 0x80002916#32+20#32=0x8000292a#32 by decide +kernel] using pg
      obtain ⟨d,td,pd,d10,d11,dr,dc⟩ := RouteLiteralEnd.failure B g ram 0#32 gp ((gr 8).trans ((fr 8).trans e8))
      have no : (47#8::ys).take 7≠WireSpec.ascii "/relay/" := by intro yes;exact more (RouteScanSpec.relay_known ys yes).2
      refine ⟨np+ns+nk+1+1+4,d,by omega,(((((ta.trans tb).trans te).trans tf).trans tg).trans td),?_,?_,dc.trans (gc.trans (fc.trans csrE))⟩
      · simpa only [no,ite_false] using And.intro pd (And.intro d10 d11)
      · intro r n1 n10 n11 n12 n13 n14 n22 n23
        exact (dr r n10 n11).trans ((gr r).trans ((fr r).trans (frameE r n1 n10 n11 n12 n13 n14 n22 n23)))
  · have ep : e.pc=0x8000292a#32 := by simpa only [equal,ite_false] using pe
    obtain ⟨d,td,pd,d10,d11,dr,dc⟩ := RouteLiteralEnd.failure B e ram 0#32 ep e8
    have no : (47#8::ys).take 7≠WireSpec.ascii "/relay/" := by intro yes;exact equal (RouteScanSpec.relay_known ys yes).1
    refine ⟨np+ns+nk+4,d,by omega,(((ta.trans tb).trans te).trans td),?_,?_,dc.trans csrE⟩
    · simpa only [no,ite_false] using And.intro pd (And.intro d10 d11)
    · intro r n1 n10 n11 n12 n13 n14 n22 n23
      exact (dr r n10 n11).trans (frameE r n1 n10 n11 n12 n13 n14 n22 n23)
end E5R.Thermostat.RelayPrefixScan
