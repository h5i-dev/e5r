import Projects.thermostat.RouteLiteralTail
import Projects.thermostat.RouteNextIndex
set_option autoImplicit false
namespace E5R.Thermostat.RouteLiteralLeading
open E5R E5R.Thermostat

theorem nonzero (n : Nat) (positive : 0<n) (bound : n≤2048) : BitVec.ofNat 32 n≠0#32 := by
  intro equal
  have hn := congrArg BitVec.toNat equal
  simp only [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (show n<2^32 by omega)] at hn
  omega

/-- Actual leading empty segments for slash-prefixed literal paths. The empty
    comparison is executed through the real memcmp, then indices advance. -/
theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8)
    (pattern path : Word) (first : BitVec 8) (rest ys : List (BitVec 8)) (count : Word)
    (patSpan : ReadBytes.Span B img ram pattern (47#8::first::rest))
    (pathSpan : Bytes.Span B ram path (47#8::ys))
    (patBound : (47#8::first::rest).length≤2048) (pathBound : (47#8::ys).length≤2048)
    (hp : c.pc=0x80002876#32) (h21 : c.get 21=pattern) (h22 : c.get 22=0#32)
    (h18 : c.get 18=BitVec.ofNat 32 (47#8::first::rest).length) (h11 : c.get 11=0#32)
    (h20 : c.get 20=path) (h10 : c.get 10=0#32) (h9 : c.get 9=BitVec.ofNat 32 (47#8::ys).length)
    (h24 : c.get 24=47#32) (h25 : c.get 25=1#32) (h26 : c.get 26=123#32) :
    ∃ n d, n≤5*(47#8::ys).length+32 ∧ Quiet.Steps B img n ⟨c,ram⟩ ⟨d,ram⟩ ∧
      d.pc=0x8000287a#32 ∧ d.get 22=1#32 ∧ d.get 11=1#32 ∧ d.get 10=1#32 ∧ d.get 23=0#32 ∧
      (∀ r : Reg, r≠1 → r≠22 → r≠23 → (r.val<10 ∨ 14<r.val) → d.get r=c.get r) ∧ d.sameCsr c := by
  have pnonzero := nonzero _ (by simp) patBound
  have test : taken .eq (c.get 18) (c.get 0)=false := by rw [h18,Core.get_zero];exact decide_eq_false pnonzero
  obtain ⟨a,ta,pa,ar,ac⟩ := QuietBranch.contract B img c ram 0x80002876#32 4#32 24#32 .eq 18 0 false
    hp (by decide) (by decide) rt2147494006 test
  have ap : a.pc=0x8000287a#32 := by simpa only [Bool.false_eq_true,ite_false,show 0x80002876#32+4#32=0x8000287a#32 by decide +kernel] using pa
  have headAt : ReadBytes.Byte B img ram (pattern+BitVec.ofNat 32 0) 47#8 := by simpa using ReadBytes.head patSpan
  obtain ⟨b,tb,pb,br,bc⟩ := RoutePatternScan.head B a ram pattern 0 47#8 ap ((ar 21).trans h21)
    ((ar 22).trans h22) ((ar 24).trans h24) headAt
  have bp : b.pc=0x8000288e#32 := by simpa only [ite_true] using pb
  have keepB (r : Reg) (n12 : r≠12) : b.get r=c.get r := (br r n12).trans (ar r)
  have pathSpan' : Bytes.Span B ram (path+BitVec.ofNat 32 0) (47#8::ys) := by simpa using pathSpan
  obtain ⟨ns,e,nsb,te,pe,e23,er,ec⟩ := RoutePathEntry.contract B b ram path 0 (47#8::ys) pathSpan' (by simpa using pathBound) bp
    ((keepB 20 (by decide)).trans h20) ((keepB 10 (by decide)).trans h10)
    (by simpa only [Nat.zero_add] using (keepB 9 (by decide)).trans h9) ((keepB 24 (by decide)).trans h24)
  have e23' : e.get 23=0#32 := by simpa only [RoutePathScan.length,ite_true,Nat.add_zero] using e23
  have keepE (r : Reg) (n12 : r≠12) (n23 : r≠23) : e.get r=c.get r := (er r n12 n23).trans (keepB r n12)
  have emptyP : ReadBytes.Span B img ram (pattern+BitVec.ofNat 32 0) [] := ReadBytes.of_ram (Bytes.empty _ _ _)
  have emptyS : ReadBytes.Span B img ram (path+BitVec.ofNat 32 0) [] := ReadBytes.of_ram (Bytes.empty _ _ _)
  obtain ⟨nk,f,nkb,tf,pf,fr,fc⟩ := RouteLiteralSegment.contract B e ram pattern path 0 0 (47#8::first::rest).length
    0 0 (47#8::ys).length [] [] 0#8 ⟨by omega,by omega,patBound⟩ ⟨by omega,by omega,pathBound⟩
    rfl rfl emptyP emptyS (by simp) (by decide) pe
    ((keepE 22 (by decide) (by decide)).trans h22) ((keepE 11 (by decide) (by decide)).trans h11)
    ((keepE 18 (by decide) (by decide)).trans h18) e23'
    ((keepE 10 (by decide) (by decide)).trans h10) ((keepE 9 (by decide) (by decide)).trans h9)
    ((keepE 21 (by decide) (by decide)).trans h21) ((keepE 20 (by decide) (by decide)).trans h20)
    ((keepE 25 (by decide) (by decide)).trans h25) ((keepE 26 (by decide) (by decide)).trans h26)
  have fp : f.pc=0x80002912#32 := by simpa only [ite_true] using pf
  have f22 : f.get 22=0#32 := (fr 22 (by decide) (by decide)).trans ((keepE 22 (by decide) (by decide)).trans h22)
  have f18 : f.get 18=BitVec.ofNat 32 (47#8::first::rest).length := (fr 18 (by decide) (by decide)).trans ((keepE 18 (by decide) (by decide)).trans h18)
  have f23 : f.get 23=0#32 := (fr 23 (by decide) (by decide)).trans e23'
  have f9 : f.get 9=BitVec.ofNat 32 (47#8::ys).length := (fr 9 (by decide) (by decide)).trans ((keepE 9 (by decide) (by decide)).trans h9)
  have patMore : taken .eq (f.get 22) (f.get 18)=false := by rw [f22,f18];exact decide_eq_false (Ne.symm pnonzero)
  obtain ⟨g,tg,pg,gr,gc⟩ := QuietBranch.contract B img f ram 0x80002912#32 4#32 28#32 .eq 22 18 false
    fp (by decide) (by decide) rt2147494162 patMore
  have gp : g.pc=0x80002916#32 := by simpa only [Bool.false_eq_true,ite_false,show 0x80002912#32+4#32=0x80002916#32 by decide +kernel] using pg
  have pathMore : taken .eq (g.get 23) (g.get 9)=false := by
    rw [gr 23,gr 9,f23,f9];exact decide_eq_false (Ne.symm (nonzero _ (by simp) pathBound))
  obtain ⟨h,th,ph,hr,hc⟩ := QuietBranch.contract B img g ram 0x80002916#32 4#32 20#32 .eq 23 9 false
    gp (by decide) (by decide) rt2147494166 pathMore
  have hpc : h.pc=0x8000291a#32 := by simpa only [Bool.false_eq_true,ite_false,show 0x80002916#32+4#32=0x8000291a#32 by decide +kernel] using ph
  obtain ⟨d,td,pd,d11,d10,d22,dr,dc⟩ := RouteNextIndex.contract B h ram 0 0 (47#8::first::rest).length
    ((hr 22).trans ((gr 22).trans f22)) ((hr 23).trans ((gr 23).trans f23))
    ((hr 18).trans ((gr 18).trans f18)) (by simp) patBound hpc
  refine ⟨1+3+ns+nk+1+1+4,d,by simp only [List.length_nil,Nat.mul_zero,Nat.zero_add] at nkb;omega,
    (((((ta.trans tb).trans te).trans tf).trans tg).trans th).trans td,pd,d22,d11,d10,?_,?_,dc.trans (hc.trans (gc.trans (fc.trans (ec.trans (bc.trans ac)))))⟩
  · exact (dr 23 (by decide) (by decide) (by decide)).trans ((hr 23).trans ((gr 23).trans f23))
  · intro r n1 n22 n23 out
    exact (dr r (by intro equal;subst r;omega) (by intro equal;subst r;omega) n22).trans
      ((hr r).trans ((gr r).trans ((fr r n1 out).trans (keepE r (by intro equal;subst r;omega) n23))))
end E5R.Thermostat.RouteLiteralLeading
