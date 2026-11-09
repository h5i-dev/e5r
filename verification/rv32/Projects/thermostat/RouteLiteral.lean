import Projects.thermostat.RouteLiteralBody
import Projects.thermostat.MainPathReturn
import Projects.thermostat.WordRegions
import Projects.thermostat.ViewFrame
set_option autoImplicit false
namespace E5R.Thermostat.RouteLiteral
open E5R E5R.Thermostat

/-- Complete actual matcher call, including stack saves, all scans/guards,
    real comparisons and ABI restore. Arbitrary slash-prefixed paths are
    classified from their bytes, including empty suffixes and extra slashes. -/
theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8)
    (pattern path params ret : Word) (first : BitVec 8) (rest ys : List (BitVec 8))
    (patSpan : ReadBytes.Span B img ram pattern (47#8::first::rest))
    (pathSpan : Bytes.Span B ram path (47#8::ys))
    (plain : ∀ b∈first::rest,b≠47#8) (literal : first≠123#8)
    (patBound : (47#8::first::rest).length≤2048) (pathBound : (47#8::ys).length≤2048)
    (patSeparate : WordRegions.Disjoint pattern (47#8::first::rest).length 0x80ffeb30#32 96)
    (pathSeparate : WordRegions.Disjoint path (47#8::ys).length 0x80ffeb30#32 96)
    (hp : c.pc=0x8000283a#32) (h2 : c.get 2=0x80ffeb90#32) (hret : c.get 1=ret)
    (retAligned : ret.getLsbD 0=false) (retMask : ret &&& ~~~1=ret)
    (h10 : c.get 10=pattern) (h11 : c.get 11=BitVec.ofNat 32 (47#8::first::rest).length)
    (h12 : c.get 12=path) (h13 : c.get 13=BitVec.ofNat 32 (47#8::ys).length) (h14 : c.get 14=params)
    (stack : Memory.Block B 0x80ffeb50#32 64) :
    ∃ n d, n≤12*(first::rest).length+10*ys.length+107 ∧
      Quiet.Steps B img n ⟨c,ram⟩ ⟨d,MainPathStateSave.memory ram c⟩ ∧ d.pc=ret ∧
      d.get 10=(if first::rest=ys then 1#32 else 0#32) ∧ d.get 11=0#32 ∧
      (∀ r : Reg, r∈[1, 2, 3, 4, 5, 6, 7, 8, 9, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31] → d.get r=c.get r) ∧ d.sameCsr c := by
  let after := MainPathStateSave.memory ram c
  have pathFrame : ViewFrame.Region ram after path (47#8::ys).length := by
    intro i;dsimp only [after];rw [MainPathStateSave.memory_eq];exact OuterSave.frame _ _ _ _ (pathSeparate i)
  have pathSaved : Bytes.Span B after path (47#8::ys) := ViewFrame.span pathSpan pathFrame
  have patSaved : ReadBytes.Span B img after pattern (47#8::first::rest) := by
    refine ⟨patSpan.length,patSpan.nowrap,?_⟩
    intro i;apply (patSpan.bytes i).frame
    dsimp only [after];rw [MainPathStateSave.memory_eq];exact OuterSave.frame _ _ _ _ (patSeparate i)
  obtain ⟨a,ta,pa,a2,ar,ac⟩ := MainPathStateSave.contract B c ram c rfl h2 stack hp
  obtain ⟨nb,b,nbb,tb,pb,b10,b11,br,bc⟩ := RouteLiteralBody.contract B a after pattern path params first rest ys patSaved pathSaved
    plain literal patBound pathBound pa ((ar 10 (by decide)).trans h10) ((ar 11 (by decide)).trans h11)
    ((ar 12 (by decide)).trans h12) ((ar 13 (by decide)).trans h13) ((ar 14 (by decide)).trans h14)
  have b2 : b.get 2=0x80ffeb50#32 := (br 2 (by decide) (by decide)).trans a2
  obtain ⟨d,td,pd,d1,d8,d9,d18,d19,d20,d21,d22,d23,d24,d25,d26,d27,d2,dr,dc⟩ := MainPathReturn.contract B b after ram c ret
    retAligned retMask b2 rfl hret stack pb
  have result : d.get 10=(if first::rest=ys then 1#32 else 0#32) :=
    (dr 10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans b10
  have captures : d.get 11=0#32 := (dr 11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans b11
  refine ⟨14+nb+15,d,by omega,(ta.trans tb).trans td,pd,result,captures,?_,dc.trans (bc.trans ac)⟩
  intro r member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact d1
  · exact d2.trans h2.symm
  · exact (dr 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans ((br 3 (by decide) (by decide)).trans (ar 3 (by decide)))
  · exact (dr 4 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans ((br 4 (by decide) (by decide)).trans (ar 4 (by decide)))
  · exact (dr 5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans ((br 5 (by decide) (by decide)).trans (ar 5 (by decide)))
  · exact (dr 6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans ((br 6 (by decide) (by decide)).trans (ar 6 (by decide)))
  · exact (dr 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans ((br 7 (by decide) (by decide)).trans (ar 7 (by decide)))
  · exact d8
  · exact d9
  · exact (dr 15 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans ((br 15 (by decide) (by decide)).trans (ar 15 (by decide)))
  · exact (dr 16 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans ((br 16 (by decide) (by decide)).trans (ar 16 (by decide)))
  · exact (dr 17 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans ((br 17 (by decide) (by decide)).trans (ar 17 (by decide)))
  · exact d18
  · exact d19
  · exact d20
  · exact d21
  · exact d22
  · exact d23
  · exact d24
  · exact d25
  · exact d26
  · exact d27
  · exact (dr 28 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans ((br 28 (by decide) (by decide)).trans (ar 28 (by decide)))
  · exact (dr 29 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans ((br 29 (by decide) (by decide)).trans (ar 29 (by decide)))
  · exact (dr 30 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans ((br 30 (by decide) (by decide)).trans (ar 30 (by decide)))
  · exact (dr 31 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans ((br 31 (by decide) (by decide)).trans (ar 31 (by decide)))
end E5R.Thermostat.RouteLiteral
