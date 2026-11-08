import Projects.thermostat.PathSites
import Projects.thermostat.ByteSlices
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.PathState
open E5R E5R.Thermostat

/-- Exact actual /state comparison, including every mismatch position. The
    matched route's six-byte length is checked by the preceding dispatcher. -/
theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (p : Word) (xs : List (BitVec 8))
    (hs : Bytes.Span B ram p xs) (hlen : xs.length = 6)
    (hp : c.pc = 0x80001fce#32) (h11 : c.get 11 = p) :
    ∃ d n, n ≤ 18 ∧ DetSteps B img n ⟨c,ram⟩ ⟨d,ram⟩ ∧
      d.pc = (if xs = WireSpec.ascii "/state" then 0x80002016#32 else 0x80002194#32) ∧
      (∀ r : Reg, r ≠ 11 → r ≠ 12 → r ≠ 13 → d.get r = c.get r) ∧ d.sameCsr c := by
  have hne : xs ≠ [] := by intro h;rw [h] at hlen;contradiction
  let pre := xs.dropLast
  let last := xs.getLast hne
  have hsplit : pre++[last] = xs := List.dropLast_concat_getLast hne
  have hprelen : pre.length = 5 := by simp only [pre,List.length_dropLast,hlen]
  have hwhole : Bytes.Span B ram p (pre++[last]) := by rw [hsplit];exact hs
  have hpre : Bytes.Span B ram (p+BitVec.ofNat 32 0) pre := by
    simpa using Bytes.left_part hwhole
  obtain ⟨d,n,hn,ht,hpc,hbase,hregs,hcsr⟩ := Literal.Chain.contract PathSites.state_prefix B ram p pre c hpre
    (by simpa only [hprelen] using (show (5 : Nat) = (WireSpec.ascii "/stat").length by decide +kernel)) hp h11 (by decide) (by decide)
  by_cases he : pre = WireSpec.ascii "/stat"
  · have hdp : d.pc = 0x8000200a#32 := by simpa only [ite_eq_left he] using hpc
    have hm : B.inRam (p+5#32) 1 = true := by simpa only [hprelen] using hwhole.memory ⟨pre.length,by simp⟩
    have hb : ram (p+5#32) = last := by
      have hh := hwhole.bytes ⟨pre.length,by simp⟩
      change ram (p+BitVec.ofNat 32 pre.length) = (pre++[last])[pre.length] at hh
      rw [List.getElem_append_right (by omega)] at hh
      simpa only [hprelen,Nat.sub_self,List.getElem_cons_zero] using hh
    obtain ⟨e,heSteps,epc,_,_,eregs,ecsr⟩ := Literal.compare B img 101#8 last PathSites.state5 d ram (p+5#32) hdp
      (by change d.get 11+5#32 = _;rw [hbase]) hm hb
    have hx : xs = WireSpec.ascii "/state" ↔ last = 101#8 := by
      rw [←hsplit,he]
      change [47#8,115#8,116#8,97#8,116#8]++[last] = [47#8,115#8,116#8,97#8,116#8,101#8] ↔ _
      simp
    refine ⟨e,n+3,by change n ≤ 3*5 at hn;omega,ht.trans heSteps,?_,?_,ecsr.trans hcsr⟩
    · simpa only [hx,PathSites.state5] using epc
    · intro r h1 h2 h3
      exact (eregs r h1 h2).trans (hregs r h2 h3)
  · have hx : xs ≠ WireSpec.ascii "/state" := by
      intro hh
      apply he
      change xs.dropLast = _
      rw [hh];rfl
    refine ⟨d,n,by change n ≤ 3*5 at hn;omega,ht,?_,?_,hcsr⟩
    · simpa only [ite_eq_right he,ite_eq_right hx] using hpc
    · intro r h1 h2 h3;exact hregs r h2 h3
end E5R.Thermostat.PathState
