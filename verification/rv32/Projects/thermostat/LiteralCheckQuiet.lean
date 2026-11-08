-- Generated stronger trace proofs; Lean checks every decoded-instruction side condition.
import Projects.thermostat.LiteralCheck
import Projects.thermostat.QuietDet
import Projects.thermostat.RamRunQuiet
import Projects.thermostat.LiteralQuiet
import Projects.thermostat.LiteralChainQuiet
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
open E5R
namespace E5R.Thermostat.Literal
theorem check_quiet {img rd rc base reject pc litPrefix finalByte k}
    (lastSite : Site img finalByte)
    (prefixCode : Chain img rd rc base lastSite.loadPc reject k pc litPrefix)
    (lastBase : lastSite.base = base) (lastOffset : lastSite.offset = BitVec.ofNat 32 (k+litPrefix.length))
    (lastBad : lastSite.badPc = reject) (hbr : base ≠ rd) (hbc : base ≠ rc)
    (B : Board) (ram : Word → BitVec 8) (p : Word) (xs : List (BitVec 8)) (c : Core)
    (hs : Bytes.Span B ram (p+BitVec.ofNat 32 k) xs) (hlen : xs.length = litPrefix.length+1)
    (hp : c.pc = pc) (hbase : c.get base = p) :
    ∃ d n, n ≤ 3*(litPrefix.length+1) ∧ Quiet.Steps B img n ⟨c,ram⟩ ⟨d,ram⟩ ∧
      d.pc = (if xs = litPrefix++[finalByte] then lastSite.nextPc else reject) ∧
      (∀ r : Reg, r ≠ rd → r ≠ rc → r ≠ lastSite.rd → r ≠ lastSite.rc → d.get r = c.get r) ∧ d.sameCsr c := by
  have hne : xs ≠ [] := by intro h;rw [h] at hlen;simp only [List.length_nil] at hlen;omega
  let pre := xs.dropLast
  let last := xs.getLast hne
  have hsplit : pre++[last] = xs := List.dropLast_concat_getLast hne
  have hprelen : pre.length = litPrefix.length := by simp only [pre,List.length_dropLast,hlen,Nat.add_sub_cancel]
  have hwhole : Bytes.Span B ram (p+BitVec.ofNat 32 k) (pre++[last]) := by rw [hsplit];exact hs
  have hpre : Bytes.Span B ram (p+BitVec.ofNat 32 k) pre := by simpa using Bytes.left_part hwhole
  have haddr : (p+BitVec.ofNat 32 k)+BitVec.ofNat 32 pre.length = p+BitVec.ofNat 32 (k+litPrefix.length) := by
    rw [BitVec.add_assoc,←BitVec.ofNat_add,hprelen]
  obtain ⟨d,n,hn,ht,hpc,hdBase,hregs,hcsr⟩ := E5R.Thermostat.Literal.Chain.contract_quiet prefixCode B ram p pre c hpre hprelen hp hbase hbr hbc
  by_cases he : pre = litPrefix
  · have hdp : d.pc = lastSite.loadPc := by simpa only [ite_eq_left he] using hpc
    have hm : B.inRam (p+BitVec.ofNat 32 (k+litPrefix.length)) 1 = true := by
      simpa only [haddr] using hwhole.memory ⟨pre.length,by simp⟩
    have hb : ram (p+BitVec.ofNat 32 (k+litPrefix.length)) = last := by
      have hh := hwhole.bytes ⟨pre.length,by simp⟩
      change ram ((p+BitVec.ofNat 32 k)+BitVec.ofNat 32 pre.length) = (pre++[last])[pre.length] at hh
      rw [List.getElem_append_right (by omega)] at hh
      simpa only [haddr,Nat.sub_self,List.getElem_cons_zero] using hh
    obtain ⟨e,heSteps,epc,_,_,eregs,ecsr⟩ := E5R.Thermostat.Literal.compare_quiet B img finalByte last lastSite d ram _ hdp
      (by rw [lastBase,lastOffset,hdBase]) hm hb
    have hx : xs = litPrefix++[finalByte] ↔ last = finalByte := by
      rw [←hsplit,he]
      simp
    refine ⟨e,n+3,by omega,ht.trans heSteps,?_,?_,ecsr.trans hcsr⟩
    · simpa only [hx,lastBad] using epc
    · intro r h1 h2 h3 h4;exact (eregs r h3 h4).trans (hregs r h1 h2)
  · have hx : xs ≠ litPrefix++[finalByte] := by
      intro hh
      apply he
      change xs.dropLast = litPrefix
      rw [hh]
      simp
    refine ⟨d,n,by omega,ht,?_,?_,hcsr⟩
    · simpa only [ite_eq_right he,ite_eq_right hx] using hpc
    · intro r h1 h2 _ _;exact hregs r h1 h2

end E5R.Thermostat.Literal
