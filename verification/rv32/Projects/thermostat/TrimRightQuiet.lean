-- Generated stronger trace proofs; Lean checks every decoded-instruction side condition.
import Projects.thermostat.TrimRight
import Projects.thermostat.QuietDet
import Projects.thermostat.RamRunQuiet
import Projects.thermostat.TrimFlowQuiet
import Projects.thermostat.TrimRightStopQuiet
import Projects.thermostat.TrimRightTurnQuiet
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
open E5R E5R.Thermostat
namespace E5R.Thermostat.TrimRight
theorem loop_quiet (B : Board) (c : Core) (ram : Word → BitVec 8) (p : Word) (ys : List (BitVec 8))
    (hs : Bytes.Span B ram p ys.reverse) (hn : 0 < ys.length)
    (hp : c.pc = 0x8000211a#32) (h11 : c.get 11 = p+BitVec.ofNat 32 (ys.length-1))
    (h9 : c.get 9 = BitVec.ofNat 32 ys.length)
    (h12 : c.get 12 = 23#32) (h13 : c.get 13 = 0x80001b#32) :
    ∃ d k, k ≤ 9*ys.length+6 ∧ Quiet.Steps B img k ⟨c,ram⟩ ⟨d,ram⟩ ∧
      d.pc = (if TrimMath.left ys = [] then 0x80002134#32 else 0x80001fb4#32) ∧
      d.get 9 = BitVec.ofNat 32 (TrimMath.left ys).length ∧
      (∀ r : Reg, r ≠ 9 → r ≠ 11 → r ≠ 14 → d.get r = c.get r) ∧ d.sameCsr c := by
  induction ys generalizing c with
  | nil => simp at hn
  | cons b bs ih =>
    have hs' : Bytes.Span B ram p (bs.reverse++[b]) := by simpa using hs
    have hm : B.inRam (p+BitVec.ofNat 32 bs.length) 1 = true := by
      simpa using hs'.memory ⟨bs.length,by simp⟩
    have hb : ram (p+BitVec.ofNat 32 bs.length) = b := by
      have hh := hs'.bytes ⟨bs.length,by simp⟩
      change ram (p+BitVec.ofNat 32 bs.length) = (bs.reverse++[b])[bs.length] at hh
      rw [List.getElem_append_right (by simp)] at hh
      simpa using hh
    have hptr : c.get 11 = p+BitVec.ofNat 32 bs.length := by simpa using h11
    cases hw : TrimMath.white b with
    | false =>
      obtain ⟨d,k,hk,ht,hpc,hr,hcsr⟩ := E5R.Thermostat.TrimRightStop.contract_quiet B c ram _ b hp hptr h12 h13 hm hb hw
      have hl : TrimMath.left (b::bs) = b::bs := by simp [TrimMath.left,List.dropWhile_cons,hw]
      refine ⟨d,k,by simp only [List.length_cons];omega,ht,?_,?_,?_,hcsr⟩
      · simpa only [hl,List.cons_ne_nil,ite_false] using hpc
      · rw [hl,hr 9 (by decide),h9]
      · intro r h1 h2 h3;exact hr r h3
    | true =>
      have hl : TrimMath.left (b::bs) = TrimMath.left bs := by simp [TrimMath.left,List.dropWhile_cons,hw]
      obtain ⟨d,ht,hpc,hcnt,hptr',hr,hcsr⟩ := E5R.Thermostat.TrimRightTurn.turn_quiet B c ram _ b (bs.length+1) (by omega)
        (by simpa using hs.length) hp hptr h9 h12 h13 hm hb hw
      cases bs with
      | nil =>
        refine ⟨d,9,by simp,ht,?_,?_,(fun r h1 h2 h3 => hr r h2 h1 h3),hcsr⟩
        · rw [hl];simpa [TrimMath.left] using hpc
        · rw [hl];simpa [TrimMath.left] using hcnt
      | cons b' bs' =>
        have hs0 : Bytes.Span B ram p (b'::bs').reverse := Bytes.left_part hs'
        have heq : (p+BitVec.ofNat 32 (b'::bs').length)+0xffffffff#32 =
            p+BitVec.ofNat 32 ((b'::bs').length-1) := by
          have hn0 : (b'::bs').length = ((b'::bs').length-1)+1 := by simp
          have hh : BitVec.ofNat 32 (b'::bs').length+0xffffffff#32 = BitVec.ofNat 32 ((b'::bs').length-1) := by
            calc
              _ = (BitVec.ofNat 32 ((b'::bs').length-1)+1#32)+0xffffffff#32 := by
                exact congrArg (fun x : Word => x+0xffffffff#32) (by rw [←BitVec.ofNat_add];exact congrArg (BitVec.ofNat 32) hn0)
              _ = _ := by rw [BitVec.add_assoc,show 1#32+0xffffffff#32 = 0#32 by decide +kernel,BitVec.add_zero]
          rw [BitVec.add_assoc,hh]
        obtain ⟨e,k,hk,he,hepc,hecnt,her,hecsr⟩ := ih d hs0 (by simp) (by simpa using hpc)
          (hptr'.trans heq) (by simpa using hcnt)
          ((hr 12 (by decide) (by decide) (by decide)).trans h12)
          ((hr 13 (by decide) (by decide) (by decide)).trans h13)
        refine ⟨e,9+k,by simp only [List.length_cons] at hk ⊢;omega,ht.trans he,?_,?_,?_,hecsr.trans hcsr⟩
        · simpa only [hl] using hepc
        · simpa only [hl] using hecnt
        · intro r h1 h2 h3;exact (her r h1 h2 h3).trans (hr r h2 h1 h3)

end E5R.Thermostat.TrimRight
namespace E5R.Thermostat.TrimRight
theorem contract_quiet (B : Board) (c : Core) (ram : Word → BitVec 8) (p : Word) (xs : List (BitVec 8))
    (hs : Bytes.Span B ram p xs) (hn : 0 < xs.length)
    (hp : c.pc = 0x8000211a#32) (h11 : c.get 11 = p+BitVec.ofNat 32 (xs.length-1))
    (h9 : c.get 9 = BitVec.ofNat 32 xs.length)
    (h12 : c.get 12 = 23#32) (h13 : c.get 13 = 0x80001b#32) :
    ∃ d k, k ≤ 9*xs.length+7 ∧ Quiet.Steps B img k ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc = 0x80001fb4#32 ∧
      d.get 9 = BitVec.ofNat 32 (TrimMath.left xs.reverse).length ∧
      (∀ r : Reg, r ≠ 9 → r ≠ 11 → r ≠ 14 → d.get r = c.get r) ∧ d.sameCsr c := by
  obtain ⟨e,k,hk,ht,epc,e9,eregs,ecsr⟩ := E5R.Thermostat.TrimRight.loop_quiet B c ram p xs.reverse (by simpa using hs)
    (by simpa using hn) hp (by simpa using h11) (by simpa using h9) h12 h13
  by_cases he : TrimMath.left xs.reverse = []
  · have hep : e.pc = 0x80002134#32 := by simpa only [ite_eq_left he] using epc
    have hjump := E5R.Thermostat.TrimFlow.rightEmpty_contract_quiet B e ram hep
    obtain ⟨hpc,hregs,hcsr⟩ := TrimFlow.rightEmpty_fields e
    refine ⟨TrimFlow.rightEmpty e,k+1,by simp only [List.length_reverse] at hk;omega,ht.trans hjump,hpc,?_,?_,hcsr.trans ecsr⟩
    · rw [hregs 9,e9]
    · intro r h1 h2 h3;exact (hregs r).trans (eregs r h1 h2 h3)
  · refine ⟨e,k,by simp only [List.length_reverse] at hk;omega,ht,?_,e9,eregs,ecsr⟩
    simpa only [ite_eq_right he] using epc

end E5R.Thermostat.TrimRight
