-- Generated stronger trace proofs; Lean checks every decoded-instruction side condition.
import Projects.thermostat.TrimLeft
import Projects.thermostat.QuietDet
import Projects.thermostat.RamRunQuiet
import Projects.thermostat.TrimHeadQuiet
import Projects.thermostat.TrimStopQuiet
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
open E5R E5R.Thermostat
namespace E5R.Thermostat.TrimLeft
theorem loop_quiet (B : Board) (c : Core) (ram : Word → BitVec 8) (p : Word) (xs : List (BitVec 8))
    (hs : Bytes.Span B ram p xs) (hn : 0 < xs.length)
    (hp : c.pc = 0x80001f90#32) (h8 : c.get 8 = p) (h9 : c.get 9 = BitVec.ofNat 32 xs.length)
    (h14 : c.get 14 = 23#32) (h15 : c.get 15 = 0x80001b#32) :
    ∃ d k, k ≤ 9*xs.length+6 ∧ Quiet.Steps B img k ⟨c,ram⟩ ⟨d,ram⟩ ∧
      d.pc = (if TrimMath.left xs = [] then 0x80001fac#32 else 0x8000210e#32) ∧
      d.get 9 = BitVec.ofNat 32 (TrimMath.left xs).length ∧
      d.get 8 = p+BitVec.ofNat 32 (xs.length-(TrimMath.left xs).length) ∧
      (∀ r : Reg, r ≠ 8 → r ≠ 9 → r ≠ 16 → d.get r = c.get r) ∧ d.sameCsr c := by
  induction xs generalizing c p with
  | nil => simp at hn
  | cons b bs ih =>
    obtain ⟨hb,hm⟩ := Bytes.head hs
    cases hw : TrimMath.white b with
    | false =>
      obtain ⟨d,k,hk,ht,hpc,hr,hcsr⟩ := E5R.Thermostat.TrimStop.contract_quiet B c ram p b hp h8 h14 h15 hm hb hw
      have hl : TrimMath.left (b::bs) = b::bs := by simp [TrimMath.left,List.dropWhile_cons,hw]
      refine ⟨d,k,by simp only [List.length_cons];omega,ht,?_,?_,?_,?_,hcsr⟩
      · simpa only [hl,List.cons_ne_nil,ite_false] using hpc
      · rw [hl,hr 9 (by decide),h9]
      · rw [hl,Nat.sub_self]
        simpa using (hr 8 (by decide)).trans h8
      · intro r h1 h2 h3;exact hr r h3
    | true =>
      have hl : TrimMath.left (b::bs) = TrimMath.left bs := by simp [TrimMath.left,List.dropWhile_cons,hw]
      obtain ⟨d,ht,hpc,hcnt,hptr,hr,hcsr⟩ := E5R.Thermostat.TrimHead.turn_quiet B c ram p b (bs.length+1) (by omega)
        (by simpa using hs.length) hp h8 h9 h14 h15 hm hb hw
      cases bs with
      | nil =>
        refine ⟨d,9,by simp,ht,?_,?_,?_,hr,hcsr⟩
        · rw [hl]
          simpa [TrimMath.left] using hpc
        · rw [hl]
          simpa [TrimMath.left] using hcnt
        · rw [hl]
          simpa [TrimMath.left] using hptr
      | cons b' bs' =>
        obtain ⟨e,k,hk,he,hepc,hecnt,heptr,her,hecsr⟩ := ih d (p+1#32) (Bytes.tail hs) (by simp)
          (by simpa using hpc) hptr (by simpa using hcnt)
          ((hr 14 (by decide) (by decide) (by decide)).trans h14)
          ((hr 15 (by decide) (by decide) (by decide)).trans h15)
        refine ⟨e,9+k,by simp only [List.length_cons] at hk ⊢;omega,ht.trans he,?_,?_,?_,?_,hecsr.trans hcsr⟩
        · simpa only [hl] using hepc
        · simpa only [hl] using hecnt
        · rw [hl,heptr,BitVec.add_assoc,←BitVec.ofNat_add]
          have hbnd := TrimMath.left_length (b'::bs')
          exact congrArg (fun n => p+BitVec.ofNat 32 n) (by simp only [List.length_cons] at hbnd ⊢;omega)
        · intro r h1 h2 h3;exact (her r h1 h2 h3).trans (hr r h1 h2 h3)

end E5R.Thermostat.TrimLeft
