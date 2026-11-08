-- Generated stronger trace proofs; Lean checks every decoded-instruction side condition.
import Projects.thermostat.AuthLoop
import Projects.thermostat.QuietDet
import Projects.thermostat.RamRunQuiet
import Projects.thermostat.AuthTurnQuiet
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
open E5R E5R.Thermostat
namespace E5R.Thermostat.AuthLoop
theorem contract_quiet (B : Board) (ram : Word → BitVec 8) (xs ys : List (BitVec 8))
    (hl : xs.length = ys.length) (hne : xs ≠ []) (p q : Word)
    (hx : ReadBytes.Span B img ram p xs) (hy : ReadBytes.Span B img ram q ys)
    (c : Core) (acc : BitVec 8) (hp : c.pc = 0x80000582#32)
    (h10 : c.get 10 = acc.setWidth 32) (h11 : c.get 11 = q) (h12 : c.get 12 = p)
    (h13 : c.get 13 = q+BitVec.ofNat 32 xs.length) :
    ∃ d, Quiet.Steps B img (7*xs.length) ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc = 0x80000596#32 ∧
      d.get 10 = (AuthSpec.diff xs ys acc).setWidth 32 ∧
      d.get 11 = q+BitVec.ofNat 32 xs.length ∧ d.get 12 = p+BitVec.ofNat 32 xs.length ∧
      (∀ r : Reg, r ≠ 10 → r ≠ 11 → r ≠ 12 → r ≠ 14 → r ≠ 15 → d.get r = c.get r) ∧ d.sameCsr c := by
  induction xs generalizing ys p q c acc with
  | nil => contradiction
  | cons a as ih =>
    cases ys with
    | nil => simp at hl
    | cons b bs =>
      have hlen : as.length = bs.length := by simpa only [List.length_cons,Nat.add_right_cancel_iff] using hl
      obtain ⟨u,hu,upc,u10,u11,u12,uregs,ucsr⟩ := E5R.Thermostat.AuthTurn.contract_quiet B c ram p q a b acc (a::as).length
        (by simp) hx.length (ReadBytes.head hx) (ReadBytes.head hy) hp h10 h11 h12 h13
      cases as with
      | nil =>
        have hb : bs = [] := by apply List.eq_nil_of_length_eq_zero;simpa only [List.length_nil] using hlen.symm
        subst bs
        refine ⟨u,?_,?_,u10,u11,u12,uregs,ucsr⟩
        · simpa only [List.length_cons,List.length_nil] using hu
        · simpa only [List.length_cons,List.length_nil,ite_true] using upc
      | cons z zs =>
        have hpc' : u.pc = 0x80000582#32 := by
          have hn : (a::z::zs).length ≠ 1 := by simp
          simpa only [ite_eq_right hn] using upc
        have hend : (q+1#32)+BitVec.ofNat 32 (z::zs).length = q+BitVec.ofNat 32 (a::z::zs).length := by
          rw [BitVec.add_assoc,←BitVec.ofNat_add]
          apply congrArg (fun n : Nat => q+BitVec.ofNat 32 n)
          simp only [List.length_cons];omega
        have u13 : u.get 13 = (q+1#32)+BitVec.ofNat 32 (z::zs).length := by
          rw [uregs 13 (by decide) (by decide) (by decide) (by decide) (by decide),h13,hend]
        obtain ⟨d,hd,dpc,d10,d11,d12,dregs,dcsr⟩ := ih bs hlen (by simp) (p+1#32) (q+1#32)
          (ReadBytes.tail hx) (ReadBytes.tail hy) u (acc ||| (a ^^^ b)) hpc' u10 u11 u12 u13
        refine ⟨d,?_,dpc,d10,?_,?_,?_,dcsr.trans ucsr⟩
        · have hcount : 7+7*(z::zs).length = 7*(a::z::zs).length := by simp only [List.length_cons];omega
          rw [←hcount];exact hu.trans hd
        · exact d11.trans hend
        · have he : (p+1#32)+BitVec.ofNat 32 (z::zs).length = p+BitVec.ofNat 32 (a::z::zs).length := by
            rw [BitVec.add_assoc,←BitVec.ofNat_add]
            apply congrArg (fun n : Nat => p+BitVec.ofNat 32 n)
            simp only [List.length_cons];omega
          exact d12.trans he
        · intro r h1 h2 h3 h4 h5
          exact (dregs r h1 h2 h3 h4 h5).trans (uregs r h1 h2 h3 h4 h5)

end E5R.Thermostat.AuthLoop
