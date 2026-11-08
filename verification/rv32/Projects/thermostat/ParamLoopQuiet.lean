-- Generated stronger trace proofs; Lean checks every decoded-instruction side condition.
import Projects.thermostat.ParamLoop
import Projects.thermostat.QuietDet
import Projects.thermostat.RamRunQuiet
import Projects.thermostat.ParamInvalidQuiet
import Projects.thermostat.ParamTurnQuiet
set_option maxRecDepth 3000
set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false
open E5R E5R.Thermostat
namespace E5R.Thermostat.ParamLoop
theorem contract_quiet (B : Board) (c : Core) (ram : Word → BitVec 8) (p : Word) (xs : List (BitVec 8))
    (a consumed : Nat) (hs : Bytes.Span B ram p xs) (hn : 0 < xs.length)
    (hbudget : consumed+xs.length ≤ 10) (habound : a < 10^consumed)
    (hp : c.pc = 0x800027d8#32) (h11 : c.get 11 = BitVec.ofNat 32 a) (h13 : c.get 13 = 0#32)
    (h12 : c.get 12 = BitVec.ofNat 32 xs.length) (h14 : c.get 14 = p) (h10 : c.get 10 = 10#32) :
    ∃ d n, n ≤ 18*xs.length ∧ Quiet.Steps B img n ⟨c,ram⟩ ⟨d,ram⟩ ∧
      d.pc = (if xs.all DecimalSpec.digit then 0x8000280e#32 else 0x800027be#32) ∧
      (xs.all DecimalSpec.digit = true →
        d.get 11 = BitVec.ofNat 32 (DecimalSpec.number xs a) ∧
        d.get 13 = BitVec.ofNat 32 (DecimalSpec.number xs a/4294967296) ∧
        d.get 12 = 0#32 ∧ d.get 14 = p+BitVec.ofNat 32 xs.length) ∧
      Frame c d ∧ d.sameCsr c := by
  induction xs generalizing c p a consumed with
  | nil => simp at hn
  | cons b bs ih =>
    obtain ⟨hb,hm⟩ := Bytes.head hs
    cases hd : DecimalSpec.digit b with
    | false =>
      obtain ⟨d,ht,hpc,hr,hcsr⟩ := E5R.Thermostat.ParamInvalid.contract_quiet B c ram p b hp h14 h10 hm hb hd
      refine ⟨d,4,by simp only [List.length_cons];omega,ht,?_,?_,?_,hcsr⟩
      · simpa [List.all_cons,hd] using hpc
      · simp [List.all_cons,hd]
      · intro r _ _ _ _ _ h15 _ _;exact hr r h15
    | true =>
      have hpow : 10^consumed ≤ 1000000000 :=
        Nat.pow_le_pow_right (by decide) (show consumed ≤ 9 by simp only [List.length_cons] at hbudget;omega)
      have ha : a < 2^32 := by omega
      have hdb : 48 ≤ b.toNat ∧ b.toNat ≤ 57 := by simpa only [DecimalSpec.digit,decide_eq_true_eq] using hd
      have hanext : 10*a+(b.toNat-48) < 10^(consumed+1) := by rw [Nat.pow_succ];omega
      obtain ⟨d,ht,hpc,dlow,dhigh,dcnt,dptr,hr,hcsr⟩ := E5R.Thermostat.ParamTurn.contract_quiet B c ram p b a (bs.length+1)
        ha (by omega) (by simpa using hs.length) hp h11 h13 h12 h14 h10 hm hb hd
      cases bs with
      | nil =>
        refine ⟨d,18,by simp,ht,?_,?_,hr,hcsr⟩
        · simpa [hd] using hpc
        · intro _;exact ⟨dlow,dhigh,dcnt,dptr⟩
      | cons b' bs' =>
        have hn' : 0 < (b'::bs').length := by simp
        have hpow' : 10^(consumed+1) ≤ 1000000000 :=
          Nat.pow_le_pow_right (by decide) (show consumed+1 ≤ 9 by simp only [List.length_cons] at hbudget;omega)
        have hanext32 : 10*a+(b.toNat-48) < 4294967296 := by omega
        have hhigh : d.get 13 = 0#32 := by rw [dhigh,Nat.div_eq_of_lt hanext32]
        obtain ⟨e,n,hebound,he,hepc,heout,heregs,hecsr⟩ := ih d (p+1#32) (10*a+(b.toNat-48)) (consumed+1)
          (Bytes.tail hs) hn' (by simp only [List.length_cons] at hbudget ⊢;omega) hanext
          (by simpa using hpc) dlow hhigh (by simpa using dcnt) dptr
          ((hr 10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h10)
        refine ⟨e,18+n,by simp only [List.length_cons] at hebound ⊢;omega,ht.trans he,?_,?_,?_,hecsr.trans hcsr⟩
        · simpa [List.all_cons,hd] using hepc
        · intro hall
          have hall' : (b'::bs').all DecimalSpec.digit = true := by simpa [List.all_cons,hd] using hall
          obtain ⟨hlow,hhigh,hzero,hend⟩ := heout hall'
          refine ⟨hlow,hhigh,hzero,?_,⟩
          rw [hend,BitVec.add_assoc,←BitVec.ofNat_add]
          congr 2
          simp [Nat.add_comm]
        · intro r h1 h2 h3 h4 h5 h6 h7 h8
          exact (heregs r h1 h2 h3 h4 h5 h6 h7 h8).trans (hr r h1 h2 h3 h4 h5 h6 h7 h8)

end E5R.Thermostat.ParamLoop
