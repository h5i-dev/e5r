-- Generated stronger trace proofs; Lean checks every decoded-instruction side condition.
import Projects.thermostat.ModeDecode
import Projects.thermostat.QuietDet
import Projects.thermostat.RamRunQuiet
import Projects.thermostat.ModeFinishQuiet
import Projects.thermostat.ModeFourQuiet
import Projects.thermostat.ModeIntroQuiet
import Projects.thermostat.ModeOffQuiet
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
open E5R E5R.Thermostat
namespace E5R.Thermostat.ModeDecode
theorem contract_quiet (B : Board) (c : Core) (ram : Word → BitVec 8) (p : Word) (xs : List (BitVec 8))
    (hs : Bytes.Span B ram p xs) (hp : c.pc = 0x8000215a#32)
    (h8 : c.get 8 = p) (h9 : c.get 9 = BitVec.ofNat 32 xs.length) :
    ∃ d n, n ≤ 26 ∧ Quiet.Steps B img n ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc = 0x80002212#32 ∧
      WireSpec.ResultWord (d.get 10) (ModeSpec.value xs) ∧
      (∀ r : Reg, r ≠ 10 → r ≠ 11 → r ≠ 12 → r ≠ 13 → d.get r = c.get r) ∧ d.sameCsr c := by
  obtain ⟨c1,n,hn,ht,hpc,htag,hstatus,hregs,hcsr⟩ := E5R.Thermostat.ModeIntro.contract_quiet B c ram xs.length hs.length hp h9
  have p8 : c1.get 8 = p := (hregs 8 (by decide) (by decide) (by decide)).trans h8
  by_cases h4 : xs.length = 4
  · have hp1 : c1.pc = 0x8000221c#32 := by simpa only [ite_eq_left h4] using hpc
    cases xs with
    | nil => simp at h4
    | cons b bs =>
      have hl : bs.length = 3 := by simp only [List.length_cons] at h4;omega
      obtain ⟨d,k,hk,td,pcd,vd,rd,cd⟩ := E5R.Thermostat.ModeFour.contract_quiet B c1 ram p b bs hs hl hp1 p8 htag hstatus
      refine ⟨d,n+k,by omega,ht.trans td,pcd,vd,?_,cd.trans hcsr⟩
      intro r h1 h2 h3 h4;rw [rd r h1 h2 h3 h4,hregs r h1 h2 h3]
  · by_cases h3 : xs.length = 3
    · have hp1 : c1.pc = 0x8000216e#32 := by simpa only [ite_eq_right h4,ite_eq_left h3] using hpc
      have he := List.eq_getElem_of_length_eq_three xs h3
      obtain ⟨d,k,hk,td,pcd,vd,rd,cd⟩ := E5R.Thermostat.ModeOff.contract_quiet B c1 ram p xs[0] xs[1] xs[2] (by rw [←he];exact hs) hp1 p8 htag hstatus
      refine ⟨d,n+k,by omega,ht.trans td,pcd,?_,?_,cd.trans hcsr⟩
      · simpa only [←he] using vd
      · intro r h1 h2 h3 h4;rw [rd r h1 h2 h3 h4,hregs r h1 h2 h3]
    · have hp1 : c1.pc = 0x8000220a#32 := by simpa only [ite_eq_right h4,ite_eq_right h3] using hpc
      obtain ⟨d,td,pcd,vd,rd,cd⟩ := E5R.Thermostat.ModeFinish.error_quiet B c1 ram hp1 htag hstatus
      have spec : ModeSpec.value xs = .error 400 := by
        have h_off : xs ≠ WireSpec.ascii "off" := by intro he;apply h3;rw [he];rfl
        have h_heat : xs ≠ WireSpec.ascii "heat" := by intro he;apply h4;rw [he];rfl
        have h_auto : xs ≠ WireSpec.ascii "auto" := by intro he;apply h4;rw [he];rfl
        simp only [ModeSpec.value,ite_eq_right h_off,ite_eq_right h_heat,ite_eq_right h_auto]
      refine ⟨d,n+4,by omega,ht.trans td,pcd,by simpa only [spec] using vd,?_,cd.trans hcsr⟩
      intro r h1 h2 h3 h4;rw [rd r h1 h2 h3,hregs r h1 h2 h3]

end E5R.Thermostat.ModeDecode
