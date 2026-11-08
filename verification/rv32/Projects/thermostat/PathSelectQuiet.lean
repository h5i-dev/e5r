-- Generated stronger trace proofs; Lean checks every decoded-instruction side condition.
import Projects.thermostat.PathSelect
import Projects.thermostat.QuietDet
import Projects.thermostat.RamRunQuiet
import Projects.thermostat.PathDispatchQuiet
import Projects.thermostat.PathFiveQuiet
import Projects.thermostat.PathLiteralsQuiet
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
open E5R E5R.Thermostat
namespace E5R.Thermostat.PathSelect
theorem contract_quiet (B : Board) (c : Core) (ram : Word → BitVec 8) (req p : Word) (xs : List (BitVec 8))
    (h : PathDispatch.PathAt B ram req p xs) (hp : c.pc = 0x80001fb4#32) (hreq : c.get 10 = req) :
    ∃ d n, n ≤ 35 ∧ Quiet.Steps B img n ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc = target xs ∧
      (∀ r : Reg, r ≠ 11 → r ≠ 12 → r ≠ 13 → d.get r = c.get r) ∧ d.sameCsr c := by
  obtain ⟨a,n,hn,ht,hpc,h11,hregs,hcsr⟩ := E5R.Thermostat.PathDispatch.contract_quiet B c ram req p xs h hp hreq
  by_cases h5 : xs.length = 5
  · have hp1 : a.pc = 0x800020ae#32 := by simpa only [PathDispatch.destination,ite_eq_left h5] using hpc
    have hp11 := h11 (Or.inl h5)
    cases xs with
    | nil => simp at h5
    | cons b bs =>
      cases bs with
      | nil => simp at h5
      | cons z zs =>
        have hl : zs.length = 3 := by simp only [List.length_cons] at h5;omega
        obtain ⟨d,k,hk,td,pcd,rd,cd⟩ := E5R.Thermostat.PathFive.contract_quiet B a ram p b z zs h.bytes hl hp1 hp11
        refine ⟨d,n+k,by omega,ht.trans td,?_,?_,cd.trans hcsr⟩
        · simpa only [target,ite_eq_left h5] using pcd
        · intro r h1 h2 h3;rw [rd r h1 h2 h3,hregs r h1 h2]
  · by_cases h9 : xs.length = 9
    · have hp1 : a.pc = 0x80002020#32 := by simpa only [PathDispatch.destination,ite_eq_right h5,ite_eq_left h9] using hpc
      obtain ⟨d,k,hk,td,pcd,rd,cd⟩ := E5R.Thermostat.PathLiterals.point_quiet B a ram p xs (by simpa using h.bytes) h9 hp1 (h11 (Or.inr (Or.inl h9)))
      refine ⟨d,n+k,by omega,ht.trans td,?_,?_,cd.trans hcsr⟩
      · simpa only [target,ite_eq_right h5,ite_eq_left h9] using pcd
      · intro r h1 h2 h3;rw [rd r h1 h2 h3,hregs r h1 h2]
    · by_cases h6 : xs.length = 6
      · have hp1 : a.pc = 0x80001fce#32 := by simpa only [PathDispatch.destination,ite_eq_right h5,ite_eq_right h9,ite_eq_left h6] using hpc
        obtain ⟨d,k,hk,td,pcd,rd,cd⟩ := E5R.Thermostat.PathLiterals.state_quiet B a ram p xs (by simpa using h.bytes) h6 hp1 (h11 (Or.inr (Or.inr h6)))
        refine ⟨d,n+k,by omega,ht.trans td,?_,?_,cd.trans hcsr⟩
        · simpa only [target,ite_eq_right h5,ite_eq_right h9,ite_eq_left h6] using pcd
        · intro r h1 h2 h3;rw [rd r h1 h2 h3,hregs r h1 h2]
      · refine ⟨a,n,by omega,ht,?_,?_,hcsr⟩
        · simpa only [target,PathDispatch.destination,ite_eq_right h5,ite_eq_right h9,ite_eq_right h6] using hpc
        · intro r h1 h2 h3;exact hregs r h1 h2

end E5R.Thermostat.PathSelect
