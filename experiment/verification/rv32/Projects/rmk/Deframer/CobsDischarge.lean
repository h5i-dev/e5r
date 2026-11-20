/-
  The COBS dependency of `next`, discharged: `CobsReportContract` (Deframer/Spec.lean) from the
  COBS worker's proved contract of `decode_in_place_report` (`E5R.Rmk.Cobs.decode`,
  Projects/rmk/Cobs/Decode.lean), and with it `next`'s contract conditional on memmove's alone.

  Original e5r code, Apache-2.0.

  PROVED here:
  * `run_len`: the decode loop's output is never longer than the frame (`Cobs.run`, the COBS
    worker's transliteration of the emitted loop);
  * `cobs_report : CobsReportContract`, by `Cobs.decode`: every precondition of `CobsEnv` here
    gives the COBS worker's `CobsEnv`; `Returns` gives the frame, registers, CSRs and RAM; `Res`
    gives the Ok test: Ok only on the success path (tag 0), whose decoded length is at most the
    frame length;
  * `next_from_copy : NextFromCopy`, i.e. `CopyContract → NextContract`.
  CopyContract is still a HYPOTHESIS (memmove's n ≥ 16 backward and misaligned paths are not
  proved yet).
-/
import Projects.rmk.Deframer.Next
import Projects.rmk.Cobs.Decode

namespace E5R.Rmk.Deframer
open E5R E5R.Rmk

theorem run_len (orig : Nat → Nat) (n : Nat) :
    ∀ fuel src (acc : List Nat), acc.length ≤ src → src ≤ n → (Cobs.run orig n fuel src acc).2.length ≤ n
  | 0, src, acc, h1, h2 => by simp only [Cobs.run]; omega
  | fuel + 1, src, acc, h1, h2 => by
    unfold Cobs.run
    split
    · dsimp only; omega
    · rename_i hs
      split
      · dsimp only; omega
      · rename_i out src' hb
        obtain ⟨a, b, c⟩ := Cobs.block_some hb (by omega)
        exact run_len orig n fuel src' (acc ++ out) (by simp only [List.length_append]; omega) b

theorem cobs_report : CobsReportContract := by
  intro m₀ E
  have E' : Cobs.CobsEnv m₀ :=
    ⟨E.pc, E.quiet, E.out, E.outAl, E.data, E.n, E.frame, E.spAl, E.sep.1.symm, E.sep.2.2, E.sep.2.1, E.ra⟩
  obtain ⟨k, m, r, ret, res⟩ := Cobs.decode m₀ E'
  refine ⟨k, m, r, ret.pc, fun r h => ret.regs r h, ret.csr, ?_, ?_⟩
  · intro x a b c'
    refine ret.ram x ?_
    intro hw
    rcases hw with hw | hw | hw
    · exact b hw
    · exact a hw
    · exact c' hw
  · intro hok
    have hlen : (m₀.core.get 12).toNat ≤ bufLen := E.n
    obtain ⟨h0, hpos⟩ := res
    by_cases hz : (m₀.core.get 12).toNat = 0
    · obtain ⟨r0, r1⟩ := h0 hz
      rw [r0, r1] at hok
      exact absurd hok (by decide)
    · obtain ⟨r0, r1, r2, -⟩ := hpos (by omega)
      let orig := Cobs.bufByte m₀.ram (m₀.core.get 11)
      let n := Cobs.firstZero orig 0 (m₀.core.get 12).toNat
      have hn : n ≤ (m₀.core.get 12).toNat :=
        (Cobs.firstZero_spec orig (m₀.core.get 12).toNat (m₀.core.get 12).toNat 0 (by omega)).2.1
      by_cases hk : (Cobs.run orig n (n + 1) 0 []).1 = .ok
      · have hl := run_len orig n (n + 1) 0 [] (by simp) (by omega)
        show (ramRead m.ram (m₀.core.get 10 + 8) .w).toNat ≤ (m₀.core.get 12).toNat
        rw [r2, BitVec.toNat_ofNat]
        have : (Cobs.run orig n (n + 1) 0 []).2.length < 2 ^ 32 := by
          have : bufLen = 488 := rfl
          omega
        rw [Nat.mod_eq_of_lt this]; omega
      · rw [r0, r1, if_neg hk, if_neg hk] at hok
        exact absurd hok (by decide)

/-- `next`'s contract given memmove's alone (COBS discharged by `cobs_report`). -/
theorem next_from_copy : NextFromCopy := fun hC => Next.next_from_deps hC cobs_report

end E5R.Rmk.Deframer
