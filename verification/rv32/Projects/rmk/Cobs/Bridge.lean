/-
  The proved COBS contract (`E5R.Rmk.Cobs.decode`) implies main's interface
  `E5R.Rmk.Deframer.CobsReportContract` (Projects/rmk/Deframer/Spec.lean, imported, not edited).

  Original e5r code, Apache-2.0.

  The two `CobsEnv`s agree field by field (same entry, bound, slot, frame, separations); the
  posts agree on pc, caller-saved registers, CSRs and the RAM frame; main's `ok` clause (when
  `(r0 - 1) | r1 = -1`, the decoded length r2 is at most n) follows from `Res`: success writes
  r0 = 0 and r2 = |run output| ≤ n ≤ len, every other outcome makes `(r0 - 1) | r1 ≠ -1`.
-/
import Projects.rmk.Cobs.Decode
import Projects.rmk.Deframer.Spec

set_option maxRecDepth 100000

namespace E5R.Rmk.Cobs
open E5R E5R.Rmk

/-- The loop's output is never longer than the first zero index. -/
theorem run_length (f : Nat → Nat) (n : Nat) :
    ∀ fuel src acc, acc.length ≤ src → src ≤ n → (run f n fuel src acc).2.length ≤ n
  | 0, _, _, h1, h2 => by simp [run]; omega
  | fuel + 1, src, acc, h1, h2 => by
    unfold run
    split
    · simp; omega
    · rename_i hs
      cases hb : block f n src with
      | none => simp; omega
      | some p =>
        obtain ⟨out, src'⟩ := p
        obtain ⟨a, b, c⟩ := block_some hb (by omega)
        exact run_length f n fuel src' (acc ++ out) (by simp; omega) b

theorem env_bridge (m : Machine) (h : E5R.Rmk.Deframer.CobsEnv m) : CobsEnv m := by
  obtain ⟨pc, quiet, n, data, out, outAl, frame, spAl, ⟨s1, s2, s3⟩, ra⟩ := h
  exact ⟨pc, quiet, out, outAl, data, n, frame, spAl, by rcases s1 with e | e <;> omega, s3, s2, ra⟩

/-- **Main's COBS interface, discharged** by the machine-code proof of `decode`. -/
theorem cobs_report_contract : E5R.Rmk.Deframer.CobsReportContract := by
  intro m₀ h
  obtain ⟨k, m, hr, hret, hres⟩ := decode m₀ (env_bridge m₀ h)
  refine ⟨k, m, hr, ⟨hret.pc, fun r hr' => hret.regs r hr', hret.csr, fun x a b c => hret.ram x ?_, ?_⟩⟩
  · simp only [Writable, not_or]; exact ⟨b, a, c⟩
  · intro hok
    obtain ⟨hz, hp⟩ := hres
    by_cases h0 : (m₀.core.get 12).toNat = 0
    · obtain ⟨r0, r4⟩ := hz h0
      rw [r0, r4] at hok; exact absurd hok (by decide)
    · obtain ⟨r0, r4, r8, -⟩ := hp (by omega)
      obtain ⟨-, hnl, -, -⟩ := firstZero_spec (bufByte m₀.ram (m₀.core.get 11)) (m₀.core.get 12).toNat
        (m₀.core.get 12).toNat 0 (by omega)
      split at r0
      · show (ramRead m.ram (m₀.core.get 10 + 8) .w).toNat ≤ _
        rw [r8, BitVec.toNat_ofNat]
        have := run_length (bufByte m₀.ram (m₀.core.get 11)) (firstZero (bufByte m₀.ram (m₀.core.get 11)) 0
          (m₀.core.get 12).toNat) (firstZero (bufByte m₀.ram (m₀.core.get 11)) 0
          (m₀.core.get 12).toNat + 1) 0 [] (by simp) (Nat.zero_le _)
        omega
      · rename_i hne
        rw [if_neg hne] at r4
        rw [r0, r4] at hok; exact absurd hok (by decide)

end E5R.Rmk.Cobs
