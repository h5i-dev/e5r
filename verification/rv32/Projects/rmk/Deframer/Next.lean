/-
  `Deframer::next` (0x8001d43a) on the pinned RMK image: the whole method.

  Original e5r code, Apache-2.0.

  PROVED here, CONDITIONAL ON `CopyContract` AND `CobsReportContract` (hypotheses, not axioms, not
  proved here): `next_from_deps : NextFromDeps`, i.e. `CopyContract → CobsReportContract →
  NextContract`: from every machine at `next` meeting `CallEnv nextPc nextStack`, the deframer
  invariant and discarding ≤ 1, whatever bytes the buffer holds, a quiet run reaches a machine
  meeting `NextPost` (returned to ra, ABI frame, None or Some(k) with 2 < k ≤ len, the invariant
  again, discarding ≤ 1, writes confined to the deframer, the buffer and 0x70 stack bytes). No
  step of that run reaches a panic: each step of a quiet run is the model's only behaviour.

  The loop: `head` (the prologue), then by induction on filled - cursor each turn either returns
  (`end_case`, `scan_case`, `call_case`) or comes back to the loop head with a larger cursor
  (`disc_case`, `call_case`).
-/
import Projects.rmk.Deframer.NextBody2

set_option maxRecDepth 100000

namespace E5R.Rmk.Deframer.Next
open E5R E5R.Rmk.Deframer.Tail

theorem loop (hC : CopyContract) (hR : CobsReportContract) (c : Core) (R0 : Word → BitVec 8)
    (E : CallEnv nextPc nextStack ⟨c, R0⟩) :
    ∀ n (d : Core) (M : Word → BitVec 8), (d.get 8).toNat - (d.get 9).toNat ≤ n → LoopInv c R0 d M →
      ∃ k m, QRun B img k ⟨d, M⟩ m ∧ NextPost ⟨c, R0⟩ m := by
  intro n
  induction n with
  | zero =>
    intro d M hn h
    have hcl := h.curle
    have heq : d.get 9 = d.get 8 := BitVec.eq_of_toNat_eq (by omega)
    exact end_case c R0 E d M h heq
  | succ n ih =>
    intro d M hn h
    by_cases heq : d.get 9 = d.get 8
    · exact end_case c R0 E d M h heq
    · rcases scan_case c R0 E d M h heq with done | ⟨k, e, j, r, hf⟩
      · exact done
      · have hs7 := h.s7
        by_cases h1 : d.get 23 = 1
        · obtain ⟨k', d', M', r', li, lt⟩ := disc_case c R0 E d M h e j hf h1
          obtain ⟨k'', m, r'', post⟩ := ih d' M' (by omega) li
          exact ⟨_, m, (r.trans r').trans r'', post⟩
        · have h0 : d.get 23 = 0 := by
            have : (d.get 23).toNat ≠ 1 := fun h' => h1 (BitVec.eq_of_toNat_eq h')
            exact BitVec.eq_of_toNat_eq (by show (d.get 23).toNat = 0; omega)
          rcases call_case hC hR c R0 E d M h e j hf h0 with ⟨k', m, r', post⟩ | ⟨k', d', M', r', li, lt⟩
          · exact ⟨_, m, r.trans r', post⟩
          · obtain ⟨k'', m, r'', post⟩ := ih d' M' (by omega) li
            exact ⟨_, m, (r.trans r').trans r'', post⟩

/-- `next`'s contract, given memmove's and the COBS decoder's (hypotheses, not proved here). -/
theorem next_from_deps : NextFromDeps := by
  intro hC hR m₀ E hI hd
  obtain ⟨c, R0⟩ := m₀
  obtain ⟨k, d, M, r, li⟩ := head c R0 E hI hd
  obtain ⟨k', m, r', post⟩ := loop hC hR c R0 E _ d M (Nat.le_refl _) li
  exact ⟨_, m, r.trans r', post⟩

end E5R.Rmk.Deframer.Next
