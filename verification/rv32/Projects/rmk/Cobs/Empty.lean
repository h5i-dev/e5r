/-
  `cobs::dec::decode_in_place_report` on an empty input (len = 0): the path
  0x8001e02e → 0x8001e03a (beqz a2) → 0x8001e0f8 → 0x8001e102 → ra.

  Original e5r code, Apache-2.0.

  Result: `Err(DecodeError)` with tag word 1 at a0 and error code 0 at a0+4
  (the empty-frame error), nothing else written but the frame; callee-saved
  registers, sp and CSRs as at entry. In `next`'s call (through
  `decode_in_place`) the length is that of a frame without its delimiter, so
  this is the decoder's answer to an empty frame (two delimiters in a row).
-/
import Projects.rmk.Cobs.Basic

set_option maxRecDepth 100000

namespace E5R.Rmk.Cobs
open E5R E5R.Rmk E5R.Rmk.CobsFetch

theorem empty (m₀ : Machine) (h : CobsEnv m₀) (hn : (m₀.core.get 12).toNat = 0) :
    ∃ k m, QRun B img k m₀ m ∧ Returns m₀ m ∧
      ramRead m.ram (m₀.core.get 10) .w = 1 ∧ ramRead m.ram (m₀.core.get 10 + 4) .w = 0 := by
  obtain ⟨c, R⟩ := m₀
  have hpro := prologue c R h.pc h.quiet h.frame h.spAl
  have h12 : c.get 12 = 0 := by simp only at hn; bv_omega
  let e0 := pro c
  let e1 := e0.goto 0x8001e0f8
  let e2 := e1.wr 7 (alu .add (e1.get 0) 0x0#32) 0x8001e0fa
  let e3 := e2.wr 11 (alu .add (e2.get 0) 0x1#32) 0x8001e0fc
  let e4 := e3.goto 0x8001e102
  have k0 : e0.sameCsr c := pro_sameCsr c
  have k4 : e4.sameCsr c :=
    (Core.sameCsr_goto _ _).trans ((Core.sameCsr_wr _ _ _ _).trans ((Core.sameCsr_wr _ _ _ _).trans
      ((Core.sameCsr_goto _ _).trans k0)))
  have q : ∀ d : Core, d.sameCsr c → Quiet d := fun d hd => Quiet.of_sameCsr hd h.quiet
  have s1 : DetStep B img ⟨e0, saved c R⟩ ⟨e1, saved c R⟩ :=
    dstep f8001e03a rfl (by
      rw [exec_branch, if_pos (by simp [taken, e0, pro_get c 12 (by decide) (by decide), h12])]
      exact jump_ok _ _ (by show (0x8001e0f8 : Word).getLsbD 0 = false; decide))
  have s2 : DetStep B img ⟨e1, saved c R⟩ ⟨e2, saved c R⟩ := dstep f8001e0f8 rfl (by rw [exec_opimm]; rfl)
  have s3 : DetStep B img ⟨e2, saved c R⟩ ⟨e3, saved c R⟩ := dstep f8001e0fa rfl (by rw [exec_opimm]; rfl)
  have s4 : DetStep B img ⟨e3, saved c R⟩ ⟨e4, saved c R⟩ :=
    dstep f8001e0fc rfl (by
      rw [exec_jal, Core.set_zero]; exact jump_ok _ _ (by show (0x8001e102 : Word).getLsbD 0 = false; decide))
  have run1 : QRun B img 4 ⟨e0, saved c R⟩ ⟨e4, saved c R⟩ :=
    .step (q _ k0) s1 (.step (q _ ((Core.sameCsr_goto _ _).trans k0)) s2
      (.step (q _ ((Core.sameCsr_wr _ _ _ _).trans ((Core.sameCsr_goto _ _).trans k0))) s3
      (.single (q _ ((Core.sameCsr_wr _ _ _ _).trans ((Core.sameCsr_wr _ _ _ _).trans
        ((Core.sameCsr_goto _ _).trans k0)))) s4)))
  have g : ∀ r : Reg, r ≠ 7 → r ≠ 11 → e4.get r = e0.get r := fun r h7 h11 => by
    simp [e4, e3, e2, e1, Core.wr_get_ne, h7, h11]
  obtain ⟨m, hm, hret, r0, r4, -, -⟩ := finish c R (saved c R) e4 h rfl (q _ k4) k4
    (by rw [g 2 (by decide) (by decide)]; exact pro_sp c)
    (by rw [g 1 (by decide) (by decide), pro_get c 1 (by decide) (by decide)])
    (by rw [g 10 (by decide) (by decide), pro_get c 10 (by decide) (by decide)])
    (by left; rw [g 16 (by decide) (by decide)]; exact pro_a6 c)
    (fun r hr hr' => by
      have n : ∀ k, k ∈ clobbered ∨ k ∈ [2, 8, 9, 18, 19] → r.val ≠ k := fun k hk e => by
        subst e; rcases hk with hk | hk; exact hr hk; exact hr' hk
      rw [g r (fun e => n 7 (by decide) (by rw [e]; rfl)) (fun e => n 11 (by decide) (by rw [e]; rfl)),
        pro_get c r (fun e => n 2 (by decide) (by rw [e]; rfl)) (fun e => n 16 (by decide) (by rw [e]; rfl))])
    (saved_hold c R h.frame)
    (fun x _ _ hx => saved_out c R h.frame x hx)
  have v11 : e4.get 11 = 1 := by simp [e4, e3, Core.wr_get_self, alu]
  have v7 : e4.get 7 = 0 := by simp [e4, e3, e2, Core.wr_get_ne, Core.wr_get_self, alu]
  have v16 : e4.get 16 = 4 := by rw [g 16 (by decide) (by decide)]; exact pro_a6 c
  refine ⟨6 + 4 + 9, m, (hpro.trans run1).trans hm, hret, ?_, ?_⟩
  · rw [r0, v11]
  · rw [← v16, r4, v7]

end E5R.Rmk.Cobs
