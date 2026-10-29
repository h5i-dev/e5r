/-
  The emitted memmove of the pinned RMK firmware, for copies of fewer than
  16 bytes (BOUNDED SPECIALIZATION: the word-copy and misaligned paths the
  code takes for 16 bytes or more are not covered here).

  Original e5r code, Apache-2.0.

  Entry is the call target every caller uses, the trampoline
  `memmove` at 0x80020c1e (`auipc t1,0; jr 0x180(t1)`), which jumps to
  `compiler_builtins::mem::memmove` at 0x80020d9e. ABI: a0 = dst, a1 = src,
  a2 = n, ra = return address, sp = stack pointer. The function saves s0,
  s1, s2 at sp-4, sp-8, sp-12 (its frame is sp-48..sp), picks the copy
  direction from `dst - src < n` (unsigned), copies bytewise for n < 16
  (forward, or backward from the top when dst lies inside the source),
  restores s0..s2 and returns to ra with a0 = dst.

  `contract`: from every machine meeting `Pre`, a quiet run (no interrupt
  enabled at any machine of it, every step deterministic: no fault, no
  event) reaches a machine meeting `Post`: at `ra`, every register but
  t1, a1..a4, a6 as at entry (s0..s2 and sp restored), CSRs unchanged, and
  RAM outside the three save slots equal to the memmove of the entry RAM
  (overlap in either direction included; zero length leaves RAM alone).
-/
import Projects.rmk.MemmoveLoops
import Theories.AbsintSound

set_option maxRecDepth 100000

namespace E5R.Rmk.Memmove
open E5R E5R.Rmk E5R.Rmk.MemmoveFetch

/-! ## Epilogue: 0x800210b0 lw s0..s2, addi sp, ret -/

theorem and_not_one (x : Word) (h : x.getLsbD 0 = false) : x &&& ~~~1 = x := by
  apply BitVec.eq_of_getElem_eq
  intro i hi
  rw [BitVec.getElem_and, BitVec.getElem_not]
  rcases i with _ | i
  · rw [← BitVec.getLsbD_eq_getElem, h]; simp
  · have : (1 : Word)[i + 1] = false := by
      rw [← BitVec.getLsbD_eq_getElem]; simp [BitVec.getLsbD_one]
    rw [this]; simp

/-- The epilogue's last core. -/
def epi (e : Core) (R : Word → BitVec 8) (sp' : Word) : Core :=
  ((((e.wr 8 (ramRead R (sp' + 0x2c#32) .w) 0x800210b2).wr 9 (ramRead R (sp' + 0x28#32) .w)
    0x800210b4).wr 18 (ramRead R (sp' + 0x24#32) .w) 0x800210b6).wr 2 (sp' + 0x30#32) 0x800210b8).goto
    (e.get 1)

theorem epilogue (e : Core) (R : Word → BitVec 8) (sp' : Word) (hpc : e.pc = 0x800210b0) (hq : Quiet e)
    (hsp : e.get 2 = sp') (hra : (e.get 1).getLsbD 0 = false)
    (h0 : (sp' + 0x2c#32).toNat % 4 = 0) (h1 : (sp' + 0x28#32).toNat % 4 = 0)
    (h2 : (sp' + 0x24#32).toNat % 4 = 0)
    (r0 : B.inRam (sp' + 0x2c#32) 4 = true) (r1 : B.inRam (sp' + 0x28#32) 4 = true)
    (r2 : B.inRam (sp' + 0x24#32) 4 = true) :
    QRun B img 5 ⟨e, R⟩ ⟨epi e R sp', R⟩ := by
  let e1 := e.wr 8 (ramRead R (sp' + 0x2c#32) .w) 0x800210b2
  let e2 := e1.wr 9 (ramRead R (sp' + 0x28#32) .w) 0x800210b4
  let e3 := e2.wr 18 (ramRead R (sp' + 0x24#32) .w) 0x800210b6
  let e4 := e3.wr 2 (sp' + 0x30#32) 0x800210b8
  have q1 : Quiet e1 := Quiet.of_sameCsr (Core.sameCsr_wr _ _ _ _) hq
  have q2 : Quiet e2 := Quiet.of_sameCsr (Core.sameCsr_wr _ _ _ _) q1
  have q3 : Quiet e3 := Quiet.of_sameCsr (Core.sameCsr_wr _ _ _ _) q2
  have q4 : Quiet e4 := Quiet.of_sameCsr (Core.sameCsr_wr _ _ _ _) q3
  have s0 : DetStep B img ⟨e, R⟩ ⟨e1, R⟩ := by
    refine detStep_of (by rw [hpc]; decide) (by rw [hpc]; exact f800210b0) fun o => ?_
    rw [exec_load, hsp, interp_load_ram (w := .w) o h0 r0, hpc]; rfl
  have s1 : DetStep B img ⟨e1, R⟩ ⟨e2, R⟩ := by
    refine detStep_of (by show (0x800210b2 : Word).getLsbD 0 = false; decide) f800210b2 fun o => ?_
    rw [exec_load]
    have : e1.get 2 = sp' := by simp [e1, Core.wr_get_ne, hsp]
    rw [this, interp_load_ram (w := .w) o h1 r1]; rfl
  have s2 : DetStep B img ⟨e2, R⟩ ⟨e3, R⟩ := by
    refine detStep_of (by show (0x800210b4 : Word).getLsbD 0 = false; decide) f800210b4 fun o => ?_
    rw [exec_load]
    have : e2.get 2 = sp' := by simp [e2, e1, Core.wr_get_ne, hsp]
    rw [this, interp_load_ram (w := .w) o h2 r2]; rfl
  have s3 : DetStep B img ⟨e3, R⟩ ⟨e4, R⟩ := by
    refine detStep_of (by show (0x800210b6 : Word).getLsbD 0 = false; decide) f800210b6 fun o => ?_
    rw [exec_opimm]
    have : e3.get 2 = sp' := by simp [e3, e2, e1, Core.wr_get_ne, hsp]
    rw [this]; rfl
  have s4 : DetStep B img ⟨e4, R⟩ ⟨epi e R sp', R⟩ := by
    refine detStep_of (by show (0x800210b8 : Word).getLsbD 0 = false; decide) f800210b8 fun o => ?_
    rw [exec_jalr, Core.set_zero]
    have : e4.get 1 = e.get 1 := by simp [e4, e3, e2, e1, Core.wr_get_ne]
    rw [this, BitVec.add_zero, and_not_one _ hra, jump_ok _ _ hra]; rfl
  exact .step hq s0 (.step q1 s1 (.step q2 s2 (.step q3 s3 (.single q4 s4))))

end E5R.Rmk.Memmove
