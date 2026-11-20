/-
`u64 sum2(const u64 *a, u64 n, const u64 *b, u64 m)` from examples/sum.c:
`sum(a, n) + sum(b, m)`, as clang -O2 compiled it:

    111b4  addi sp, sp, -32          frame
    111b8  sd   ra, 24(sp)           save ra, s0, s1, s2
    111bc  sd   s0, 16(sp)
    111c0  sd   s1, 8(sp)
    111c4  sd   s2, 0(sp)
    111c8  addi s0, a3, 0            keep m and b across the first call
    111cc  addi s1, a2, 0
    111d0  auipc ra, 0               call sum(a, n)
    111d4  jalr ra, -64(ra)
    111d8  addi s2, a0, 0
    111dc  addi a0, s1, 0
    111e0  addi a1, s0, 0
    111e4  auipc ra, 0               call sum(b, m)
    111e8  jalr ra, -84(ra)
    111ec  add  a0, a0, s2
    111f0  ld   ra, 24(sp)           restore
    111f4  ld   s0, 16(sp)
    111f8  ld   s1, 8(sp)
    111fc  ld   s2, 0(sp)
    11200  addi sp, sp, 32
    11204  jalr zero, 0(ra)

The proof never looks at `sum`'s code: both calls go through
`Verified.call` with `sum_verified`, using only `sum`'s specification
(its result, the registers it preserves, and that it writes no memory).
-/
import Examples.Sum

namespace Examples.Sum2
open NoCompiler Examples.Sum.Image
open Examples.Sum (sumW Args spec sum_verified)

/-- The logical arguments: two arrays. -/
structure Args2 where
  a : Word
  xs : List Word
  b : Word
  ys : List Word

/-- `sum2`: a0, a1 = the first array, a2, a3 = the second; returns the sum of
    both. It reads only the arrays and uses 32 bytes of stack, which the arrays
    must not overlap. -/
def spec2 : Spec Args2 where
  pre := fun ⟨a, xs, b, ys⟩ s =>
    s.reg Reg.a0 = a ∧ s.reg Reg.a1 = BitVec.ofNat 64 xs.length ∧
    s.reg Reg.a2 = b ∧ s.reg Reg.a3 = BitVec.ofNat 64 ys.length ∧
    8 * xs.length < 2 ^ 64 ∧ 8 * ys.length < 2 ^ 64 ∧ aligned a 8 ∧ aligned b 8 ∧
    arr64 s.mem a xs ∧ arr64 s.mem b ys ∧
    (∀ x, (arrRegion a xs).mem x → ¬ (Spec.stackRegion s 32).mem x) ∧
    (∀ x, (arrRegion b ys).mem x → ¬ (Spec.stackRegion s 32).mem x)
  post := fun ⟨_, xs, _, ys⟩ _ s' => s'.reg Reg.a0 = sumW xs + sumW ys
  reads := fun ⟨a, xs, b, ys⟩ _ => [arrRegion a xs, arrRegion b ys]
  stack := 32

/-- `sum2` as compiled: correct, memory-safe, terminating, ABI-preserving,
    from `sum`'s specification. -/
theorem sum2_verified : Verified code sum2_dom sum2_entry spec2 := by
  rintro ⟨a, xs, b, ys⟩ s he ⟨ha0, ha1, ha2, ha3, hl1, hl2, hal1, hal2, harr1, harr2, hd1, hd2⟩
  have hpc : s.pc = 0x111b4#64 := he.pc
  have hx := he.live
  -- fb: the frame base, sp - 32.
  have hfb : s.reg 2 + 0xffffffffffffffe0#64 = s.reg 2 - BitVec.ofNat 64 32 := by bv_omega
  generalize hF : s.reg 2 - BitVec.ofNat 64 32 = fb at hfb
  have hfal : aligned fb 16 := by
    have : aligned (s.reg 2) 16 := he.sp
    unfold aligned at this ⊢
    rw [← hF, BitVec.toNat_sub, Nat.mod_mod_of_dvd _ (by decide : 16 ∣ 2 ^ 64)]
    rw [toNat_ofNat_of_lt (by decide)]; omega
  have hfal8 : aligned fb 8 := by unfold aligned at hfal ⊢; omega
  have hw : ∀ off, off + 8 ≤ 32 → (spec2.perm ⟨a, xs, b, ys⟩ s).canWrite (fb + BitVec.ofNat 64 off) 8 := by
    intro off ho
    right
    refine ⟨Spec.stackRegion s 32, by simp [Spec.perm, spec2], ?_⟩
    unfold Region.covers Spec.stackRegion
    simp only [hF]
    rw [add_ofNat_sub_toNat fb (by omega)]; omega
  have hal : ∀ off, off % 8 = 0 → aligned (fb + BitVec.ofNat 64 off) 8 := fun off ho =>
    aligned_add_ofNat hfal8 ho (by decide)
  -- addi sp, sp, -32
  nocompiler_step [hpc, hfb]
  -- sd ra, 24(sp); sd s0, 16(sp); sd s1, 8(sp); sd s2, 0(sp)
  nocompiler_step
  · exact hw 24 (by omega)
  simp only [hal 24 (by decide), ite_true, Reach.opt_some]
  nocompiler_step
  · exact hw 16 (by omega)
  simp only [hal 16 (by decide), ite_true, Reach.opt_some]
  nocompiler_step
  · exact hw 8 (by omega)
  simp only [hal 8 (by decide), ite_true, Reach.opt_some]
  nocompiler_step
  · simpa using hw 0 (by omega)
  simp only [hfal8, ite_true, Reach.opt_some]
  -- The frame, abstracted: each slot holds what was stored, nothing else moved.
  have hcov : ∀ off, off + 8 ≤ 32 → (Spec.stackRegion s 32).covers (fb + BitVec.ofNat 64 off) 8 := by
    intro off ho
    unfold Region.covers Spec.stackRegion
    simp only [hF]
    rw [add_ofNat_sub_toNat fb (by omega)]; omega
  have hcov0 : (Spec.stackRegion s 32).covers fb 8 := by simpa using hcov 0 (by omega)
  generalize hM : writeLE (writeLE (writeLE (writeLE s.mem (fb + 24#64) (s.reg 1).toNat 8)
    (fb + 16#64) (s.reg 8).toNat 8) (fb + 8#64) (s.reg 9).toNat 8) fb (s.reg 18).toNat 8 = M
  have hMout : ∀ x, ¬ (Spec.stackRegion s 32).mem x → M x = s.mem x := by
    intro x hx
    rw [← hM, writeLE_of_not_mem hcov0 hx, writeLE_of_not_mem (hcov 8 (by omega)) hx,
      writeLE_of_not_mem (hcov 16 (by omega)) hx, writeLE_of_not_mem (hcov 24 (by omega)) hx]
  have hM0 : read64 M fb = s.reg 18 := by rw [← hM]; exact read64_writeLE_same _ _ _
  have hM8 : read64 M (fb + 8#64) = s.reg 9 := by
    rw [← hM]
    have := read64_writeLE_other (writeLE (writeLE (writeLE s.mem (fb + 24#64) (s.reg 1).toNat 8)
      (fb + 16#64) (s.reg 8).toNat 8) (fb + 8#64) (s.reg 9).toNat 8) fb (s.reg 18).toNat
      (i := 8) (j := 0) (by decide) (by decide) (by omega)
    simp only [BitVec.add_zero] at this
    rw [this]; exact read64_writeLE_same _ _ _
  have hM16 : read64 M (fb + 16#64) = s.reg 8 := by
    rw [← hM]
    have h1 := read64_writeLE_other (writeLE (writeLE (writeLE s.mem (fb + 24#64) (s.reg 1).toNat 8)
      (fb + 16#64) (s.reg 8).toNat 8) (fb + 8#64) (s.reg 9).toNat 8) fb (s.reg 18).toNat
      (i := 16) (j := 0) (by decide) (by decide) (by omega)
    have h2 := read64_writeLE_other (writeLE (writeLE s.mem (fb + 24#64) (s.reg 1).toNat 8)
      (fb + 16#64) (s.reg 8).toNat 8) fb (s.reg 9).toNat (i := 16) (j := 8) (by decide) (by decide) (by omega)
    simp only [BitVec.add_zero] at h1 h2
    rw [h1, h2]; exact read64_writeLE_same _ _ _
  have hM24 : read64 M (fb + 24#64) = s.reg 1 := by
    rw [← hM]
    have h1 := read64_writeLE_other (writeLE (writeLE (writeLE s.mem (fb + 24#64) (s.reg 1).toNat 8)
      (fb + 16#64) (s.reg 8).toNat 8) (fb + 8#64) (s.reg 9).toNat 8) fb (s.reg 18).toNat
      (i := 24) (j := 0) (by decide) (by decide) (by omega)
    have h2 := read64_writeLE_other (writeLE (writeLE s.mem (fb + 24#64) (s.reg 1).toNat 8)
      (fb + 16#64) (s.reg 8).toNat 8) fb (s.reg 9).toNat (i := 24) (j := 8) (by decide) (by decide) (by omega)
    have h3 := read64_writeLE_other (writeLE s.mem (fb + 24#64) (s.reg 1).toNat 8)
      fb (s.reg 8).toNat (i := 24) (j := 16) (by decide) (by decide) (by omega)
    simp only [BitVec.add_zero] at h1 h2 h3
    rw [h1, h2, h3]; exact read64_writeLE_same _ _ _
  -- mv s0, a3; mv s1, a2; call sum
  nocompiler_steps 4
  have hPle : ∀ (c : Word) (zs : List Word) (st : State), st.reg 2 = fb →
      (arrRegion c zs = arrRegion a xs ∨ arrRegion c zs = arrRegion b ys) →
      (spec.perm ⟨c, zs⟩ st).le (spec2.perm ⟨a, xs, b, ys⟩ s) := by
    intro c zs st hst hr
    apply Perm.le_of
    · intro r hr'
      simp only [Spec.perm, spec, List.mem_singleton] at hr'
      subst hr'
      rcases hr with e | e
      · exact ⟨arrRegion a xs, by simp [Spec.perm, spec2], e ▸ Region.within_refl _⟩
      · exact ⟨arrRegion b ys, by simp [Spec.perm, spec2], e ▸ Region.within_refl _⟩
    · intro r hr'
      simp only [Spec.perm, spec, List.nil_append, List.mem_singleton] at hr'
      subst hr'
      refine ⟨Spec.stackRegion s 32, by simp [Spec.perm, spec2], ?_⟩
      unfold Region.within Spec.stackRegion
      simp only [hst, hF]
      have : fb - BitVec.ofNat 64 0 - fb = 0 := by bv_omega
      rw [this]; simp
  refine Verified.call sum_verified ⟨a, xs⟩ ⟨by nocompiler_norm <;> rfl, by nocompiler_norm [hx],
    by nocompiler_norm <;> decide, by nocompiler_norm <;> decide, by nocompiler_norm <;> exact hfal⟩ ?_
    (Dom.sub_of_ranges (by decide))
    (hPle a xs _ (by nocompiler_norm) (.inl rfl)) ?_
  · refine ⟨by nocompiler_norm [ha0], by nocompiler_norm [ha1], hl1, hal1, ?_⟩
    nocompiler_norm
    exact arr64_congr hl1 harr1 fun x hx => hMout x (hd1 x hx)
  intro s1 hdone hfr
  obtain ⟨hx1, hpc1, hpres1, hpost1⟩ := hdone.resolve_right fun h => h.2.elim
  -- What the first call left: sp, s0, s1, s2 and the rest of the callee-saved
  -- registers, the result in a0, and all of memory.
  have hp1 : ∀ r ∈ preservedRegs, s1.reg r = if r = 8 then s.reg 13 else if r = 9 then s.reg 12
      else if r = 2 then fb else s.reg r := by
    intro r hr
    rw [hpres1 r hr]
    simp only [preservedRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      nocompiler_norm
  have hm1 : s1.mem = M := by
    funext x
    rw [hfr x ?_]
    · nocompiler_norm
    · rintro ⟨r, hr, hm⟩
      simp only [Spec.perm, spec, List.nil_append, List.mem_singleton] at hr
      subst hr
      exact absurd hm (by simp [Region.mem, Spec.stackRegion])
  have h1pc : s1.pc = 70104#64 := by rw [hpc1]; nocompiler_norm
  have h1a0 : s1.reg 10 = sumW xs := hpost1
  have h1s0 : s1.reg 8 = s.reg 13 := by simpa using hp1 8 (by decide)
  have h1s1 : s1.reg 9 = s.reg 12 := by simpa using hp1 9 (by decide)
  have h1sp : s1.reg 2 = fb := by simpa using hp1 2 (by decide)
  -- mv s2, a0; mv a0, s1; mv a1, s0; call sum
  nocompiler_steps 5 [h1pc, h1a0, h1s0, h1s1]
  refine Verified.call sum_verified ⟨b, ys⟩ ⟨by nocompiler_norm <;> rfl, by nocompiler_norm [hx1],
    by nocompiler_norm <;> decide, by nocompiler_norm <;> decide, by nocompiler_norm [h1sp] <;> exact hfal⟩ ?_
    (Dom.sub_of_ranges (by decide)) (hPle b ys _ (by nocompiler_norm [h1sp]) (.inr rfl)) ?_
  · refine ⟨by nocompiler_norm [ha2], by nocompiler_norm [ha3], hl2, hal2, ?_⟩
    nocompiler_norm [hm1]
    exact arr64_congr hl2 harr2 fun x hx => hMout x (hd2 x hx)
  intro s2 hdone hfr
  obtain ⟨hx2, hpc2, hpres2, hpost2⟩ := hdone.resolve_right fun h => h.2.elim
  have hp2 : ∀ r ∈ preservedRegs, s2.reg r = if r = 18 then sumW xs else s1.reg r := by
    intro r hr
    rw [hpres2 r hr]
    simp only [preservedRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      nocompiler_norm [h1a0]
  have hm2 : s2.mem = M := by
    funext x
    rw [hfr x ?_]
    · nocompiler_norm [hm1]
    · rintro ⟨r, hr, hm⟩
      simp only [Spec.perm, spec, List.nil_append, List.mem_singleton] at hr
      subst hr
      exact absurd hm (by simp [Region.mem, Spec.stackRegion])
  have h2pc : s2.pc = 70124#64 := by rw [hpc2]; nocompiler_norm
  have h2a0 : s2.reg 10 = sumW ys := hpost2
  have h2s2 : s2.reg 18 = sumW xs := by simpa using hp2 18 (by decide)
  have h2sp : s2.reg 2 = fb := by rw [hp2 2 (by decide)]; simpa using h1sp
  have hret : fb + 32#64 = s.reg 2 := by rw [← hF]; bv_omega
  -- add a0, a0, s2
  nocompiler_step [h2pc, h2a0, h2s2]
  -- ld ra, 24(sp); ld s0, 16(sp); ld s1, 8(sp); ld s2, 0(sp)
  nocompiler_step [h2sp]
  · exact Perm.canRead_of_canWrite (hw 24 (by omega))
  simp only [hal 24 (by decide), ite_true, Reach.opt_some]
  nocompiler_step [h2sp]
  · exact Perm.canRead_of_canWrite (hw 16 (by omega))
  simp only [hal 16 (by decide), ite_true, Reach.opt_some]
  nocompiler_step [h2sp]
  · exact Perm.canRead_of_canWrite (hw 8 (by omega))
  simp only [hal 8 (by decide), ite_true, Reach.opt_some]
  nocompiler_step [h2sp]
  · simpa using Perm.canRead_of_canWrite (hw 0 (by omega))
  simp only [hfal8, ite_true, Reach.opt_some]
  -- addi sp, sp, 32; ret
  nocompiler_step [h2sp, hret]
  nocompiler_step [hm2, hM24]
  rw [ret_mask he.retAligned]
  simp only [he.retAligned, ite_true, Reach.opt_some]
  apply Exec.final
  · left; nocompiler_norm; exact he.ret
  · left
    refine ⟨by nocompiler_norm [hx2], by nocompiler_norm, ?_, ?_⟩
    · intro r hr
      have h2 := hp2 r hr
      have h1 := hp1 r hr
      simp only [preservedRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        nocompiler_norm [hM16, hM8, hM0] <;> simp_all
    · show _ = sumW xs + sumW ys
      nocompiler_norm
      exact BitVec.add_comm _ _

end Examples.Sum2
