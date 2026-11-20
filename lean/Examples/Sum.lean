/-
`u64 sum(const u64 *a, u64 n)` from examples/sum.c, as clang -O2 compiled it
into examples/elf/sum.elf (the words are in Examples/Sum/Image.lean):

    11190  addi a2, zero, 0          s = 0
           block
    11194    beq  a1, zero, 0x111ac    n = 0: done
             loop
    11198      ld   a3, 0(a0)
    1119c      add  a2, a3, a2
    111a0      addi a1, a1, -1
    111a4      addi a0, a0, 8
    111a8      bne  a1, zero, 0x11198
    111ac  addi a0, a2, 0
    111b0  jalr zero, 0(ra)

The compiler rotated the loop and counts n down instead of i up; the proof
is about the code it wrote, not the source. The loop invariant at 0x11198,
after k elements: a0 = a + 8k, a1 = n - k, a2 = the sum of the first k.
-/
import Examples.Sum.Image
import NoCompiler.Vocab

namespace Examples.Sum
open NoCompiler Examples.Sum.Image

/-- The sum of a list of words, modulo 2^64. -/
def sumW (xs : List Word) : Word := xs.foldl (· + ·) 0

/-- The logical arguments: the array's address and contents. -/
structure Args where
  a : Word
  xs : List Word

/-- `u64 sum(const u64 *a, u64 n)`: a0 = a, a1 = n; returns the sum in a0.
    It may read the array and nothing else, and uses no stack. -/
def spec : Spec Args where
  pre := fun ⟨a, xs⟩ s => s.reg Reg.a0 = a ∧ s.reg Reg.a1 = BitVec.ofNat 64 xs.length ∧
    8 * xs.length < 2^64 ∧ aligned a 8 ∧ arr64 s.mem a xs
  post := fun ⟨_, xs⟩ _ s' => s'.reg Reg.a0 = sumW xs
  reads := fun ⟨a, xs⟩ _ => [arrRegion a xs]


/-- The return path, `mv a0, a2; ret`, from either way of reaching it. -/
theorem tail (s0 s : State) (ar : Args) (hv : s.reg 12 = sumW ar.xs)
    (he : Entry sum_dom sum_entry s0)
    (hpc : s.pc = 0x111ac#64) (hx : s.exit = none) (hr : Same s0 s [10, 11, 12, 13]) :
    Exec code (spec.perm ar s0) sum_dom (spec.Done ar s0) s := by
  nocompiler_step [hpc]
  nocompiler_step [hpc]
  rw [hr 1 (by decide), ret_mask he.retAligned]
  simp only [he.retAligned, ite_true]
  nocompiler_norm
  apply Exec.final
  · left; simpa using he.ret
  · left
    refine ⟨by simp [hx], by simp, ?_, ?_⟩
    · intro r hr'
      simp only [preservedRegs, List.mem_cons, List.not_mem_nil, or_false] at hr'
      rcases hr' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        (nocompiler_norm; exact hr _ (by decide))
    · simp [spec, hv]

theorem sumW_take_succ (xs : List Word) (k : Nat) (h : k < xs.length) :
    sumW (xs.take (k + 1)) = sumW (xs.take k) + xs[k] := Vocab.foldl_take_succ _ _ xs k h

/-- `sum` as compiled: correct, memory-safe, terminating, ABI-preserving. -/
theorem sum_verified : VerifiedImg code sum_dom sum_entry spec := by
  rintro ⟨a, xs⟩ s he ⟨ha0, ha1, hlen, hal, harr⟩
  have hpc : s.pc = 0x11190#64 := he.pc
  have hx := he.live
  nocompiler_step [hpc]
  nocompiler_step [hpc]
  have hn : xs.length < 2^64 := by omega
  have hsame0 : Same s ((s.setReg 12 0).setPc 70060#64) [10, 11, 12, 13] :=
    (Same.refl s _).setReg 0 (by decide) |>.setPc _
  split
  · -- n = 0: straight to the return
    rename_i hz
    have h0 : xs.length = 0 := by
      have : s.reg 11 = 0 := by simpa using hz
      rw [ha1] at this
      have := congrArg BitVec.toNat this
      simp at this; omega
    rw [Reach.opt_some]
    apply tail s _ ⟨a, xs⟩ _ he (by simp) (by simp [hx]) ((Same.refl s _).setReg 0 (by decide) |>.setPc _)
    simp [List.length_eq_zero_iff.1 h0, sumW]
  · rename_i hz
    rw [Reach.opt_some]
    let I : State → Prop := fun u => ∃ k, k < xs.length ∧ u.pc = 0x11198#64 ∧ u.exit = none ∧
      u.reg 10 = a + BitVec.ofNat 64 (8 * k) ∧ u.reg 11 = BitVec.ofNat 64 (xs.length - k) ∧
      u.reg 12 = sumW (xs.take k) ∧ Same s u [10, 11, 12, 13] ∧ u.mem = s.mem
    refine Reach.loop I (fun u => (u.reg 11).toNat) ?_ _ ?_
    · rintro u ⟨k, hk, hpc', hx', h10, h11, h12, hsame, hmem⟩
      have h8k : 8 * k + 8 ≤ 8 * xs.length := by omega
      -- ld a3, 0(a0)
      nocompiler_step [hpc']
      · right
        refine ⟨arrRegion a xs, by simp [Spec.perm, spec], ?_⟩
        simp only [Region.covers, arrRegion, h10, add_ofNat_sub_toNat a (show 8 * k < 2 ^ 64 by omega)]
        omega
      have hal' : aligned (a + BitVec.ofNat 64 (8 * k)) 8 :=
        aligned_add_ofNat hal (by omega) (by decide)
      rw [h10]; simp only [hal', ite_true, Reach.opt_some]
      -- add a2, a3, a2; addi a1, a1, -1; addi a0, a0, 8; bnez a1, loop
      nocompiler_steps 4 [h10, h11, h12]
      have hm : read64 u.mem (a + BitVec.ofNat 64 (8 * k)) = xs[k] := by rw [hmem]; exact harr k hk
      have h11' := ofNat_add_allOnes (xs.length - k) (by omega) (by omega)
      have h10' : a + BitVec.ofNat 64 (8 * k) + 8#64 = a + BitVec.ofNat 64 (8 * (k + 1)) :=
        add_ofNat_add a (8 * k) 8
      have h12' : xs[k] + sumW (List.take k xs) = sumW (List.take (k + 1) xs) := by
        rw [sumW_take_succ xs k hk, BitVec.add_comm]
      have hsub : xs.length - k - 1 = xs.length - (k + 1) := by omega
      simp only [hm, h11', h10', h12', hsub]
      by_cases hk1 : k + 1 < xs.length
      · -- taken: back to the loop head with k + 1
        have hne : (BitVec.ofNat 64 (xs.length - (k + 1)) != (0 : Word)) = true := by
          simp only [bne_iff_ne, ne_eq]
          rw [ofNat_eq_zero_iff (by omega)]; omega
        simp only [hne, ite_true]
        nocompiler_norm
        refine .done (.inr ⟨⟨k + 1, hk1, rfl, hx', by nocompiler_norm, by nocompiler_norm,
          by nocompiler_norm, ?_, by nocompiler_norm [hmem]⟩, ?_⟩)
        · nocompiler_same
        · nocompiler_norm [h11]
          rw [toNat_ofNat_of_lt (by omega), toNat_ofNat_of_lt (by omega)]; omega
      · -- not taken: the return
        have hk1 : k + 1 = xs.length := by omega
        have hne : (BitVec.ofNat 64 (xs.length - (k + 1)) != (0 : Word)) = false := by
          rw [← hk1, Nat.sub_self]; rfl
        simp only [hne, Bool.false_eq_true, ite_false, Reach.opt_some]
        refine Reach.mono (fun _ h => Or.inl h)
          (tail s _ ⟨a, xs⟩ ?_ he (by nocompiler_norm) (by nocompiler_norm [hx']) ?_)
        · nocompiler_norm; rw [hk1, List.take_length]
        · nocompiler_same
    · refine ⟨0, ?_, by simp, by simp [hx], by simp [ha0], by simp [ha1], by simp [sumW], ?_, by simp⟩
      · have : s.reg 11 ≠ 0 := by simpa using hz
        rw [ha1] at this
        refine Nat.pos_of_ne_zero fun h0 => this ?_
        simp [h0]
      · exact (Same.refl s _).setReg 0 (by decide) |>.setPc _

/-- What `sum_verified` says about the machine, for a run started from a
    loaded image: no fault and only permitted accesses, the result on return,
    and termination (NoCompiler/Adequacy.lean). -/
theorem sum_hw (ar : Args) (s : State) (he : Entry sum_dom sum_entry s) (hpre : spec.pre ar s)
    (hl : code.Loaded s.mem) (hp : Protected code (spec.perm ar s)) :
    (∀ t, HwRun sum_dom s t → sum_dom.mem t.pc → t.exit = none →
      (∃ t', HwStep t t') ∧ ∀ t', HwStep t t' → Step code (spec.perm ar s) t t') ∧
    (∀ t, HwRun sum_dom s t → Final sum_dom t → spec.Done ar s t) ∧
    ¬ ∃ f : Nat → State, f 0 = s ∧ ∀ n, sum_dom.mem (f n).pc ∧ HwStep (f n) (f (n + 1)) :=
  sum_verified.hw ar s he hpre hl hp (by decide)

end Examples.Sum
