/- e5r-proof ptx=00a3aa3c8853ab99495822aa10c28f98a5e88867c43ac036c61ec57cb280587c spec=bf776281c41e45abecbf18130b156d7e9c0f56f111abb49e05f2f54012035366 toolchain=leanprover/lean4:v4.35.0 -/
import E5rSpec

set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace E5rProof
open Ptx Ptx.Auto E5rSpec

/-- Independent byte-layout specification: source bit for output bit i. -/
def sourceBit (i : Nat) : Nat := 8 * (3 - i / 8) + i % 8

/-- The JSON contract implements the frozen bit-layout formula, for every word/mask. -/
theorem contract_layout (x mask : BitVec 32) (i : Nat) (hi : i < 32) :
    (spec.f (fun _ => mask) (fun _ => x)).getLsbD i =
      (x.getLsbD (sourceBit i) ^^ mask.getLsbD i) := by
  have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11 ∨ i = 12 ∨ i = 13 ∨ i = 14 ∨ i = 15 ∨ i = 16 ∨ i = 17 ∨ i = 18 ∨ i = 19 ∨ i = 20 ∨ i = 21 ∨ i = 22 ∨ i = 23 ∨ i = 24 ∨ i = 25 ∨ i = 26 ∨ i = 27 ∨ i = 28 ∨ i = 29 ∨ i = 30 ∨ i = 31 := by omega
  rcases cases with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 | h21 | h22 | h23 | h24 | h25 | h26 | h27 | h28 | h29 | h30 | h31
  all_goals subst i
  all_goals simp [spec, sourceBit, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight,
    BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_xor]

/-- The candidate swaps neighbors, then halfwords; this is not the contract expression. -/
def implementation (x : BitVec 32) : BitVec 32 :=
  let neighbors := ((x &&& 16711935) <<< 8) ||| ((x >>> 8) &&& 16711935)
  (neighbors <<< 16) ||| (neighbors >>> 16)

theorem implementation_layout (x : BitVec 32) (i : Nat) (hi : i < 32) :
    (implementation x).getLsbD i = x.getLsbD (sourceBit i) := by
  have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11 ∨ i = 12 ∨ i = 13 ∨ i = 14 ∨ i = 15 ∨ i = 16 ∨ i = 17 ∨ i = 18 ∨ i = 19 ∨ i = 20 ∨ i = 21 ∨ i = 22 ∨ i = 23 ∨ i = 24 ∨ i = 25 ∨ i = 26 ∨ i = 27 ∨ i = 28 ∨ i = 29 ∨ i = 30 ∨ i = 31 := by omega
  rcases cases with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 | h21 | h22 | h23 | h24 | h25 | h26 | h27 | h28 | h29 | h30 | h31
  all_goals subst i
  all_goals simp [implementation, sourceBit, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight,
    BitVec.getLsbD_and, BitVec.getLsbD_or]

theorem implementation_contract (x mask : BitVec 32) :
    implementation x ^^^ mask = spec.f (fun _ => mask) (fun _ => x) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [contract_layout x mask i hi, BitVec.getLsbD_xor, implementation_layout x i hi]

 theorem thread : spec.GuardedOk endian_xor := by
  intro A hpre m₀ t ht r p
  obtain ⟨⟨hcx, htx, hcy, hcz, hty, htz⟩, hg⟩ := Ptx.Auto.thread_facts ht
  have hsch := hpre.2.2.2
  simp only [ptx_spec, Ptx.Auto.MapSpec.SchedOk] at hsch
  have hGB := Ptx.Auto.mul32_le A.G A.B
  have hcB := Ptx.Auto.mul32_le t.ctaid.x A.B
  have hBc : A.B.toNat * t.ctaid.x.toNat = t.ctaid.x.toNat * A.B.toNat := Nat.mul_comm _ _
  have hBG : A.B.toNat * A.G.toNat = A.G.toNat * A.B.toNat := Nat.mul_comm _ _
  refine (wp_sound (f := 58) (cut := fun pc => false) ?_).weaken
    fun s m h => ⟨h.2.resolve_left (by simp), h.1⟩
  simp only [ptx_eval, endian_xor]
  ptx_spec_simp
  unfold gid at *
  ptx_addrs [A.base "input", A.base "output"] [t.ctaid.x.toNat * A.B.toNat + t.tid.x.toNat]
  ptx_branches
  all_goals (try and_intros)
  all_goals first
    | done
    | (with_reducible exact MapSpec.accessOk_elem hpre (by ptx_spec_simp) (by omega))
    | (with_reducible exact MapSpec.infoot_load (by ptx_spec_simp) (by omega))
    | (with_reducible exact MapSpec.infoot_store (by ptx_spec_simp) (by omega))
    | (intro hi; exfalso; omega)
    | (simp only [MapSpec.EPost]; intro hi; exfalso; omega)
    | (simp only [MapSpec.EPost, ptx_spec]
       intro hi
       rw [rd32_wr_same]
       simp only [MapSpec.val, ptx_spec, lo32_ext32, lo32_rd_b4]
       simp only [lo32, BitVec.reduceOfInt, BitVec.reduceSetWidth, BitVec.reduceToNat,
         Nat.min_def, Nat.reduceLeDiff, reduceIte]
       exact implementation_contract _ _)


 theorem correct : E5rSpec.statement :=
  correct_of_threadOk rfl (threadOk_of_guardedOk spec_sched thread)

end E5rProof
