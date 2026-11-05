/- e5r-proof ptx=e7793391a8cbc1a491c456f2ae1b25c6ba4bf2dac4a7ec5eebe7a3801d30263e spec=ba6465b85f46da4071311de702f57052e58fe56c846a7aea5c54a606637277cc toolchain=leanprover/lean4:v4.35.0 -/
import E5rSpec
import Ptx.Auto.Tactic
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option linter.unusedSimpArgs false
namespace E5rProof
open Ptx Ptx.Auto Ptx.Auto.Packing Ptx.Auto.Packing.Spec
abbrev S := E5rSpec.spec
abbrev K := E5rSpec.«unpack»

 def spread (x : BitVec 32) : BitVec 32 :=
   let z := x &&& 15
   let z := (z ||| z <<< (14 : Nat)) &&& 196611
   (z ||| z <<< (7 : Nat)) &&& 16843009
 theorem spread_bit (x : BitVec 32) (k : Nat) (hk : k < 32) :
    (spread x).getLsbD k = (k % 8 == 0 && x.getLsbD (k/8)) := by
   have h : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 ∨ k = 8 ∨ k = 9 ∨ k = 10 ∨ k = 11 ∨ k = 12 ∨ k = 13 ∨ k = 14 ∨ k = 15 ∨ k = 16 ∨ k = 17 ∨ k = 18 ∨ k = 19 ∨ k = 20 ∨ k = 21 ∨ k = 22 ∨ k = 23 ∨ k = 24 ∨ k = 25 ∨ k = 26 ∨ k = 27 ∨ k = 28 ∨ k = 29 ∨ k = 30 ∨ k = 31 := by omega
   rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
   all_goals subst k
   all_goals simp [spread, BitVec.getLsbD_and, BitVec.getLsbD_or,
     BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ofNat]

theorem shift_amount (x : BitVec 32) :
    min ((x &&& (7#32)) <<< (2 : Nat)).toNat 32 = 4*(x.toNat%8) := by
  have hx : (x &&& (7#32)).toNat = x.toNat % 8 := by
    simpa only [BitVec.toNat_and, BitVec.reduceToNat, Nat.reducePow, Nat.reduceSub] using Nat.and_two_pow_sub_one_eq_mod x.toNat 3
  simp only [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, hx]
  have := Nat.mod_lt x.toNat (by decide : 0 < 8)
  omega

theorem thread : S.ThreadOk K := by
  intro A hp m₀ t ht r p
  have hd := S.oneD A
  obtain ⟨hc,htt,hy,hz,hty,htz⟩ := hd.thread ht
  have hg := hd.gid_lt ht
  obtain ⟨fi,fo,ai,ao,sep,htail,hn,hmax⟩ := hp
  have hp : S.Pre A := ⟨fi,fo,ai,ao,sep,htail,hn,hmax⟩
  simp only [S, E5rSpec.spec, Op.iw, Op.count, reduceIte, Nat.one_mul, true_implies] at fi fo htail
  have hBc : A.B.toNat * t.ctaid.x.toNat = t.ctaid.x.toNat * A.B.toNat := Nat.mul_comm _ _
  have hg32 := hd.gid_bv ht hmax
  have hprod : t.ctaid.x.toNat * A.B.toNat % 4294967296 = t.ctaid.x.toNat * A.B.toNat :=
    Nat.mod_eq_of_lt (by unfold gid at hg; omega)
  have hsum : (t.ctaid.x.toNat * A.B.toNat + t.tid.x.toNat) % 4294967296 = t.ctaid.x.toNat * A.B.toNat + t.tid.x.toNat :=
    Nat.mod_eq_of_lt (by unfold gid at hg; omega)
  unfold gid at *
  refine (wp_sound (f := 40) (cut := fun _ => false) ?_).weaken
    fun s m h => ⟨h.2.resolve_left (by simp),h.1⟩
  simp only [ptx_eval, K, E5rSpec.«unpack», launch, S, E5rSpec.spec]
  ptx_addrs [A.base "input", A.base "output"] [t.ctaid.x.toNat * A.B.toNat + t.tid.x.toNat, (t.ctaid.x.toNat * A.B.toNat + t.tid.x.toNat)/8]
  ptx_branches
  all_goals simp only [hprod,hsum] at *
  all_goals (try and_intros)
  all_goals (first
    | trivial
    | (simpa only [launch,S,E5rSpec.spec] using
        (access_input hp (i := (t.ctaid.x.toNat * A.B.toNat + t.tid.x.toNat)/8)
          (by simp [S,E5rSpec.spec,Op.count]; omega)))
    | (simpa only [launch,S,E5rSpec.spec] using
        (access_output hp (i := t.ctaid.x.toNat * A.B.toNat + t.tid.x.toNat) (by omega)))
    | (apply load_foot (S := S) (j := 0) (by omega) (by decide))
    | (exact store_foot (S := S) (by omega))
    | (simp only [Post]; intro hi; exfalso; omega)
    | skip)
  all_goals (
    simp only [Post]
    intro hi k hk
    rw [rd32_wr_same]
    simp only [lo32_ext32, lo32_rd_b4]
    simp only [lo32, BitVec.reduceOfInt, BitVec.reduceSetWidth, BitVec.reduceToNat,
      (show min 2 32 = 2 from rfl), (show min 14 32 = 14 from rfl), (show min 7 32 = 7 from rfl)]
    rw [shift_amount, hg32]
    change (spread ((rd32 m₀ (elem (A.base "input") ((t.ctaid.x.toNat * A.B.toNat + t.tid.x.toNat)/8))) >>>
      (4*((t.ctaid.x.toNat * A.B.toNat + t.tid.x.toNat)%8)))).getLsbD k = _
    rw [spread_bit _ k hk]
    simp only [bit, BitVec.getLsbD_ushiftRight]
  )

theorem correct : E5rSpec.statement := Spec.correct_of rfl thread
end E5rProof
