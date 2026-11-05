-- UNFINISHED DEVELOPMENT PROOF: outstanding goals; no accepted proof claimed.
/- e5r-proof ptx=b9e3891749dcf4ef8df8ab909c75f56e9cd70f4154a3801b84e68c37ab2ab7aa spec=ad1992fcf2702962467a46814ae0188c0f470a972b0471dab422bfc919ff2e24 toolchain=leanprover/lean4:v4.35.0 -/
import E5rSpec
import Ptx.Auto.Tactic
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option linter.unusedSimpArgs false
namespace E5rProof
open Ptx Ptx.Auto Ptx.Auto.Packing Ptx.Auto.Packing.Spec
abbrev S := E5rSpec.spec
abbrev K := E5rSpec.«threshold»

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
  refine (wp_sound (f := 200) (cut := fun _ => false) ?_).weaken
    fun s m h => ⟨h.2.resolve_left (by simp),h.1⟩
  simp only [ptx_eval, K, E5rSpec.«threshold», launch, S, E5rSpec.spec]
  ptx_addrs [A.base "input", A.base "output"] [8*(t.ctaid.x.toNat * A.B.toNat + t.tid.x.toNat)+0, 8*(t.ctaid.x.toNat * A.B.toNat + t.tid.x.toNat)+1, 8*(t.ctaid.x.toNat * A.B.toNat + t.tid.x.toNat)+2, 8*(t.ctaid.x.toNat * A.B.toNat + t.tid.x.toNat)+3, 8*(t.ctaid.x.toNat * A.B.toNat + t.tid.x.toNat)+4, 8*(t.ctaid.x.toNat * A.B.toNat + t.tid.x.toNat)+5, 8*(t.ctaid.x.toNat * A.B.toNat + t.tid.x.toNat)+6, 8*(t.ctaid.x.toNat * A.B.toNat + t.tid.x.toNat)+7, t.ctaid.x.toNat * A.B.toNat + t.tid.x.toNat, (t.ctaid.x.toNat * A.B.toNat + t.tid.x.toNat)/8]
  ptx_branches
  all_goals simp only [hprod,hsum] at *
  all_goals (try and_intros)
  all_goals (first
    | trivial
    | (with_reducible exact access_input hp (by simp [S,E5rSpec.spec,Op.count]; omega))
    | (with_reducible exact access_output hp (by omega))
    | (apply load_foot (S := S) (j := 0) (by omega) (by decide))
    | (exact store_foot (S := S) (by omega))
    | (simp only [Post]; intro hi; exfalso; omega)
    | skip)
  all_goals trace_state

theorem correct : E5rSpec.statement := Spec.correct_of rfl thread
end E5rProof
