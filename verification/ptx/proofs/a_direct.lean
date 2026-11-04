/- e5r-proof ptx=54c18301c47eebc7977431d6f215b5bae29e41b158dfe541fe8170141b31b44d spec=ce6a9031796b1300d647a23fc92b23f34cefbeb4478df82877b5a4f78ed8fdc6 toolchain=leanprover/lean4:v4.35.0 -/
/-
A supplied proof (docs/verification/ptx.md, "Supplied proofs") for
`m5/m4/kernels/a_direct.ptx`: every thread with `gid < n` adds `x[gid]` to
`*out` with one `atom.global.add.u32`. There is no shared array and no
barrier, so the `reduce32` automation does not apply (`unsupported`), but the
class statement does: `*out` ends as its initial value plus the sum of
`x[0 .. min(n, G·B))`.

The proof is one phase of `phase_sound` per thread, with `*out` the
accumulator cell and each thread's element its ghost contribution.

Check it with
  e5r ptx check m5/m4/kernels/a_direct.ptx --spec m5/m4/specs/a_direct.json \
    --proof proofs/a_direct.lean
-/
import E5rSpec

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace E5rProof
open Ptx Ptx.Auto Ptx.Auto.Block Ptx.Auto.Reduce32 E5rSpec

abbrev K := E5rSpec.«a_direct»

section
variable (A : Block.Args spec)

/-- The global index of a thread. -/
def gid (t : Tid) : Nat := t.ctaid.x.toNat * A.B.toNat + t.tid.x.toNat

/-- A thread reads its element when `gid < n` and writes nothing: its atomic
addition to `*out` is the accumulator cell, not a footprint. -/
def foot (t : Tid) (_ : Nat) : Foot :=
  { r := fun l => l.1 = .global ∧ gid A t < A.n.toNat ∧ covers (elem A.x (gid A t)) 4 l.2
    w := fun _ => False }

def phased (m₀ : Mem) (sh₀ : Dim3 → Mem) : Phased where
  P := fun _ => 1
  F := foot A
  T := fun _ _ s => s.pc = 0
  N := fun _ _ => 24
  M := fun b _ => ⟨m₀, sh₀ b⟩
  bpc := fun _ _ => 0
  Cell := fun a => a = A.out
  Δ := fun t _ a => if gid A t < A.n.toNat ∧ a = A.out then ext32 (rd32 m₀ (elem A.x (gid A t))) else 0

set_option maxHeartbeats 4000000 in
theorem phase (hpre : Pre K 1 A) (m₀ : Mem) (sh₀ : Dim3 → Mem) {t : Tid}
    (ht : t ∈ (A.launch 1).threads) (s : TState) (hs : s.pc = 0) :
    Run K ((A.launch 1).allocs K) ((A.launch 1).ctx t) (foot A t 0) (fun a => a = A.out) add32
      ((phased A m₀ sh₀).J K (A.launch 1) t 0) 24 s ⟨m₀, sh₀ t.ctaid⟩ (fun _ => 0) := by
  obtain ⟨pc, r, p⟩ := s
  simp only at hs; subst hs
  obtain ⟨hc, hi, hcB, hGB, -, -, -, -⟩ := A.thread_facts hpre.2.2.1 ht
  have fx := hpre.2.2.2.1
  have xal := hpre.2.2.2.2.1
  have fout := hpre.2.2.2.2.2.1
  have oal := hpre.2.2.2.2.2.2.1
  have hg := A.gid_toNat hcB hGB
  have hcB' : t.ctaid.x.toNat * A.B.toNat < 2 ^ 32 := by omega
  refine (wpR_sound (cut := fun _ => false) ?_).weaken fun s h d hq => hq.1
  simp only [ptx_eval, K, E5rSpec.«a_direct», Block.Args.launch, Block.Args.params, spec_input,
    spec_output, spec_length, Phased.J, phased, foot, gid, List.map_cons, List.map_nil]
  ptx_branches4
  all_goals ptx_addrs4 [A.x, A.out] [t.ctaid.x.toNat * A.B.toNat + t.tid.x.toNat, 0]
  all_goals (try and_intros)
  all_goals first
    | trivial
    | (intro _ h; exact h.elim)
    | (exfalso; omega)
    | exact accessOk_elem_mem (N := A.n.toNat) (by simp) fx xal (by omega)
    | exact accessOk_elem_mem (N := 1) (by simp) fout oal (by omega)
    | exact elem_zero _
    | exact fun y hy => .inl ⟨rfl, by omega, hy⟩
    | exact fun y hy => .inl ⟨trivial, by omega, hy⟩
    | (funext a
       have hn : ¬ (t.ctaid.x.toNat * A.B.toNat + t.tid.x.toNat < A.n.toNat ∧ a = A.out) :=
         fun h => absurd h.1 (by omega)
       simp only [hn, ↓reduceIte])
    | (refine ⟨_, addsTo_add _, fun v => ⟨?_, fun _ h => h.elim, trivial⟩⟩
       funext a
       simp only [Ghost.acc, add32_op, lo32_rd_b4, lo32_ext32, lo32_zero, BitVec.zero_add, elem_zero A.out]
       by_cases ha : a = A.out
       · subst ha; simp [show t.ctaid.x.toNat * A.B.toNat + t.tid.x.toNat < A.n.toNat by omega]
       · simp [ha])
  done

theorem ok (hpre : Pre K 1 A) (m₀ : Mem) (sh₀ : Dim3 → Mem) (r₀ : Tid → String → Val)
    (p₀ : Tid → String → Bool) : (phased A m₀ sh₀).Ok K (A.launch 1) r₀ p₀ m₀ sh₀ := by
  have fx := hpre.2.2.2.1
  have fout := hpre.2.2.2.2.2.1
  have hsep := hpre.2.2.2.2.2.2.2.1
  refine ⟨fun _ _ => by simp [phased], fun _ _ => rfl, fun _ _ _ => rfl, ?_, fun _ _ _ _ _ _ => rfl,
    ?_, ?_, ?_, ?_⟩
  · intro t ht k hk s hs
    simp only [phased] at hk hs ⊢
    obtain rfl : k = 0 := by omega
    exact phase A hpre m₀ sh₀ ht s hs
  · intro t _ u _ _ _ k _ x hw _
    exact hw
  · intro t _ u _ _ k _ j' _ a hw _
    exact hw
  · -- `*out` is in nobody's footprint
    intro t ht k a ha y hy htc
    simp only [phased] at ha htc
    subst ha
    obtain ⟨-, -, hcB, -⟩ := A.thread_facts hpre.2.2.1 ht
    have hc0 : covers (elem A.out 0) 4 y := by rw [elem_zero]; exact hy
    rcases htc with ⟨-, hlt, hcv⟩ | h
    · exact elem_disjoint₂ fout fx (by omega) (by omega : 0 < 1) hlt hc0 hcv
    · exact h
  · intro a b ha hb hab
    simp only [phased] at ha hb
    exact absurd (ha.trans hb.symm) hab

end

theorem correct : E5rSpec.statement := by
  intro A hpre m₀ sh₀ r₀ p₀ L c₀
  have R := Phased.phase_sound (ok A hpre m₀ sh₀ r₀ p₀)
  refine ⟨R.noFault, R.progress, R.bounded, R.raceFree,
    Phased.exists_done_of R.progress R.bounded, fun c hc hd => ?_⟩
  obtain ⟨-, hun, hcell⟩ := R.final c hc hd
  refine ⟨?_, fun y hy => hun y (fun t _ k _ h => h) ?_⟩
  · rw [cell_add32 (hcell A.out rfl)]
    congr 1
    simp only [phased, and_true, lo32_tfold_add32, lo32_afold_add32, accUpTo]
    refine (tsum_congr fun t _ => ?_).trans
      (tsum_oneD_gid (A.launch_oneD 1) (fun i => if i < A.n.toNat then rd32 m₀ (elem A.x i) else 0))
    simp only [gid]
    split <;> (rename_i h; simp only [h, ↓reduceIte, lo32_ext32]; first | rfl | exact BitVec.zero_add _)
  · intro b hb; simp only [phased] at hb; subst hb; exact hy

end E5rProof
