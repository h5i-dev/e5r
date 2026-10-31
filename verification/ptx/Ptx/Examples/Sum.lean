/-
M1: a sequential loop. `sum` (benchmarks/correct/sum.ptx, written directly in
PTX) has one thread add up `a[0..n)` and store the total to `out[0]`.

Theorem `sum_correct`: launched as one thread, for every `n` (the whole
`.u32` range), every `a` that fits and is aligned, every aligned `out` (which
may alias `a`: the store comes after the last load), every initial register
content and every interleaving (there is only one thread): no fault,
termination, and `out[0] = a[0] + … + a[n-1] (mod 2^32)` with every other
byte unchanged.

The loop is proved with `Safe.loop`: the invariant at the loop head
(pc 7) says the counter is `k ≤ n` and the accumulator holds the sum of the
first `k` elements; the measure is `n - k`.
-/
import Ptx.Logic.Launch1D
import Ptx.Tactics.Eval
import Ptx.Kernels.Sum

namespace Ptx.Examples.Sum
open Ptx

abbrev K := Ptx.Kernels.Sum.sum

def params (a out : Addr) (n : BitVec 32) : String → Val := fun x =>
  if x = "sum_a" then a else if x = "sum_out" then out else if x = "sum_n" then ext32 n else 0

def launch (a out : Addr) (n : BitVec 32) : Launch :=
  { grid := ⟨1, 1, 1⟩, block := ⟨1, 1, 1⟩, params := params a out n,
    alloc := [⟨a, 4 * n.toNat⟩, ⟨out, 4⟩] }

/-- `a[0] + … + a[k-1]` in 32-bit arithmetic. -/
def sumTo (m : Mem) (a : Addr) : Nat → BitVec 32
  | 0 => 0
  | k + 1 => sumTo m a k + rd32 m (elem a k)

def R (a : Addr) (N : Nat) (x : Addr) : Prop := ∃ j < N, covers (elem a j) 4 x
def W (out : Addr) (x : Addr) : Prop := covers out 4 x

/-- The loop head: counter `k`, measure `n - k`. -/
def Inv (a out : Addr) (n : BitVec 32) (m₀ : Mem) (v : Nat) (s : TState) (m : Mem) : Prop :=
  ∃ k ≤ n.toNat, v = n.toNat - k ∧ s.pc = 7 ∧ m = m₀ ∧ s.r "%rd1" = a ∧ s.r "%rd2" = out ∧
    s.r "%r1" = ext32 n ∧ s.r "%r2" = ext32 (sumTo m₀ a k) ∧ s.r "%r3" = ext32 (BitVec.ofNat 32 k)

theorem toNat_ofNat32 {k : Nat} (h : k < 2 ^ 32) : (BitVec.ofNat 32 k).toNat = k := by
  simp [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

theorem mulWide4u {k : Nat} (h : k < 2 ^ 32) :
    ext32 (BitVec.ofNat 32 k) * ext32 (lo32 (BitVec.ofInt 64 4)) = BitVec.ofNat 64 (4 * k) := by
  have : ext32 (lo32 (BitVec.ofInt 64 4)) = 4#64 := by decide
  rw [this]; apply BitVec.eq_of_toNat_eq
  simp [ext32, Nat.mod_eq_of_lt h]; omega

section
variable {a out : Addr} {n : BitVec 32} {m₀ : Mem}

theorem step (fa : Fits a n.toNat) (aa : a.toNat % 4 = 0) (ao : out.toNat % 4 = 0) (t : Tid) :
    ∀ v s m, Inv a out n m₀ v s m →
      Safe K (launch a out n).alloc ((launch a out n).ctx t) (R a n.toNat) (W out)
        (fun s m => (∃ v' < v, Inv a out n m₀ v' s m) ∨
          (action K ((launch a out n).ctx t) s = .done ∧ rd32 m out = sumTo m₀ a n.toNat ∧
            ∀ x, ¬ covers out 4 x → m x = m₀ x)) s m := by
  intro v s m hI
  obtain ⟨k, hk, hv, hpc, hm, h1, h2, hn, h3, h4⟩ := hI
  obtain ⟨pc, r, p⟩ := s
  simp only at hpc h1 h2 hn h3 h4
  subst hpc hm
  have hn32 := n.isLt
  have hz : BitVec.ofInt 64 0 = 0#64 := by decide
  refine (wp_sound (f := 20) (cut := fun pc => pc == 7) ?_).weaken fun s m h => h.1
  by_cases hkn : k = n.toNat
  · subst hkn
    have hb : n.ule (BitVec.ofNat 32 n.toNat) = true := by
      simp only [BitVec.ule, toNat_ofNat32 hn32, Nat.le_refl, decide_true]
    simp only [ptx_eval, K, Ptx.Kernels.Sum.sum, launch, params, h2, hn, h3, h4, hb, hz,
      BitVec.add_zero, bne_iff_ne, ne_eq, Bool.true_eq_false, not_false_eq_true]
    refine ⟨?_, fun x hx => .inl hx, .inr ⟨trivial, ?_, fun x hx => wr_outside hx⟩⟩
    · simp [accessOk, Region.holds, ao]
    · rw [rd32_wr_same]; simp [lo32, ext32]
  · have hlt : k < n.toNat := by omega
    have hb : n.ule (BitVec.ofNat 32 k) = false := by
      rw [Bool.eq_false_iff]; intro h
      simp only [BitVec.ule, toNat_ofNat32 (by omega : k < 2 ^ 32), decide_eq_true_eq] at h; omega
    have one : lo32 (BitVec.ofInt 64 1) = 1#32 := by decide
    simp only [ptx_eval, K, Ptx.Kernels.Sum.sum, launch, params, h1, h2, hn, h3, h4, hb, hz,
      bne_self_eq_false, mulWide4u (by omega : k < 2 ^ 32), BitVec.add_zero, elem_def, lo32_rd_b4,
      one]
    refine ⟨?_, fun x hx => .inr ⟨rfl, k, hlt, hx⟩, .inl ⟨n.toNat - (k + 1), by omega,
      k + 1, by omega, rfl, rfl, rfl, ?_, ?_, ?_, ?_, ?_⟩⟩
    · simp [accessOk, aligned_elem fa hlt aa, holds_elem fa hlt]
    all_goals simp only [upd, String.reduceEq, ↓reduceIte, h1, h2, hn]
    · simp [sumTo]
    · apply BitVec.eq_of_toNat_eq; simp [ext32, BitVec.toNat_ofNat]

/-- From the entry to the loop head. -/
theorem entry (t : Tid) (r : String → Val) (p : String → Bool) :
    Safe K (launch a out n).alloc ((launch a out n).ctx t) (R a n.toNat) (W out)
      (fun s m => ∃ v, Inv a out n m₀ v s m) ⟨0, r, p⟩ m₀ := by
  refine (wp_sound (f := 10) (cut := fun pc => pc == 7) ?_).weaken fun s m h => h.1
  simp only [ptx_eval, K, Ptx.Kernels.Sum.sum, launch, params]
  exact ⟨n.toNat, 0, Nat.zero_le _, by omega, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem thread (fa : Fits a n.toNat) (aa : a.toNat % 4 = 0) (ao : out.toNat % 4 = 0) (t : Tid)
    (r : String → Val) (p : String → Bool) :
    Safe K (launch a out n).alloc ((launch a out n).ctx t) (R a n.toNat) (W out)
      (fun s m => action K ((launch a out n).ctx t) s = .done ∧ rd32 m out = sumTo m₀ a n.toNat ∧
        ∀ x, ¬ covers out 4 x → m x = m₀ x) ⟨0, r, p⟩ m₀ :=
  (entry t r p).mono fun _ _ ⟨v, hI⟩ => Safe.loop (step fa aa ao t) v _ _ hI

end

theorem sum_correct (n : BitVec 32) (a out : Addr) (m₀ : Mem)
    (r₀ : Tid → String → Val) (p₀ : Tid → String → Bool)
    (fa : Fits a n.toNat) (aa : a.toNat % 4 = 0) (ao : out.toNat % 4 = 0) :
    let L := launch a out n
    let c₀ := Cfg.init r₀ p₀ m₀
    (∀ cfg, Reach K L c₀ cfg → ¬ Faults K L cfg) ∧
    (∀ cfg, Reach K L c₀ cfg → Done K L cfg ∨ ∃ cfg', Step K L cfg cfg') ∧
    (∃ bound, ∀ j cfg, Steps K L j c₀ cfg → j ≤ bound) ∧
    RaceFree K L c₀ ∧
    (∃ cfg, Reach K L c₀ cfg ∧ Done K L cfg) ∧
    (∀ cfg, Reach K L c₀ cfg → Done K L cfg →
      rd32 cfg.mem out = sumTo m₀ a n.toNat ∧ ∀ x, ¬ covers out 4 x → cfg.mem x = m₀ x) := by
  intro L c₀
  have h1 : L.OneD 1 1 := ⟨rfl, rfl⟩
  let P : Tid → Mem → Prop := fun _ M => rd32 M out = sumTo m₀ a n.toNat ∧ ∀ x, ¬ covers out 4 x → M x = m₀ x
  have hsolo : ∀ t ∈ L.threads, ∃ k, Solo K L.alloc (L.ctx t) (R a n.toNat) (W out)
      (s0 r₀ p₀ m₀ t) m₀ k ∧ P t (trace K L.alloc (L.ctx t) k (s0 r₀ p₀ m₀ t) m₀).2 := by
    intro t _
    exact ((thread fa aa ao t (r₀ t) (p₀ t)).weaken fun s m h => ⟨h.1, h.2⟩).solo
  have hdisj : ∀ t ∈ L.threads, ∀ u ∈ L.threads, t ≠ u → ∀ x,
      W out x → ¬ R a n.toNat x ∧ ¬ W out x := by
    intro t ht u hu htu
    exact absurd (h1.gid_inj ht hu (by have := h1.gid_lt ht; have := h1.gid_lt hu; simp at *; omega)) htu
  obtain ⟨bound, g⟩ := grid_sound (R := fun _ => R a n.toNat) (W := fun _ => W out) (P := P) hsolo hdisj
  refine ⟨g.noFault, g.progress, ⟨bound, g.bounded⟩, g.raceFree, g.exists_done, ?_⟩
  intro cfg hr hd
  obtain ⟨hown, hrest⟩ := g.final cfg hr hd
  have hm := (h1.owner_mem (i := 0) (by decide)).1
  obtain ⟨M, ⟨hP, hF⟩, hM⟩ := hown _ hm
  refine ⟨by rw [← hP]; exact rd32_congr fun x hx => hM x hx, fun x hx => ?_⟩
  by_cases hw : covers out 4 x
  · exact absurd hw hx
  · exact hrest x fun _ _ h => hw h

end Ptx.Examples.Sum
