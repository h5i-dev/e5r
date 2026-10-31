/-
`vadd` as compiled by nvcc 13.2 (benchmarks/correct/vadd_nvcc.{cu,ptx}),
verified on its PTX for every input length and every launch in range.

```c
extern "C" __global__ void vadd(const int* a, const int* b, int* c, int n) {
  int i = blockIdx.x * blockDim.x + threadIdx.x;
  if (i < n) c[i] = a[i] + b[i];
}
```

Theorem `vadd_correct`: for a 1-D launch of `G` CTAs of `B` threads with
`G * B ≤ 2^31` threads covering `n < 2^31` elements, arrays that fit in the
address space and are 4-byte aligned, and an output array that overlaps
neither input (the inputs may alias each other), under every interleaving and
every initial register content: no thread faults, every execution
terminates, there is no data race, and when all threads are done
`c[i] = a[i] + b[i] (mod 2^32)` for every `i < n` and no other byte of memory
has changed. A finished execution exists, so this is not vacuous.

The preconditions are the ones the PTX needs, found by the proof:

* `G * B ≤ 2^31`: `mad.lo.s32` computes the index in 32 bits and `setp.ge.s32`
  compares it signed. With more threads the index wraps negative, passes the
  bounds check, and `mul.wide.s32` turns it into an address below `a`
  (benchmarks/buggy shows the unguarded version faulting).
* `n < 2^31`: `n` is an `int`; `n = 2^31` as a `.u32` parameter is negative
  and the kernel writes nothing.
* `n ≤ G * B`: the kernel has no grid-stride loop; with fewer threads the
  tail is never written (compare Map.lean).
-/
import Ptx.Logic.Launch1D
import Ptx.Tactics.Eval
import Ptx.Kernels.VAddNvcc

namespace Ptx.Examples.VectorAdd
open Ptx

abbrev K := Ptx.Kernels.VAddNvcc.vadd

def params (a b c : Addr) (n : BitVec 32) : String → Val := fun x =>
  if x = "vadd_param_0" then a else if x = "vadd_param_1" then b
  else if x = "vadd_param_2" then c else if x = "vadd_param_3" then ext32 n else 0

/-- The launch: `G` CTAs of `B` threads, the three arrays as the only
allocations. -/
def launch (G B : BitVec 32) (a b c : Addr) (n : BitVec 32) : Launch :=
  { grid := ⟨G, 1, 1⟩, block := ⟨B, 1, 1⟩, params := params a b c n,
    alloc := [⟨a, 4 * n.toNat⟩, ⟨b, 4 * n.toNat⟩, ⟨c, 4 * n.toNat⟩] }

theorem launch_oneD (G B n : BitVec 32) (a b c : Addr) : (launch G B a b c n).OneD G B :=
  ⟨rfl, rfl⟩

/-- Thread `t` reads `a[gid]` and `b[gid]`, and writes `c[gid]`, if `gid < n`. -/
def R (B : BitVec 32) (a b : Addr) (N : Nat) (t : Tid) (x : Addr) : Prop :=
  gid B t < N ∧ (covers (elem a (gid B t)) 4 x ∨ covers (elem b (gid B t)) 4 x)

def W (B : BitVec 32) (c : Addr) (N : Nat) (t : Tid) (x : Addr) : Prop :=
  gid B t < N ∧ covers (elem c (gid B t)) 4 x

/-- What one thread leaves behind, relative to the initial memory `m`. -/
def Post (B : BitVec 32) (a b c : Addr) (N : Nat) (m : Mem) (t : Tid) (M : Mem) : Prop :=
  gid B t < N → rd32 M (elem c (gid B t)) = rd32 m (elem a (gid B t)) + rd32 m (elem b (gid B t))

/-- One thread, run alone. -/
theorem thread {G B n : BitVec 32} {a b c : Addr} {t : Tid} (m : Mem) (r : String → Val)
    (p : String → Bool) (ht : t ∈ (launch G B a b c n).threads) (hGB : G.toNat * B.toNat ≤ 2 ^ 31)
    (hn : n.toNat < 2 ^ 31) (fa : Fits a n.toNat) (fb : Fits b n.toNat) (fc : Fits c n.toNat)
    (aa : a.toNat % 4 = 0) (ab : b.toNat % 4 = 0) (ac : c.toNat % 4 = 0) :
    wp K (launch G B a b c n).alloc ((launch G B a b c n).ctx t) (R B a b n.toNat t)
      (W B c n.toNat t) (fun _ => false) (fun _ M => Post B a b c n.toNat m t M) 30 ⟨0, r, p⟩ m := by
  have hg := (launch_oneD G B n a b c).gid_bv ht hGB
  have hlt := (launch_oneD G B n a b c).gid_lt ht
  simp only [ptx_eval, K, Ptx.Kernels.VAddNvcc.vadd, launch, params]
  generalize t.ctaid.x * B + t.tid.x = g at *
  have h4 := mulWide4 (g := g) (by omega)
  have hz : BitVec.ofInt 64 0 = 0#64 := by decide
  simp only [h4, hz, BitVec.add_zero, hg, elem_def, lo32_rd_b4]
  by_cases hc : n.toNat ≤ gid B t
  · have : (n.sle g != false) = true := by
      have := (sle_nonneg (g := g) hn (by omega)).mpr (by omega); simp [this]
    simp only [this]; intro h; omega
  · have : ¬ (n.sle g != false) = true := by
      have := mt (sle_nonneg (g := g) hn (by omega)).mp (by omega); simpa using this
    simp only [this]
    have hi : gid B t < n.toNat := by omega
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [accessOk, aligned_elem fb hi ab, holds_elem fb hi]
    · intro x hx; exact .inr ⟨rfl, hi, .inr hx⟩
    · simp [accessOk, aligned_elem fa hi aa, holds_elem fa hi]
    · intro x hx; exact .inr ⟨rfl, hi, .inl hx⟩
    · simp [accessOk, aligned_elem fc hi ac, holds_elem fc hi]
    · intro x hx; exact .inl ⟨hi, hx⟩
    · intro _; rw [rd32_wr_same]; simp [lo32, ext32, BitVec.add_comm]

theorem vadd_correct (G B n : BitVec 32) (a b c : Addr) (m₀ : Mem)
    (r₀ : Tid → String → Val) (p₀ : Tid → String → Bool)
    (hGB : G.toNat * B.toNat ≤ 2 ^ 31) (hcov : n.toNat ≤ G.toNat * B.toNat) (hn : n.toNat < 2 ^ 31)
    (fa : Fits a n.toNat) (fb : Fits b n.toNat) (fc : Fits c n.toNat)
    (aa : a.toNat % 4 = 0) (ab : b.toNat % 4 = 0) (ac : c.toNat % 4 = 0)
    (sa : c.toNat + 4 * n.toNat ≤ a.toNat ∨ a.toNat + 4 * n.toNat ≤ c.toNat)
    (sb : c.toNat + 4 * n.toNat ≤ b.toNat ∨ b.toNat + 4 * n.toNat ≤ c.toNat) :
    let L := launch G B a b c n
    let c₀ := Cfg.init r₀ p₀ m₀
    (∀ cfg, Reach K L c₀ cfg → ¬ Faults K L cfg) ∧
    (∀ cfg, Reach K L c₀ cfg → Done K L cfg ∨ ∃ cfg', Step K L cfg cfg') ∧
    (∃ bound, ∀ j cfg, Steps K L j c₀ cfg → j ≤ bound) ∧
    RaceFree K L c₀ ∧
    (∃ cfg, Reach K L c₀ cfg ∧ Done K L cfg) ∧
    (∀ cfg, Reach K L c₀ cfg → Done K L cfg →
      (∀ i < n.toNat, rd32 cfg.mem (elem c i) = rd32 m₀ (elem a i) + rd32 m₀ (elem b i)) ∧
      (∀ x, (∀ i < n.toNat, ¬ covers (elem c i) 4 x) → cfg.mem x = m₀ x)) := by
  intro L c₀
  have h1 := launch_oneD G B n a b c
  have hsolo : ∀ t ∈ L.threads, ∃ k, Solo K L.alloc (L.ctx t) (R B a b n.toNat t) (W B c n.toNat t)
      (s0 r₀ p₀ m₀ t) m₀ k ∧ Post B a b c n.toNat m₀ t (trace K L.alloc (L.ctx t) k (s0 r₀ p₀ m₀ t) m₀).2 := by
    intro t ht
    have := wp_sound (thread m₀ (r₀ t) (p₀ t) ht hGB hn fa fb fc aa ab ac)
    exact (this.weaken fun s m h => ⟨h.2.resolve_left (by simp), h.1⟩).solo
  have hdisj : ∀ t ∈ L.threads, ∀ u ∈ L.threads, t ≠ u → ∀ x,
      W B c n.toNat t x → ¬ R B a b n.toNat u x ∧ ¬ W B c n.toNat u x := by
    intro t ht u hu htu x ⟨hit, hx⟩
    refine ⟨fun ⟨hiu, hr⟩ => ?_, fun ⟨hiu, hw⟩ => ?_⟩
    · rcases hr with hr | hr
      · exact elem_disjoint₂ fc fa sa hit hiu hx hr
      · exact elem_disjoint₂ fc fb sb hit hiu hx hr
    · exact elem_disjoint fc hit hiu (fun h => htu (h1.gid_inj ht hu h)) hx hw
  obtain ⟨bound, g⟩ := grid_sound (P := Post B a b c n.toNat m₀) hsolo hdisj
  refine ⟨g.noFault, g.progress, ⟨bound, g.bounded⟩, g.raceFree, g.exists_done, ?_⟩
  intro cfg hr hd
  obtain ⟨hown, hrest⟩ := g.final cfg hr hd
  refine ⟨fun i hi => ?_, fun x hx => hrest x fun t ht ⟨hit, hw⟩ => hx _ hit hw⟩
  obtain ⟨hm, hgi⟩ := h1.owner_mem (i := i) (by omega)
  obtain ⟨M, hP, hM⟩ := hown _ hm
  have := hP (by rw [hgi]; exact hi)
  rw [hgi] at this
  rw [← this]
  exact rd32_congr fun x hx => hM x ⟨by rw [hgi]; exact hi, by rw [hgi]; exact hx⟩

/-- The hypotheses are satisfiable: two CTAs of 128 threads, 200 elements. -/
example : let G : BitVec 32 := 2; let B : BitVec 32 := 128; let n : BitVec 32 := 200
    let a : Addr := 0x1000; let b : Addr := 0x2000; let c : Addr := 0x3000
    G.toNat * B.toNat ≤ 2 ^ 31 ∧ n.toNat ≤ G.toNat * B.toNat ∧ n.toNat < 2 ^ 31 ∧
    Fits a n.toNat ∧ Fits b n.toNat ∧ Fits c n.toNat ∧
    a.toNat % 4 = 0 ∧ b.toNat % 4 = 0 ∧ c.toNat % 4 = 0 ∧
    (c.toNat + 4 * n.toNat ≤ a.toNat ∨ a.toNat + 4 * n.toNat ≤ c.toNat) ∧
    (c.toNat + 4 * n.toNat ≤ b.toNat ∨ b.toNat + 4 * n.toNat ≤ c.toNat) := by
  simp only [Fits]; decide

end Ptx.Examples.VectorAdd
