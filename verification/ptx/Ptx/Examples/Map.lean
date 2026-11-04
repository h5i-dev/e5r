/-
M2: a map over an array of any length, on any 1-D launch.

`saxpy` (benchmarks/correct/saxpy.ptx, written directly in PTX) computes
`y[i] = a * x[i] + y[i] (mod 2^32)` for every `i < n` with a grid-stride loop:
thread `g = ctaid.x * ntid.x + tid.x` handles `g, g + S, g + 2S, …` where
`S = nctaid.x * ntid.x`. Index and stride are 64-bit, so nothing wraps.

Theorem `saxpy_correct`: for every grid size `G` and block size `B` (any
32-bit values; a thread exists only if both are positive), every `n` in the
`.u32` range, `x` and `y` that fit, are aligned and do not overlap, every
initial register content and every interleaving: no fault, every execution
terminates, no data race (each `y[i]` is read and written by exactly one
thread), and when all threads are done every `y[i]` holds `a * x[i] + y[i]`
of the initial memory and no other byte has changed. Unlike vadd, there is
no relation between `n` and the number of threads.
-/
import Ptx.Logic.Launch1D
import Ptx.Tactics.Eval
import Ptx.Kernels.Saxpy

namespace Ptx.Examples.Map
open Ptx

abbrev K := Ptx.Kernels.Saxpy.saxpy

def params (x y : Addr) (a n : BitVec 32) : String → Val := fun s =>
  if s = "saxpy_x" then x else if s = "saxpy_y" then y
  else if s = "saxpy_a" then ext32 a else if s = "saxpy_n" then ext32 n else 0

def launch (G B : BitVec 32) (x y : Addr) (a n : BitVec 32) : Launch :=
  { grid := ⟨G, 1, 1⟩, block := ⟨B, 1, 1⟩, params := params x y a n,
    alloc := [⟨x, 4 * n.toNat⟩, ⟨y, 4 * n.toNat⟩] }

theorem launch_oneD (G B : BitVec 32) (x y : Addr) (a n : BitVec 32) :
    (launch G B x y a n).OneD G B := ⟨rfl, rfl⟩

/-- The value the kernel must leave at `y[j]`. -/
def f (m₀ : Mem) (x y : Addr) (a : BitVec 32) (j : Nat) : BitVec 32 :=
  a * rd32 m₀ (elem x j) + rd32 m₀ (elem y j)

/-- Element `j` is one of thread `g`'s: `j = g + q * S`. -/
def Owns (S g j : Nat) : Prop := ∃ q, j = g + q * S

def R (S N : Nat) (x : Addr) (g : Nat) (b : Addr) : Prop :=
  ∃ q, g + q * S < N ∧ covers (elem x (g + q * S)) 4 b

def W (S N : Nat) (y : Addr) (g : Nat) (b : Addr) : Prop :=
  ∃ q, g + q * S < N ∧ covers (elem y (g + q * S)) 4 b

def Post (S N : Nat) (x y : Addr) (a : BitVec 32) (m₀ : Mem) (g : Nat) (M : Mem) : Prop :=
  ∀ q, g + q * S < N → rd32 M (elem y (g + q * S)) = f m₀ x y a (g + q * S)

/-- The loop head after `k` iterations. -/
def Inv (S N g : Nat) (x y : Addr) (a : BitVec 32) (m₀ : Mem) (v : Nat) (s : TState) (m : Mem) :
    Prop :=
  ∃ k, v = N - (g + k * S) ∧ g + k * S < 2 ^ 32 + S ∧ s.pc = 15 ∧
    s.r "%rd1" = x ∧ s.r "%rd2" = y ∧ s.r "%r1" = ext32 a ∧
    s.r "%rd3" = BitVec.ofNat 64 (g + k * S) ∧ s.r "%rd5" = BitVec.ofNat 64 S ∧
    s.r "%rd6" = BitVec.ofNat 64 N ∧
    (∀ q < k, g + q * S < N → rd32 m (elem y (g + q * S)) = f m₀ x y a (g + q * S)) ∧
    (∀ b, (∀ q < k, g + q * S < N → ¬ covers (elem y (g + q * S)) 4 b) → m b = m₀ b)

theorem stride_inj {S g₁ g₂ q₁ q₂ : Nat} (h₁ : g₁ < S) (h₂ : g₂ < S)
    (h : g₁ + q₁ * S = g₂ + q₂ * S) : g₁ = g₂ := by
  have e₁ : (g₁ + q₁ * S) % S = g₁ := by rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt h₁]
  have e₂ : (g₂ + q₂ * S) % S = g₂ := by rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt h₂]
  rw [← e₁, ← e₂, h]

theorem stride_inj' {S g q₁ q₂ : Nat} (hS : 0 < S) (h : g + q₁ * S = g + q₂ * S) : q₁ = q₂ :=
  Nat.eq_of_mul_eq_mul_right hS (by omega)

theorem shl2 {i : Nat} (h : i < 2 ^ 62) :
    BitVec.ofNat 64 i <<< min (lo32 (BitVec.ofInt 64 2)).toNat 64 = BitVec.ofNat 64 (4 * i) := by
  have : min (lo32 (BitVec.ofInt 64 2)).toNat 64 = 2 := by decide
  rw [this]; apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.mod_eq_of_lt (by omega : i < 2 ^ 64)]
  omega

theorem ule_ofNat {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    (BitVec.ofNat 64 a).ule (BitVec.ofNat 64 b) = decide (a ≤ b) := by
  simp [BitVec.ule, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]

section
variable {G B : BitVec 32} {x y : Addr} {a n : BitVec 32} {m₀ : Mem}

theorem step (S g : Nat) (hS : 0 < S) (hSl : S < 2 ^ 64 - 2 ^ 32)
    (fx : Fits x n.toNat) (fy : Fits y n.toNat) (ax : x.toNat % 4 = 0) (ay : y.toNat % 4 = 0)
    (sep : x.toNat + 4 * n.toNat ≤ y.toNat ∨ y.toNat + 4 * n.toNat ≤ x.toNat) (t : Tid) :
    ∀ v s m, Inv S n.toNat g x y a m₀ v s m →
      Safe K (launch G B x y a n).alloc ((launch G B x y a n).ctx t) (R S n.toNat x g)
        (W S n.toNat y g)
        (fun s m => (∃ v' < v, Inv S n.toNat g x y a m₀ v' s m) ∨
          (action K ((launch G B x y a n).ctx t) s = .done ∧ Post S n.toNat x y a m₀ g m ∧
            ∀ b, ¬ W S n.toNat y g b → m b = m₀ b)) s m := by
  intro v s m hI
  obtain ⟨k, hv, hik, hpc, h1, h2, h3, h4, h5, h6, ha, hb⟩ := hI
  obtain ⟨pc, r, p⟩ := s
  simp only at hpc h1 h2 h3 h4 h5 h6
  subst hpc
  have hN := n.isLt
  have hz : BitVec.ofInt 64 0 = 0#64 := by decide
  refine (wp_sound (f := 20) (cut := fun pc => pc == 15) ?_).weaken fun s m h => h.1
  generalize hi : g + k * S = i at *
  by_cases hin : n.toNat ≤ i
  · have hc : (BitVec.ofNat 64 n.toNat).ule (BitVec.ofNat 64 i) = true := by
      rw [ule_ofNat (by omega) (by omega)]; simp [hin]
    simp only [ptx_eval, K, Ptx.Kernels.Saxpy.saxpy, launch, params, h4, h6, hc,
      bne_iff_ne, ne_eq, Bool.true_eq_false, not_false_eq_true]
    refine .inr ⟨trivial, fun q hq => ?_, fun b hnot => hb b fun q hq hqn hc => hnot ⟨q, hqn, hc⟩⟩
    have : q < k := by
      rcases Nat.lt_or_ge q k with h | h
      · exact h
      · have : q * S ≥ k * S := Nat.mul_le_mul_right _ h
        omega
    exact ha q this hq
  · have hlt : i < n.toNat := by omega
    have hc : (BitVec.ofNat 64 n.toNat).ule (BitVec.ofNat 64 i) = false := by
      rw [ule_ofNat (by omega) (by omega)]; simp; omega
    have hk1 : g + (k + 1) * S = i + S := by rw [Nat.add_mul, Nat.one_mul]; omega
    have hadd : BitVec.ofNat 64 i + BitVec.ofNat 64 S = BitVec.ofNat 64 (g + (k + 1) * S) := by
      apply BitVec.eq_of_toNat_eq; simp [Nat.add_mul]; omega
    simp only [ptx_eval, K, Ptx.Kernels.Saxpy.saxpy, launch, params, h1, h2, h3, h4, h5, h6, hc,
      bne_self_eq_false, shl2 (by omega : i < 2 ^ 62), hz, BitVec.add_zero, elem_def, lo32_rd_b4,
      hadd]
    -- the bytes this iteration touches were not written before it
    have fresh : ∀ b, covers (elem y i) 4 b → ∀ q < k, g + q * S < n.toNat →
        ¬ covers (elem y (g + q * S)) 4 b := by
      intro b hb' q hq hqn hc'
      have hne : g + q * S ≠ i := by
        intro h; rw [← hi] at h; have := stride_inj' hS h; omega
      exact elem_disjoint fy hlt hqn (Ne.symm hne) hb' hc'
    have hxv : rd32 m (elem x i) = rd32 m₀ (elem x i) :=
      rd32_congr fun b hb' => hb b fun q _ hqn hc' => elem_disjoint₂ fx fy sep hlt hqn hb' hc'
    have hyv : rd32 m (elem y i) = rd32 m₀ (elem y i) :=
      rd32_congr fun b hb' => hb b (fresh b hb')
    refine ⟨?_, ⟨rfl, nofun, fun b hb' => .inr ⟨rfl, k, by omega, by rw [hi]; exact hb'⟩⟩, ?_,
      ⟨rfl, nofun, fun b hb' => .inl ⟨k, by omega, by rw [hi]; exact hb'⟩⟩, ?_,
      ⟨rfl, nofun, fun b hb' => .inl ⟨k, by omega, by rw [hi]; exact hb'⟩⟩,
      .inl ⟨n.toNat - (g + (k + 1) * S), by omega, k + 1, rfl, by omega, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
    · simp [accessOk, aligned_elem fx hlt ax, holds_elem fx hlt]
    · simp [accessOk, aligned_elem fy hlt ay, holds_elem fy hlt]
    · simp [accessOk, aligned_elem fy hlt ay, holds_elem fy hlt]
    all_goals try (simp only [upd, String.reduceEq, ↓reduceIte, h1, h2, h3, h5, h6]; done)
    · intro q hq hqn
      rcases Nat.lt_or_ge q k with hqk | hqk
      · rw [rd32_wr_disjoint (fun b hb' hc' => fresh b hc' q hqk hqn hb')]
        exact ha q hqk hqn
      · have : q = k := by omega
        subst this; rw [hi, rd32_wr_same]
        simp [f, lo32, ext32, ← hxv, ← hyv]
    · intro b hnot
      have hout : ¬ covers (elem y i) 4 b := by
        have := hnot k (by omega); rw [hi] at this; exact this hlt
      rw [wr_outside hout]
      exact hb b fun q hq hqn => hnot q (by omega) hqn

theorem entry {t : Tid} (ht : t ∈ (launch G B x y a n).threads) (r : String → Val) (p : String → Bool) :
    Safe K (launch G B x y a n).alloc ((launch G B x y a n).ctx t)
      (R (G.toNat * B.toNat) n.toNat x (gid B t)) (W (G.toNat * B.toNat) n.toNat y (gid B t))
      (fun s m => ∃ v, Inv (G.toNat * B.toNat) n.toNat (gid B t) x y a m₀ v s m) ⟨0, r, p⟩ m₀ := by
  have h1 := launch_oneD G B x y a n
  obtain ⟨hcx, htx, -⟩ := h1.thread ht
  have hl := h1.gid_lt ht
  refine (wp_sound (f := 20) (cut := fun pc => pc == 15) ?_).weaken fun s m h => h.1
  simp only [ptx_eval, K, Ptx.Kernels.Saxpy.saxpy, launch, params]
  have hG := G.isLt; have hB := B.isLt; have hc := t.ctaid.x.isLt
  have e1 : ext32 t.ctaid.x * ext32 B + ext32 t.tid.x = BitVec.ofNat 64 (gid B t) := by
    apply BitVec.eq_of_toNat_eq
    have : t.ctaid.x.toNat * B.toNat < 2 ^ 64 := by
      have := Nat.mul_le_mul (by omega : t.ctaid.x.toNat ≤ 2 ^ 32 - 1) (by omega : B.toNat ≤ 2 ^ 32 - 1)
      omega
    simp [ext32, gid, BitVec.toNat_mul, BitVec.toNat_add, Nat.mod_eq_of_lt this]
  have e2 : ext32 G * ext32 B = BitVec.ofNat 64 (G.toNat * B.toNat) := by
    apply BitVec.eq_of_toNat_eq
    simp [ext32, BitVec.toNat_mul]
  have e3 : ext32 n = BitVec.ofNat 64 n.toNat := by
    apply BitVec.eq_of_toNat_eq; simp [ext32]
  simp only [e1, e2, e3]
  refine ⟨n.toNat - gid B t, 0, by simp, by simp; omega, rfl, ?_, ?_, ?_, ?_, ?_, ?_,
    fun q hq => absurd hq (Nat.not_lt_zero _), fun b _ => rfl⟩
  all_goals simp only [upd, String.reduceEq, ↓reduceIte, Nat.zero_mul, Nat.add_zero]

theorem S_bounds (G B : BitVec 32) : G.toNat * B.toNat < 2 ^ 64 - 2 ^ 32 := by
  have hG := G.isLt; have hB := B.isLt
  have : G.toNat * B.toNat ≤ (2 ^ 32 - 1) * (2 ^ 32 - 1) := Nat.mul_le_mul (by omega) (by omega)
  omega

theorem thread {t : Tid} (ht : t ∈ (launch G B x y a n).threads) (r : String → Val) (p : String → Bool)
    (fx : Fits x n.toNat) (fy : Fits y n.toNat) (ax : x.toNat % 4 = 0) (ay : y.toNat % 4 = 0)
    (sep : x.toNat + 4 * n.toNat ≤ y.toNat ∨ y.toNat + 4 * n.toNat ≤ x.toNat) :
    Safe K (launch G B x y a n).alloc ((launch G B x y a n).ctx t)
      (R (G.toNat * B.toNat) n.toNat x (gid B t)) (W (G.toNat * B.toNat) n.toNat y (gid B t))
      (fun s m => action K ((launch G B x y a n).ctx t) s = .done ∧
        Post (G.toNat * B.toNat) n.toNat x y a m₀ (gid B t) m) ⟨0, r, p⟩ m₀ := by
  have hl := (launch_oneD G B x y a n).gid_lt ht
  refine (entry (m₀ := m₀) ht r p).mono fun s m ⟨v, hI⟩ => ?_
  exact (Safe.loop (step _ _ (by omega) (S_bounds G B) fx fy ax ay sep t) v s m hI).weaken
    fun s m h => ⟨h.1, h.2.1⟩

end

theorem saxpy_correct (G B a n : BitVec 32) (x y : Addr) (m₀ : Mem) (s₀ : Dim3 → Mem)
    (r₀ : Tid → String → Val) (p₀ : Tid → String → Bool)
    (fx : Fits x n.toNat) (fy : Fits y n.toNat) (ax : x.toNat % 4 = 0) (ay : y.toNat % 4 = 0)
    (sep : x.toNat + 4 * n.toNat ≤ y.toNat ∨ y.toNat + 4 * n.toNat ≤ x.toNat) :
    let L := launch G B x y a n
    let c₀ := Cfg.init r₀ p₀ m₀ s₀
    (∀ cfg, Reach K L c₀ cfg → ¬ Faults K L cfg) ∧
    (∀ cfg, Reach K L c₀ cfg → Done K L cfg ∨ ∃ cfg', Step K L cfg cfg') ∧
    (∃ bound, ∀ j cfg, Steps K L j c₀ cfg → j ≤ bound) ∧
    RaceFree K L c₀ ∧
    (∃ cfg, Reach K L c₀ cfg ∧ Done K L cfg) ∧
    (∀ cfg, Reach K L c₀ cfg → Done K L cfg → 0 < G.toNat * B.toNat →
      (∀ i < n.toNat, rd32 cfg.mem (elem y i) = a * rd32 m₀ (elem x i) + rd32 m₀ (elem y i)) ∧
      (∀ b, (∀ i < n.toNat, ¬ covers (elem y i) 4 b) → cfg.mem b = m₀ b)) := by
  intro L c₀
  have h1 := launch_oneD G B x y a n
  let S := G.toNat * B.toNat
  have hsolo : ∀ t ∈ L.threads, ∃ k, Solo K L.alloc (L.ctx t) (R S n.toNat x (gid B t))
      (W S n.toNat y (gid B t)) (s0 r₀ p₀ m₀ t) m₀ k ∧
      Post S n.toNat x y a m₀ (gid B t) (trace K L.alloc (L.ctx t) k (s0 r₀ p₀ m₀ t) m₀).2 :=
    fun t ht => (thread ht (r₀ t) (p₀ t) fx fy ax ay sep).solo
  have hdisj : ∀ t ∈ L.threads, ∀ u ∈ L.threads, t ≠ u → ∀ b,
      W S n.toNat y (gid B t) b → ¬ R S n.toNat x (gid B u) b ∧ ¬ W S n.toNat y (gid B u) b := by
    intro t ht u hu htu b ⟨q, hq, hc⟩
    refine ⟨fun ⟨q', hq', hc'⟩ => elem_disjoint₂ fy fx (by omega) hq hq' hc hc', fun ⟨q', hq', hc'⟩ => ?_⟩
    have hne : gid B t + q * S ≠ gid B u + q' * S := fun h =>
      htu (h1.gid_inj ht hu (stride_inj (h1.gid_lt ht) (h1.gid_lt hu) h))
    exact elem_disjoint fy hq hq' hne hc hc'
  obtain ⟨bound, g⟩ := grid_sound (R := fun t => R S n.toNat x (gid B t))
    (W := fun t => W S n.toNat y (gid B t)) (P := fun t => Post S n.toNat x y a m₀ (gid B t)) hsolo hdisj s₀
  refine ⟨g.noFault, g.progress, ⟨bound, g.bounded⟩, g.raceFree, g.exists_done, ?_⟩
  intro cfg hr hd hS
  obtain ⟨hown, hrest⟩ := g.final cfg hr hd
  refine ⟨fun i hi => ?_, fun b hb => hrest b fun t _ ⟨q, hq, hc⟩ => hb _ hq hc⟩
  have hgi : i % S < S := Nat.mod_lt _ hS
  obtain ⟨hm, hg⟩ := h1.owner_mem (i := i % S) hgi
  obtain ⟨M, hP, hM⟩ := hown _ hm
  have hdec : i % S + i / S * S = i := by rw [Nat.mul_comm]; exact Nat.mod_add_div i S
  have := hP (i / S) (by rw [hg, hdec]; exact hi)
  rw [hg, hdec] at this
  rw [← show rd32 M (elem y i) = rd32 cfg.mem (elem y i) from rd32_congr fun b hb =>
    (hM b ⟨i / S, by rw [hg, hdec]; exact hi, by rw [hg, hdec]; exact hb⟩).symm, this]
  rfl

end Ptx.Examples.Map
