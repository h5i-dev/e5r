/- e5r-proof ptx=98e5d7357ce97b779e2ed7267c36d14b67db5d9bb1dcac5c52e44232c38449d6 spec=8f9da26877a81ec6873eb5d85d5cfc2c8848f380fa023b148eeda702bff5de9d toolchain=leanprover/lean4:v4.35.0 -/
/-
A supplied proof (docs/verification/ptx.md, "Supplied proofs") for
`m5/m4/kernels/s_pingpong.ptx`, a Hillis-Steele scan with two shared
buffers and one barrier per round:

```c
buf[0][t] = i < n ? x[i] : 0;                      // phase 0
for (d = 1; d < blockDim.x; d <<= 1) {             // phase k + 1 is round k
  v = buf[src][t]; if (t >= d) v += buf[src][t - d];
  buf[1 - src][t] = v; src = 1 - src; __syncthreads();
}
if (i < n) y[i] = buf[src][t];                     // phase R + 1
```

`scan32`'s automation expects three barriers (read, then add, in place), so
the kernel is `unsupported` there; the class statement `Scan32.Correct` is
the same. Round `k` reads buffer `k % 2` and writes buffer `(k+1) % 2`, so
the window values `Scan32.V` of the library hold: after round `k`, buffer
`(k+1) % 2` holds `V (k+1)` and buffer `k % 2` still holds `V k`.
-/
import E5rSpec

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace E5rProof
open Ptx Ptx.Auto Ptx.Auto.Block Ptx.Auto.Scan32 E5rSpec
open Ptx.Auto.Reduce32 (accUpTo_congr)

abbrev K := E5rSpec.«s_pingpong»

section
variable (A : Block.Args spec)

def gid (t : Tid) : Nat := t.ctaid.x.toNat * A.B.toNat + t.tid.x.toNat

/-- Buffer `s` (0 or 1), 1024 words each. -/
abbrev bf (s : Nat) : Addr := elem A.sb (1024 * s)

/-- What thread `t` touches in phase `p`. -/
def foot (t : Tid) (p : Nat) : Foot :=
  if p = 0 then
    { r := fun l => l.1 = .global ∧ gid A t < A.n.toNat ∧ covers (elem A.x (gid A t)) 4 l.2
      w := fun l => l.1 = .shared ∧ covers (elem A.sb t.tid.x.toNat) 4 l.2 }
  else if p = A.j + 1 then
    { r := fun l => l.1 = .shared ∧ gid A t < A.n.toNat ∧
        covers (elem A.sb (1024 * (A.j % 2) + t.tid.x.toNat)) 4 l.2
      w := fun l => l.1 = .global ∧ gid A t < A.n.toNat ∧ covers (elem A.out (gid A t)) 4 l.2 }
  else
    { r := fun l => l.1 = .shared ∧ (covers (elem A.sb (1024 * ((p - 1) % 2) + t.tid.x.toNat)) 4 l.2 ∨
        (2 ^ (p - 1) ≤ t.tid.x.toNat ∧
          covers (elem A.sb (1024 * ((p - 1) % 2) + (t.tid.x.toNat - 2 ^ (p - 1)))) 4 l.2))
      w := fun l => l.1 = .shared ∧ covers (elem A.sb (1024 * (p % 2) + t.tid.x.toNat)) 4 l.2 }

/-- The shared memory of a CTA after round `r - 1` (after the load for `r = 0`). -/
def sm (m₀ : Mem) (b : Nat) (sh : Mem) (r : Nat) : Mem :=
  if r = 0 then cells A.sb A.B.toNat (V A m₀ b 0) sh
  else cells (bf A (r % 2)) A.B.toNat (V A m₀ b r) (cells (bf A ((r + 1) % 2)) A.B.toNat (V A m₀ b (r - 1)) sh)

def mem (m₀ : Mem) (sh₀ : Dim3 → Mem) (b : Dim3) : Nat → Heap
  | 0 => ⟨m₀, sh₀ b⟩
  | p + 1 => ⟨if p = A.j + 1 then outs A m₀ b.x.toNat else m₀, sm A m₀ b.x.toNat (sh₀ b) (min p A.j)⟩

/-- Registers shared by every phase entry. -/
def regs (t : Tid) (s : TState) : Prop :=
  s.r "%r1" = ext32 A.B ∧ s.r "%r2" = ext32 t.tid.x ∧
  s.r "%r3" = ext32 (BitVec.ofNat 32 (gid A t)) ∧
  s.r "%r18" = ext32 (BitVec.ofNat 32 (4 * t.tid.x.toNat)) ∧
  s.r "%r19" = ext32 (BitVec.ofNat 32 A.sb.toNat) ∧ s.r "%rd2" = A.out ∧
  s.p "%p1" = decide (A.n.toNat ≤ gid A t)

def T (t : Tid) : Nat → TState → Prop
  | 0, s => s.pc = 0
  | 1, s => s.pc = 20 ∧ s.r "%r51" = ext32 0 ∧ regs A t s
  | k + 2, s => s.pc = 42 ∧ s.r "%r48" = ext32 (BitVec.ofNat 32 (2 ^ k)) ∧
      s.r "%r51" = ext32 (BitVec.ofNat 32 ((k + 1) % 2)) ∧ regs A t s

def phased (m₀ : Mem) (sh₀ : Dim3 → Mem) : Phased where
  P := fun _ => A.j + 2
  F := foot A
  T := T A
  N := fun _ _ => 60
  M := mem A m₀ sh₀
  bpc := fun _ p => if p = 0 then 19 else 41
  Cell := fun _ => False
  Δ := fun _ _ _ => 0

theorem fits_sb (hpre : Pre K A) :
    A.sb.toNat % 4 = 0 ∧ Fits A.sb 2048 ∧ A.B.toNat ≤ 1024 ∧ A.sb.toNat + 8192 ≤ 2 ^ 32 := by
  have := A.sb_facts (K := K) (W := 2048) ⟨4, by simp [K, E5rSpec.«s_pingpong»], by decide, by decide,
    by simp [spec]⟩ hpre.2.2.2.2.2.2.2.2.2.2.2
  have hB := hpre.2.1
  simp only [spec_maxJ] at hB
  refine ⟨this.1, ?_, by omega, by omega⟩
  unfold Fits; omega

theorem fits_bf (hpre : Pre K A) (s : Nat) (hs : s < 2) : Fits (bf A s) A.B.toNat := by
  obtain ⟨-, f, hB, -⟩ := fits_sb A hpre
  exact fits_tail f (by omega)

theorem sb_alloc : ⟨A.sb, 4 * 2048⟩ ∈ (A.launch A.n.toNat).allocs K .shared :=
  A.sb_alloc (K := K) (al := 4) (by simp [K, E5rSpec.«s_pingpong», spec])

theorem lo32_ofInt_zero : lo32 (BitVec.ofInt 64 0) = 0 := by decide

set_option maxHeartbeats 4000000 in
theorem phase_load (hpre : Pre K A) (m₀ : Mem) (sh₀ : Dim3 → Mem) {t : Tid}
    (ht : t ∈ (A.launch A.n.toNat).threads) (s : TState) (hs : T A t 0 s) :
    Run K ((A.launch A.n.toNat).allocs K) ((A.launch A.n.toNat).ctx t) (foot A t 0) (fun _ => False) add32
      ((phased A m₀ sh₀).J K (A.launch A.n.toNat) t 0) 60 s (mem A m₀ sh₀ t.ctaid 0) (fun _ => 0) := by
  obtain ⟨pc, r, p⟩ := s
  simp only [T] at hs; subst hs
  obtain ⟨hc, hi, hcB, hGB, -, -, -, -⟩ := A.thread_facts hpre.2.2.2.2.1 ht
  obtain ⟨sal, fsb, hBW, sbb⟩ := fits_sb A hpre
  have fsbB : Fits A.sb A.B.toNat := by unfold Fits at fsb ⊢; omega
  have fx := hpre.2.2.2.2.2.2.1
  have xal := hpre.2.2.2.2.2.2.2.1
  have hcB' : t.ctaid.x.toNat * A.B.toNat < 2 ^ 32 := by omega
  have hg := A.gid_toNat hcB hGB
  refine (wpR_sound (cut := fun _ => false) ?_).weaken fun s h d hq => hq.1
  simp only [ptx_eval, K, E5rSpec.«s_pingpong», Block.Args.launch, Block.Args.params, spec_input,
    spec_output, spec_length, mem, Phased.J, phased, foot, gid, ↓reduceIte, List.map_cons, List.map_nil]
  try simp only [show A.sh "_ZZ10s_pingpongE3buf" = A.sb from rfl]
  ptx_branches4
  all_goals ptx_addrs4 [A.sb, A.x] [t.tid.x.toNat, t.ctaid.x.toNat * A.B.toNat + t.tid.x.toNat]
  all_goals (try and_intros)
  all_goals first
    | trivial
    | (exfalso; omega)
    | exact accessOk_elem_mem (N := 2048) (by simp) fsb sal (by omega)
    | exact accessOk_elem_mem (N := A.n.toNat) (by simp) fx xal (by omega)
    | exact fun y hy => ⟨rfl, hy⟩
    | exact fun y hy => ⟨trivial, hy⟩
    | exact fun y hy => .inl ⟨rfl, by omega, hy⟩
    | exact fun y hy => .inl ⟨trivial, by omega, hy⟩
    | (rintro ⟨sp, y⟩ ⟨hsp, hy⟩
       try simp only at hsp
       subst hsp
       refine wr_cells fsbB hi hy ?_
       simp only [Scan32.V, Block.Args.seg, lo32_ext32, lo32_rd_b4, lo32_ofInt_zero]
       split <;> first | rfl | (exfalso; omega))
    | (simp (config := { failIfUnchanged := false }) only [T, regs, gid, upd, String.reduceEq,
         ↓reduceIte, true_and, and_true]
       all_goals (try and_intros)
       all_goals first
         | ptx_reg4
         | (rw [Ptx.Auto.ule_toNat, hg]; try exact rfl))
  done

theorem foot_round (t : Tid) {k : Nat} (hk : k < A.j) : foot A t (k + 1) =
    { r := fun l => l.1 = .shared ∧ (covers (elem A.sb (1024 * (k % 2) + t.tid.x.toNat)) 4 l.2 ∨
        (2 ^ k ≤ t.tid.x.toNat ∧ covers (elem A.sb (1024 * (k % 2) + (t.tid.x.toNat - 2 ^ k))) 4 l.2))
      w := fun l => l.1 = .shared ∧ covers (elem A.sb (1024 * ((k + 1) % 2) + t.tid.x.toNat)) 4 l.2 } := by
  simp only [foot, show k + 1 ≠ 0 by omega, show k + 1 ≠ A.j + 1 by omega, ↓reduceIte,
    Nat.add_sub_cancel]

theorem foot_store (t : Tid) : foot A t (A.j + 1) =
    { r := fun l => l.1 = .shared ∧ gid A t < A.n.toNat ∧
        covers (elem A.sb (1024 * (A.j % 2) + t.tid.x.toNat)) 4 l.2
      w := fun l => l.1 = .global ∧ gid A t < A.n.toNat ∧ covers (elem A.out (gid A t)) 4 l.2 } := by
  simp only [foot, show A.j + 1 ≠ 0 by omega, ↓reduceIte]

theorem foot_load (t : Tid) : foot A t 0 =
    { r := fun l => l.1 = .global ∧ gid A t < A.n.toNat ∧ covers (elem A.x (gid A t)) 4 l.2
      w := fun l => l.1 = .shared ∧ covers (elem A.sb t.tid.x.toNat) 4 l.2 } := rfl

/-- The entry state of phase `k + 1`: after the load (`k = 0`) or after
round `k - 1`. -/
theorem T_succ {t : Tid} {k pc : Nat} {r : String → Val} {p : String → Bool}
    (hs : T A t (k + 1) ⟨pc, r, p⟩) : regs A t ⟨pc, r, p⟩ ∧
    ((k = 0 ∧ pc = 20 ∧ r "%r51" = ext32 0) ∨
     (1 ≤ k ∧ pc = 42 ∧ r "%r48" = ext32 (BitVec.ofNat 32 (2 ^ (k - 1))) ∧
       r "%r51" = ext32 (BitVec.ofNat 32 (k % 2)))) := by
  rcases k with _ | k
  · simp only [T] at hs; exact ⟨hs.2.2, .inl ⟨rfl, hs.1, hs.2.1⟩⟩
  · simp only [T] at hs
    exact ⟨hs.2.2.2, .inr ⟨by omega, hs.1, by simpa using hs.2.1, hs.2.2.1⟩⟩

set_option maxHeartbeats 8000000 in
theorem phase_round (hpre : Pre K A) (m₀ : Mem) (sh₀ : Dim3 → Mem) {t : Tid}
    (ht : t ∈ (A.launch A.n.toNat).threads) {k : Nat} (hk : k < A.j) (s : TState)
    (hs : T A t (k + 1) s) :
    Run K ((A.launch A.n.toNat).allocs K) ((A.launch A.n.toNat).ctx t) (foot A t (k + 1))
      (fun _ => False) add32 ((phased A m₀ sh₀).J K (A.launch A.n.toNat) t (k + 1)) 60 s
      (mem A m₀ sh₀ t.ctaid (k + 1)) (fun _ => 0) := by
  obtain ⟨hc, hi, hcB, hGB, -, -, -, -⟩ := A.thread_facts hpre.2.2.2.2.1 ht
  obtain ⟨sal, fsb, hBW, sbb⟩ := fits_sb A hpre
  have fsbB : Fits A.sb A.B.toNat := by unfold Fits at fsb ⊢; omega
  have hpw := pow_lt A hpre hk
  have hB2 : 2 ≤ A.B.toNat := by
    have := pow_lt A hpre (i := 0) (by omega); simp at this; omega
  have hmin : min k A.j = k := by omega
  have hmin1 : min (k + 1) A.j = k + 1 := by omega
  have hnext : k + 1 < A.j → 2 ^ (k + 1) < A.B.toNat := fun h => pow_lt A hpre h
  have hlast : k + 1 = A.j → A.B.toNat ≤ 2 ^ (k + 1) := fun h => by rw [h]; exact hpre.2.2.1
  have hp2 : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [Nat.pow_succ]; omega
  have hpw1 : 1 ≤ k → 2 ^ (k - 1) * 2 = 2 ^ k := fun h => by
    rw [← Nat.pow_succ]; congr 1; omega
  have fb := fits_bf A hpre ((k + 1) % 2) (by omega)
  have fa := fits_bf A hpre (k % 2) (by omega)
  obtain ⟨pc, r, p⟩ := s
  obtain ⟨⟨hr1, hr2, hr3, hr18, hr19, hrd2, hp1⟩, ⟨hk0, rfl, hr51⟩ | ⟨hk1, rfl, hr48, hr51⟩⟩ :=
    T_succ A hs
  all_goals simp only at hr1 hr2 hr3 hr18 hr19 hrd2 hp1
  · subst hk0
    rw [foot_round A t hk]
    refine (wpR_sound (cut := fun _ => false) ?_).weaken fun s h d hq => hq.1
    simp only [ptx_eval, K, E5rSpec.«s_pingpong», Block.Args.launch, Block.Args.params, spec_input,
      spec_output, spec_length, mem, Phased.J, phased, foot_round A t hk, hmin, hmin1, sm, gid,
      hr1, hr2, hr3, hr18, hr19, hrd2, hr51, ↓reduceIte, List.map_cons, List.map_nil,
      show (0 : Nat) ≠ A.j + 1 by omega, Nat.zero_mod, Nat.mul_zero, Nat.zero_add, Nat.pow_zero,
      Nat.reduceMod, Nat.reduceMul, Nat.reduceAdd, Nat.mul_one]
    try simp only [show A.sh "_ZZ10s_pingpongE3buf" = A.sb from rfl]
    ptx_branches4
    all_goals ptx_addrs4 [A.sb] [t.tid.x.toNat, t.tid.x.toNat - 1, 1024 + t.tid.x.toNat]
    all_goals (try and_intros)
    all_goals first
      | exact trivial
      | (exfalso; omega)
      | (intro y hy; exact hy)
      | exact fun y hy => ⟨trivial, hy⟩
      | exact fun y hy => ⟨rfl, hy⟩
      | exact accessOk_elem_mem (N := 2048) (List.mem_singleton.2 rfl) fsb sal (by omega)
      | exact fun y hy => ⟨trivial, .inl hy⟩
      | exact fun y hy => ⟨rfl, .inl hy⟩
      | exact fun y hy => ⟨trivial, .inr ⟨by omega, hy⟩⟩
      | exact fun y hy => ⟨rfl, .inr ⟨by omega, hy⟩⟩
      | exact fun y hy => .inl ⟨trivial, .inl hy⟩
      | exact fun y hy => .inl ⟨rfl, .inl hy⟩
      | exact fun y hy => .inl ⟨trivial, .inr ⟨by omega, hy⟩⟩
      | exact fun y hy => .inl ⟨rfl, .inr ⟨by omega, hy⟩⟩
      | exact fun y hy => .inr ⟨trivial, hy⟩
      | exact fun y hy => .inr ⟨rfl, hy⟩
      | (rintro ⟨sp, y⟩ ⟨hsp, hy⟩
         try simp only at hsp
         subst hsp
         rw [show 1024 + t.tid.x.toNat = 1024 * 1 + t.tid.x.toNat by rfl, ← elem_elem] at hy ⊢
         refine wr_cells (fits_bf A hpre 1 (by omega)) hi hy ?_
         simp only [lo32_ext32, lo32_rd_b4]
         first
           | (rw [rd32_cells fsbB hi, rd32_cells fsbB (by omega)]
              simp only [Scan32.V, show 2 ^ 0 ≤ t.tid.x.toNat by omega, ↓reduceIte, Nat.pow_zero]
              exact BitVec.add_comm _ _)
           | (rw [rd32_cells fsbB hi]
              simp only [Scan32.V, show ¬ 2 ^ 0 ≤ t.tid.x.toNat by omega, ↓reduceIte, Nat.pow_zero]))
      | (simp (config := { failIfUnchanged := false }) only [T, regs, gid, upd, String.reduceEq,
           ↓reduceIte, true_and, and_true]
         all_goals (try and_intros)
         all_goals first | ptx_reg4 | assumption)
    done
  · rw [foot_round A t hk]
    refine (wpR_sound (cut := fun _ => false) ?_).weaken fun s h d hq => hq.1
    simp only [ptx_eval, K, E5rSpec.«s_pingpong», Block.Args.launch, Block.Args.params, spec_input,
      spec_output, spec_length, mem, Phased.J, phased, foot_round A t hk, hmin, hmin1, sm, gid,
      hr1, hr2, hr3, hr18, hr19, hrd2, hr48, hr51, ↓reduceIte, List.map_cons, List.map_nil,
      show k ≠ 0 by omega, show k + 1 ≠ 0 by omega, show k ≠ A.j + 1 by omega, Nat.add_sub_cancel]
    try simp only [show A.sh "_ZZ10s_pingpongE3buf" = A.sb from rfl]
    ptx_branches4
    all_goals ptx_addrs4 [A.sb] [1024 * (k % 2) + t.tid.x.toNat, 1024 * (k % 2) + (t.tid.x.toNat - 2 ^ k),
      1024 * ((k + 1) % 2) + t.tid.x.toNat]
    all_goals (try and_intros)
    all_goals first
      | exact trivial
      | (exfalso; omega)
      | (intro y hy; exact hy)
      | exact fun y hy => ⟨trivial, hy⟩
      | exact fun y hy => ⟨rfl, hy⟩
      | exact accessOk_elem_mem (N := 2048) (List.mem_singleton.2 rfl) fsb sal (by omega)
      | exact fun y hy => ⟨trivial, .inl hy⟩
      | exact fun y hy => ⟨rfl, .inl hy⟩
      | exact fun y hy => ⟨trivial, .inr ⟨by omega, hy⟩⟩
      | exact fun y hy => ⟨rfl, .inr ⟨by omega, hy⟩⟩
      | exact fun y hy => .inl ⟨trivial, .inl hy⟩
      | exact fun y hy => .inl ⟨rfl, .inl hy⟩
      | exact fun y hy => .inl ⟨trivial, .inr ⟨by omega, hy⟩⟩
      | exact fun y hy => .inl ⟨rfl, .inr ⟨by omega, hy⟩⟩
      | exact fun y hy => .inr ⟨trivial, hy⟩
      | exact fun y hy => .inr ⟨rfl, hy⟩
      | (rintro ⟨sp, y⟩ ⟨hsp, hy⟩
         try simp only at hsp
         subst hsp
         rw [← elem_elem] at hy ⊢
         refine wr_cells fb hi hy ?_
         simp only [lo32_ext32, lo32_rd_b4]
         first
           | (rw [← elem_elem, ← elem_elem, rd32_cells fa hi, rd32_cells fa (by omega)]
              simp only [Scan32.V, show 2 ^ k ≤ t.tid.x.toNat by omega, ↓reduceIte]
              exact BitVec.add_comm _ _)
           | (rw [← elem_elem, rd32_cells fa hi]
              simp only [Scan32.V, show ¬ 2 ^ k ≤ t.tid.x.toNat by omega, ↓reduceIte]))
      | (simp (config := { failIfUnchanged := false }) only [T, regs, gid, upd, String.reduceEq,
           ↓reduceIte, true_and, and_true]
         all_goals (try and_intros)
         all_goals first | ptx_reg4 | assumption)
    done

/-- After round `r - 1`, buffer `r % 2` holds `V r`. -/
theorem rd_sm (hpre : Pre K A) (m₀ : Mem) (b : Nat) (sh : Mem) (r : Nat) {i : Nat}
    (hi : i < A.B.toNat) :
    rd32 (sm A m₀ b sh r) (elem A.sb (1024 * (r % 2) + i)) = V A m₀ b r i := by
  obtain ⟨-, fsb, hBW, -⟩ := fits_sb A hpre
  unfold sm
  split
  · next h =>
    subst h
    have fsbB : Fits A.sb A.B.toNat := by unfold Fits at fsb ⊢; omega
    simp only [Nat.zero_mod, Nat.mul_zero, Nat.zero_add]
    rw [rd32_cells fsbB hi]
  · rw [← elem_elem, rd32_cells (fits_bf A hpre (r % 2) (by omega)) hi]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem phase_store (hpre : Pre K A) (m₀ : Mem) (sh₀ : Dim3 → Mem) {t : Tid}
    (ht : t ∈ (A.launch A.n.toNat).threads) (s : TState) (hs : T A t (A.j + 1) s) :
    Run K ((A.launch A.n.toNat).allocs K) ((A.launch A.n.toNat).ctx t) (foot A t (A.j + 1))
      (fun _ => False) add32 ((phased A m₀ sh₀).J K (A.launch A.n.toNat) t (A.j + 1)) 60 s
      (mem A m₀ sh₀ t.ctaid (A.j + 1)) (fun _ => 0) := by
  obtain ⟨hc, hi, hcB, hGB, -, -, -, -⟩ := A.thread_facts hpre.2.2.2.2.1 ht
  obtain ⟨sal, fsb, hBW, sbb⟩ := fits_sb A hpre
  have fout := hpre.2.2.2.2.2.2.2.2.1
  have oal := hpre.2.2.2.2.2.2.2.2.2.1
  have hBR := hpre.2.2.1
  have hR0 : A.j = 0 → A.B.toNat = 1 := fun h => by
    rw [h] at hBR; have := hpre.1; simp at hBR; omega
  have hpw1 : 1 ≤ A.j → 2 ^ (A.j - 1) * 2 = 2 ^ A.j := fun h => by
    rw [← Nat.pow_succ]; congr 1; omega
  have h2 : 1 ≤ A.j → 2 ^ (A.j - 1) < A.B.toNat := fun h => by
    rcases hpre.2.2.2.1 with h' | h' <;> omega
  have hcB' : t.ctaid.x.toNat * A.B.toNat < 2 ^ 32 := by omega
  have hg := A.gid_toNat hcB hGB
  have hrd := rd_sm A hpre m₀ t.ctaid.x.toNat (sh₀ t.ctaid) A.j hi
  have hgid : gid A t = t.ctaid.x.toNat * A.B.toNat + t.tid.x.toNat := rfl
  obtain ⟨pc, r, p⟩ := s
  obtain ⟨⟨hr1, hr2, hr3, hr18, hr19, hrd2, hp1⟩, ⟨hj0, rfl, hr51⟩ | ⟨hj1, rfl, hr48, hr51⟩⟩ :=
    T_succ A hs
  all_goals simp only at hr1 hr2 hr3 hr18 hr19 hrd2 hp1
  all_goals rw [foot_store A t]
  all_goals refine (wpR_sound (cut := fun _ => false) ?_).weaken fun s h d hq => hq.1
  -- decide the store guard up front
  all_goals rcases Nat.lt_or_ge (gid A t) A.n.toNat with hgn | hgn
  all_goals first
    | rw [show decide (A.n.toNat ≤ gid A t) = false from decide_eq_false (by omega)] at hp1
    | rw [show decide (A.n.toNat ≤ gid A t) = true from decide_eq_true (by omega)] at hp1
  · have hB1 := hR0 hj0
    simp only [ptx_eval, K, E5rSpec.«s_pingpong», Block.Args.launch, Block.Args.params, spec_input,
      spec_output, spec_length, mem, Phased.J, phased, foot_store A t, gid, Nat.min_self,
      hr1, hr2, hr3, hr18, hr19, hrd2, hp1, hr51, ↓reduceIte, List.map_cons, List.map_nil,
      show ¬ (A.j + 1 + 1 < A.j + 2) by omega]
    try simp only [show A.sh "_ZZ10s_pingpongE3buf" = A.sb from rfl]
    ptx_branches4
    all_goals ptx_addrs4 [A.sb, A.out] [1024 * (A.j % 2) + t.tid.x.toNat,
      t.ctaid.x.toNat * A.B.toNat + t.tid.x.toNat]
    all_goals (try and_intros)
    all_goals first
      | exact trivial
      | (exfalso; omega)
      | exact accessOk_elem_mem (N := 2048) (List.mem_singleton.2 rfl) fsb sal (by omega)
      | exact accessOk_elem_mem (N := A.n.toNat) (by simp) fout oal (by omega)
      | exact fun y hy => .inl ⟨trivial, by omega, hy⟩
      | exact fun y hy => .inl ⟨rfl, by omega, hy⟩
      | exact fun y hy => ⟨trivial, by omega, hy⟩
      | exact fun y hy => ⟨rfl, by omega, hy⟩
      | (rintro ⟨sp, y⟩ ⟨-, hlt, -⟩; exfalso; omega)
      | (rintro ⟨sp, y⟩ ⟨hsp, hlt, hy⟩
         try simp only at hsp
         subst hsp
         show _ = cells _ _ _ m₀ y
         rw [← elem_elem] at hy ⊢
         refine wr_cells (fits_tail fout (c := t.ctaid.x.toNat * A.B.toNat) (M := _) (by omega))
           (by omega) hy ?_
         simp only [lo32_ext32, lo32_rd_b4]
         exact hrd)
    done
  · have hB1 := hR0 hj0
    simp only [ptx_eval, K, E5rSpec.«s_pingpong», Block.Args.launch, Block.Args.params, spec_input,
      spec_output, spec_length, mem, Phased.J, phased, foot_store A t, gid, Nat.min_self,
      hr1, hr2, hr3, hr18, hr19, hrd2, hp1, hr51, ↓reduceIte, List.map_cons, List.map_nil,
      show ¬ (A.j + 1 + 1 < A.j + 2) by omega]
    try simp only [show A.sh "_ZZ10s_pingpongE3buf" = A.sb from rfl]
    ptx_branches4
    all_goals ptx_addrs4 [A.sb, A.out] [1024 * (A.j % 2) + t.tid.x.toNat,
      t.ctaid.x.toNat * A.B.toNat + t.tid.x.toNat]
    all_goals (try and_intros)
    all_goals first
      | exact trivial
      | (exfalso; omega)
      | exact accessOk_elem_mem (N := 2048) (List.mem_singleton.2 rfl) fsb sal (by omega)
      | exact accessOk_elem_mem (N := A.n.toNat) (by simp) fout oal (by omega)
      | exact fun y hy => .inl ⟨trivial, by omega, hy⟩
      | exact fun y hy => .inl ⟨rfl, by omega, hy⟩
      | exact fun y hy => ⟨trivial, by omega, hy⟩
      | exact fun y hy => ⟨rfl, by omega, hy⟩
      | (rintro ⟨sp, y⟩ ⟨-, hlt, -⟩; exfalso; omega)
      | (rintro ⟨sp, y⟩ ⟨hsp, hlt, hy⟩
         try simp only at hsp
         subst hsp
         show _ = cells _ _ _ m₀ y
         rw [← elem_elem] at hy ⊢
         refine wr_cells (fits_tail fout (c := t.ctaid.x.toNat * A.B.toNat) (M := _) (by omega))
           (by omega) hy ?_
         simp only [lo32_ext32, lo32_rd_b4]
         exact hrd)
    done
  · have h1 := hpw1 hj1
    have h2' := h2 hj1
    simp only [ptx_eval, K, E5rSpec.«s_pingpong», Block.Args.launch, Block.Args.params, spec_input,
      spec_output, spec_length, mem, Phased.J, phased, foot_store A t, gid, Nat.min_self,
      hr1, hr2, hr3, hr18, hr19, hrd2, hp1, hr48, hr51, ↓reduceIte, List.map_cons, List.map_nil,
      show ¬ (A.j + 1 + 1 < A.j + 2) by omega]
    try simp only [show A.sh "_ZZ10s_pingpongE3buf" = A.sb from rfl]
    ptx_branches4
    all_goals ptx_addrs4 [A.sb, A.out] [1024 * (A.j % 2) + t.tid.x.toNat,
      t.ctaid.x.toNat * A.B.toNat + t.tid.x.toNat]
    all_goals (try and_intros)
    all_goals first
      | exact trivial
      | (exfalso; omega)
      | exact accessOk_elem_mem (N := 2048) (List.mem_singleton.2 rfl) fsb sal (by omega)
      | exact accessOk_elem_mem (N := A.n.toNat) (by simp) fout oal (by omega)
      | exact fun y hy => .inl ⟨trivial, by omega, hy⟩
      | exact fun y hy => .inl ⟨rfl, by omega, hy⟩
      | exact fun y hy => ⟨trivial, by omega, hy⟩
      | exact fun y hy => ⟨rfl, by omega, hy⟩
      | (rintro ⟨sp, y⟩ ⟨-, hlt, -⟩; exfalso; omega)
      | (rintro ⟨sp, y⟩ ⟨hsp, hlt, hy⟩
         try simp only at hsp
         subst hsp
         show _ = cells _ _ _ m₀ y
         rw [← elem_elem] at hy ⊢
         refine wr_cells (fits_tail fout (c := t.ctaid.x.toNat * A.B.toNat) (M := _) (by omega))
           (by omega) hy ?_
         simp only [lo32_ext32, lo32_rd_b4]
         exact hrd)
    done

  · have h1 := hpw1 hj1
    have h2' := h2 hj1
    simp only [ptx_eval, K, E5rSpec.«s_pingpong», Block.Args.launch, Block.Args.params, spec_input,
      spec_output, spec_length, mem, Phased.J, phased, foot_store A t, gid, Nat.min_self,
      hr1, hr2, hr3, hr18, hr19, hrd2, hp1, hr48, hr51, ↓reduceIte, List.map_cons, List.map_nil,
      show ¬ (A.j + 1 + 1 < A.j + 2) by omega]
    try simp only [show A.sh "_ZZ10s_pingpongE3buf" = A.sb from rfl]
    ptx_branches4
    all_goals ptx_addrs4 [A.sb, A.out] [1024 * (A.j % 2) + t.tid.x.toNat,
      t.ctaid.x.toNat * A.B.toNat + t.tid.x.toNat]
    all_goals (try and_intros)
    all_goals first
      | exact trivial
      | (exfalso; omega)
      | exact accessOk_elem_mem (N := 2048) (List.mem_singleton.2 rfl) fsb sal (by omega)
      | exact accessOk_elem_mem (N := A.n.toNat) (by simp) fout oal (by omega)
      | exact fun y hy => .inl ⟨trivial, by omega, hy⟩
      | exact fun y hy => .inl ⟨rfl, by omega, hy⟩
      | exact fun y hy => ⟨trivial, by omega, hy⟩
      | exact fun y hy => ⟨rfl, by omega, hy⟩
      | (rintro ⟨sp, y⟩ ⟨-, hlt, -⟩; exfalso; omega)
      | (rintro ⟨sp, y⟩ ⟨hsp, hlt, hy⟩
         try simp only at hsp
         subst hsp
         show _ = cells _ _ _ m₀ y
         rw [← elem_elem] at hy ⊢
         refine wr_cells (fits_tail fout (c := t.ctaid.x.toNat * A.B.toNat) (M := _) (by omega))
           (by omega) hy ?_
         simp only [lo32_ext32, lo32_rd_b4]
         exact hrd)
    done

/-- Phase `p < R + 2` is the load, a round, or the store. -/
theorem phase_cases {p : Nat} (hp : p < A.j + 2) :
    p = 0 ∨ (∃ k < A.j, p = k + 1) ∨ p = A.j + 1 := by
  rcases Nat.eq_zero_or_pos p with h | h
  · exact .inl h
  · by_cases hR : p = A.j + 1
    · exact .inr (.inr hR)
    · exact .inr (.inl ⟨p - 1, by omega, by omega⟩)

/-- A byte of buffer `s` that no thread writes is outside the buffer's cells. -/
theorem outside_buf (hpre : Pre K A) {b : Dim3} (hb : ∃ t ∈ (A.launch A.n.toNat).threads, t.ctaid = b)
    {s : Nat} (hs : s < 2) {y : Addr}
    (hno : ∀ u ∈ (A.launch A.n.toNat).threads, u.ctaid = b →
      ¬ covers (elem A.sb (1024 * s + u.tid.x.toNat)) 4 y) :
    ¬ (y - bf A s).toNat < 4 * A.B.toNat := by
  intro h
  have hm := A.th_mem hb (i := (y - bf A s).toNat / 4) (by omega)
  apply hno _ hm.1 rfl
  rw [hm.2, ← elem_elem]
  exact covers_of_lt (fits_bf A hpre s hs) h

theorem cells_out {base y : Addr} {N : Nat} {V : Nat → BitVec 32} {m : Mem}
    (h : ¬ (y - base).toNat < 4 * N) : cells base N V m y = m y := by
  show (if (y - base).toNat < 4 * N then _ else m y) = m y
  simp only [h, ↓reduceIte]

theorem ok (hpre : Pre K A) (m₀ : Mem) (sh₀ : Dim3 → Mem) (r₀ : Tid → String → Val)
    (p₀ : Tid → String → Bool) : (phased A m₀ sh₀).Ok K (A.launch A.n.toNat) r₀ p₀ m₀ sh₀ := by
  obtain ⟨sal, fsb, hBW, sbb⟩ := fits_sb A hpre
  have fsbB : Fits A.sb A.B.toNat := by unfold Fits at fsb ⊢; omega
  have hB1 := hpre.1
  have hGB := hpre.2.2.2.2.1
  have fx := hpre.2.2.2.2.2.2.1
  have fout := hpre.2.2.2.2.2.2.2.2.1
  have hsep := hpre.2.2.2.2.2.2.2.2.2.2.1
  refine ⟨fun _ _ => by simp [phased], fun _ _ => rfl, fun _ _ _ => rfl, ?_, ?_, ?_, ?_,
    fun _ _ _ _ h => h.elim, fun _ _ h => h.elim⟩
  · intro t ht k hk s hs
    simp only [phased] at hk hs ⊢
    rcases phase_cases A hk with rfl | ⟨i, hi, rfl⟩ | rfl
    · exact phase_load A hpre m₀ sh₀ ht s hs
    · exact phase_round A hpre m₀ sh₀ ht hi s hs
    · exact phase_store A hpre m₀ sh₀ ht s hs
  · -- what nobody wrote in a phase is unchanged by it
    intro b k x hb hk hno
    simp only [phased] at hk hno ⊢
    have hb' := hb
    obtain ⟨t₀, ht₀, rfl⟩ := hb'
    obtain ⟨sp, y⟩ := x
    rcases phase_cases A hk with rfl | ⟨i, hi, rfl⟩ | rfl
    · cases sp with
      | global => simp only [mem, Heap.get, Heap.at, show (0 : Nat) ≠ A.j + 1 by omega, ↓reduceIte]
      | shared =>
        show sm A m₀ _ (sh₀ t₀.ctaid) (min 0 A.j) y = sh₀ t₀.ctaid y
        rw [show min 0 A.j = 0 by omega]
        unfold sm
        simp only [↓reduceIte]
        have hbf0 : bf A 0 = A.sb := by simp [bf]
        have hout := outside_buf A hpre hb (s := 0) (by omega) (y := y) fun u hu hc hcv => ?_
        · rw [hbf0] at hout; exact cells_out hout
        have := hno u hu hc
        rw [foot_load] at this
        exact this ⟨rfl, by simpa using hcv⟩
    · cases sp with
      | global =>
        simp only [mem, Heap.get, Heap.at, show i + 1 ≠ A.j + 1 by omega, show i ≠ A.j + 1 by omega,
          ↓reduceIte]
      | shared =>
        show sm A m₀ _ (sh₀ t₀.ctaid) (min (i + 1) A.j) y = sm A m₀ _ (sh₀ t₀.ctaid) (min i A.j) y
        rw [show min (i + 1) A.j = i + 1 by omega, show min i A.j = i by omega]
        have hout := outside_buf A hpre hb (s := (i + 1) % 2) (by omega) fun u hu hc hcv => by
          have := hno u hu hc
          rw [foot_round A u hi] at this
          exact this ⟨rfl, hcv⟩
        unfold sm
        simp only [show i + 1 ≠ 0 by omega, ↓reduceIte, Nat.add_sub_cancel]
        rw [cells_out hout, show (i + 1 + 1) % 2 = i % 2 by omega]
        split
        · next h0 => subst h0; rw [show bf A 0 = A.sb by simp [bf]]
        · apply cells_congr (fun _ => rfl)
          intro _
          rw [show (i + 1) % 2 = (i + 1) % 2 from rfl] at hout
          exact (cells_out hout).symm
    · cases sp with
      | shared =>
        show sm A m₀ _ (sh₀ t₀.ctaid) (min (A.j + 1) A.j) y = sm A m₀ _ (sh₀ t₀.ctaid) (min A.j A.j) y
        rw [show min (A.j + 1) A.j = A.j by omega, Nat.min_self]
      | global =>
        show (if A.j + 1 = A.j + 1 then _ else m₀) y = (if A.j = A.j + 1 then _ else m₀) y
        simp only [↓reduceIte, show A.j ≠ A.j + 1 by omega]
        show cells _ _ _ m₀ y = m₀ y
        unfold cells; split
        · next h =>
          exfalso
          have hcnt : (y - elem A.out (t₀.ctaid.x.toNat * A.B.toNat)).toNat / 4 <
              min A.B.toNat (A.n.toNat - t₀.ctaid.x.toNat * A.B.toNat) := by omega
          have hm := A.th_mem hb (i := (y - elem A.out (t₀.ctaid.x.toNat * A.B.toNat)).toNat / 4)
            (by omega)
          have hnw := hno _ hm.1 rfl
          rw [foot_store] at hnw
          have hf := fits_tail fout (c := t₀.ctaid.x.toNat * A.B.toNat)
            (M := min A.B.toNat (A.n.toNat - t₀.ctaid.x.toNat * A.B.toNat)) (by omega)
          refine hnw ⟨rfl, ?_, ?_⟩
          · show t₀.ctaid.x.toNat * A.B.toNat + (th t₀.ctaid _).tid.x.toNat < _
            rw [hm.2]; omega
          show covers (elem A.out ((th t₀.ctaid _).ctaid.x.toNat * A.B.toNat +
            (th t₀.ctaid _).tid.x.toNat)) 4 y
          rw [hm.2, show (th t₀.ctaid _).ctaid = t₀.ctaid from rfl, ← elem_elem]
          exact covers_of_lt hf h
        · rfl
  · -- in one phase of one CTA, no thread writes what another touches
    intro t ht u hu htu hc k hk x hw htc
    simp only [phased] at hk hw htc
    have hne := A.tid_ne ht hu hc htu
    obtain ⟨htc', hti, -⟩ := A.thread_facts hGB ht
    obtain ⟨huc', hui, -⟩ := A.thread_facts hGB hu
    have hcx : t.ctaid.x.toNat = u.ctaid.x.toNat := by rw [hc]
    obtain ⟨sp, y⟩ := x
    rcases phase_cases A hk with rfl | ⟨i, hi, rfl⟩ | rfl
    · rw [foot_load] at hw htc
      obtain ⟨hsp, hcv⟩ := hw
      rcases htc with ⟨hsp', -⟩ | ⟨-, hcv'⟩
      · simp only at hsp hsp'; rw [hsp] at hsp'; cases hsp'
      · exact elem_disjoint fsbB hti hui hne hcv hcv'
    · rw [foot_round A t hi] at hw
      rw [foot_round A u hi] at htc
      obtain ⟨-, hcv⟩ := hw
      have hpw := pow_lt A hpre hi
      have hpw0 := Nat.one_le_two_pow (n := i)
      rcases htc with ⟨-, hcv' | ⟨hle, hcv'⟩⟩ | ⟨-, hcv'⟩
      · exact elem_disjoint fsb (by omega) (by omega) (by omega) hcv hcv'
      · exact elem_disjoint fsb (by omega) (by omega) (by omega) hcv hcv'
      · exact elem_disjoint fsb (by omega) (by omega) (by omega) hcv hcv'
    · rw [foot_store] at hw htc
      obtain ⟨hsp, hlt, hcv⟩ := hw
      rcases htc with ⟨hsp', -⟩ | ⟨-, hlt', hcv'⟩
      · simp only at hsp hsp'; rw [hsp] at hsp'; cases hsp'
      · exact elem_disjoint fout hlt hlt' (by simp only [gid]; rw [hcx]; omega) hcv hcv'
  · -- across CTAs, no global byte one writes is touched by another
    intro t ht u hu hc k hk j' hj a hw htc
    simp only [phased] at hk hj hw htc
    have hkS : k = A.j + 1 := by
      rcases phase_cases A hk with rfl | ⟨i, hi, rfl⟩ | rfl
      · rw [foot_load] at hw; exact absurd hw.1 nofun
      · rw [foot_round A t hi] at hw; exact absurd hw.1 nofun
      · rfl
    subst hkS
    rw [foot_store] at hw
    obtain ⟨-, hlt, hcv⟩ := hw
    have hgid := A.gid_ne ht hu hc
    rcases phase_cases A hj with rfl | ⟨i, hi, rfl⟩ | rfl
    · rw [foot_load] at htc
      rcases htc with ⟨-, hlt', hcv'⟩ | ⟨h, -⟩
      · exact elem_disjoint₂ fout fx (by omega) hlt hlt' hcv hcv'
      · exact absurd h nofun
    · rw [foot_round A u hi] at htc
      rcases htc with ⟨h, -⟩ | ⟨h, -⟩ <;> exact absurd h nofun
    · rw [foot_store] at htc
      rcases htc with ⟨h, -⟩ | ⟨-, hlt', hcv'⟩
      · exact absurd h nofun
      · exact elem_disjoint fout hlt hlt' hgid hcv hcv'

end

theorem correct : E5rSpec.statement := by
  intro A hpre m₀ sh₀ r₀ p₀ L c₀
  have R := Phased.phase_sound (ok A hpre m₀ sh₀ r₀ p₀)
  have hB1 := hpre.1
  have hBR := hpre.2.2.1
  have hnGB := hpre.2.2.2.2.2.1
  have fout := hpre.2.2.2.2.2.2.2.2.1
  refine ⟨R.noFault, R.progress, R.bounded, R.raceFree,
    Phased.exists_done_of R.progress R.bounded, fun c hc hd => ?_⟩
  obtain ⟨hw, hun, -⟩ := R.final c hc hd
  refine ⟨fun i hi => ?_, fun y hy => hun y ?_ (fun _ h => h.elim)⟩
  · have hq : i / A.B.toNat < A.G.toNat := by
      rw [Nat.div_lt_iff_lt_mul (by omega)]; omega
    have hr : i % A.B.toNat < A.B.toNat := Nat.mod_lt _ (by omega)
    have hgi : i / A.B.toNat * A.B.toNat + i % A.B.toNat = i := by
      rw [Nat.mul_comm]; exact Nat.div_add_mod i A.B.toNat
    generalize i / A.B.toNat = q at hq hgi ⊢
    generalize i % A.B.toNat = r at hr hgi ⊢
    subst hgi
    obtain ⟨ht, hc', ht'⟩ := A.th_of (len := A.n.toNat) hq hr
    have hmem : ∀ a, covers (elem A.out (q * A.B.toNat + r)) 4 a → c.mem a = _ := fun a hcv => by
      refine hw _ ht (A.j + 1) (by simp [phased]) a ?_
      show (foot A _ (A.j + 1)).w (.global, a)
      rw [foot_store]
      refine ⟨rfl, ?_, ?_⟩
      · show (BitVec.ofNat 32 q).toNat * A.B.toNat + (BitVec.ofNat 32 r).toNat < _
        rw [hc', ht']; exact hi
      · show covers (elem A.out ((BitVec.ofNat 32 q).toNat * A.B.toNat + (BitVec.ofNat 32 r).toNat)) 4 a
        rw [hc', ht']; exact hcv
    rw [rd32_congr hmem]
    simp only [phased, mem, ↓reduceIte, hc', outs]
    rw [← elem_elem,
      rd32_cells (fits_tail fout (c := q * A.B.toNat) (M := _) (by omega)) (by omega),
      V_final A m₀ _ (by omega)]
    refine accUpTo_congr fun j hj => ?_
    simp only [Block.Args.seg]
    split <;> first | rfl | (exfalso; omega)
  · intro t ht k hk hwk
    simp only [phased] at hk hwk
    rcases phase_cases A hk with rfl | ⟨i, hi, rfl⟩ | rfl
    · rw [foot_load] at hwk; exact absurd hwk.1 nofun
    · rw [foot_round A t hi] at hwk; exact absurd hwk.1 nofun
    · rw [foot_store] at hwk
      exact hy _ hwk.2.1 hwk.2.2

end E5rProof
