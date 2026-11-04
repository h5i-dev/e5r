/-
M4: the Hillis-Steele block scan nvcc 13.2 emits (benchmarks/correct/scan_nvcc.{cu,ptx}),
verified on its PTX for every block size up to 1024, every grid size and every
input length the grid covers.

```c
__shared__ unsigned s[1024];
s[tid] = i < n ? x[i] : 0;                    // phase 0, then bar.sync
for (off = 1; off < blockDim.x; off <<= 1) {
  unsigned t = tid >= off ? s[tid - off] : 0; // phase 2k + 1, then bar.sync
  s[tid] += t;                                // phase 2k + 2, then bar.sync
}
if (i < n) out[i] = s[tid];                   // phase 2K + 1
```

With `K` rounds (`2^(K-1) < B ≤ 2^K`), after round `k` `s[i]` holds the sum of
the `2^k` elements ending at `i` (`V_window`); after the last, the prefix sum
of the block's segment.
-/
import Ptx.Logic.PhaseSound
import Ptx.Logic.PhaseWp
import Ptx.Logic.Cells
import Ptx.Tactics.EvalR
import Ptx.Auto.Tactic4
import Ptx.Examples.Reduce
import Ptx.Kernels.ScanNvcc

set_option linter.unusedSimpArgs false

namespace Ptx.Examples.Scan
open Ptx Ptx.Examples.Reduce

abbrev K := Ptx.Kernels.ScanNvcc.«scan»

/-- The launch-time values the theorem quantifies over: `G` blocks of `B`
threads, `R` rounds of the loop (`R = ⌈log₂ B⌉`). -/
structure Args where
  G : BitVec 32
  B : BitVec 32
  R : Nat
  n : BitVec 32
  x : Addr
  out : Addr
  sh : String → Addr

namespace Args
variable (A : Args)

def sb : Addr := A.sh "_ZZ4scanE1s"

def params : String → Val := fun p =>
  if p = "scan_param_0" then A.x else if p = "scan_param_1" then A.out
  else if p = "scan_param_2" then ext32 A.n else 0

def launch : Launch :=
  { grid := ⟨A.G, 1, 1⟩, block := ⟨A.B, 1, 1⟩, params := A.params,
    alloc := [⟨A.x, 4 * A.n.toNat⟩, ⟨A.out, 4 * A.n.toNat⟩], shared := A.sh }

def Pre : Prop :=
  1 ≤ A.B.toNat ∧ A.B.toNat ≤ 1024 ∧ A.B.toNat ≤ 2 ^ A.R ∧ (A.R = 0 ∨ 2 ^ (A.R - 1) < A.B.toNat) ∧
  A.G.toNat * A.B.toNat ≤ 2 ^ 32 ∧ A.n.toNat ≤ A.G.toNat * A.B.toNat ∧
  Fits A.x A.n.toNat ∧ A.x.toNat % 4 = 0 ∧ Fits A.out A.n.toNat ∧ A.out.toNat % 4 = 0 ∧
  (A.x.toNat + 4 * A.n.toNat ≤ A.out.toNat ∨ A.out.toNat + 4 * A.n.toNat ≤ A.x.toNat) ∧
  LayoutOk K A.sh

/-- Element `i` of CTA `b`'s segment, `0` past the end of the input. -/
def seg (m₀ : Mem) (b i : Nat) : BitVec 32 :=
  if b * A.B.toNat + i < A.n.toNat then rd32 m₀ (elem A.x (b * A.B.toNat + i)) else 0

/-- What `s[i]` holds after round `k`. -/
def V (m₀ : Mem) (b : Nat) : Nat → Nat → BitVec 32
  | 0, i => A.seg m₀ b i
  | k + 1, i => if 2 ^ k ≤ i then V m₀ b k i + V m₀ b k (i - 2 ^ k) else V m₀ b k i

/-- What thread `i` reads in round `k`. -/
def rv (m₀ : Mem) (b k i : Nat) : BitVec 32 := if 2 ^ k ≤ i then A.V m₀ b k (i - 2 ^ k) else 0

end Args

/-! ### The rounds compute window sums, and the last one the prefix sum -/

theorem accUpTo_add (f : Nat → BitVec 32) (a b : Nat) :
    accUpTo f (a + b) = accUpTo f a + accUpTo (fun m => f (a + m)) b := by
  induction b with
  | zero => simp [accUpTo]
  | succ b ih => rw [← Nat.add_assoc]; simp only [accUpTo]; rw [ih, BitVec.add_assoc]

theorem accUpTo_succ' (f : Nat → BitVec 32) (N : Nat) :
    accUpTo f (N + 1) = f 0 + accUpTo (fun m => f (m + 1)) N := by
  rw [Nat.add_comm, accUpTo_add]; simp [accUpTo, Nat.add_comm 1]

theorem accUpTo_rev (f : Nat → BitVec 32) : ∀ N, accUpTo f N = accUpTo (fun m => f (N - 1 - m)) N := by
  intro N
  induction N with
  | zero => rfl
  | succ N ih =>
    rw [accUpTo_succ' (fun m => f (N + 1 - 1 - m)), show accUpTo f (N + 1) = accUpTo f N + f N from rfl, ih]
    rw [BitVec.add_comm]
    congr 1
    exact accUpTo_congr fun m hm => by congr 1; omega

namespace Args
variable (A : Args)

theorem V_window (m₀ : Mem) (b : Nat) : ∀ k i,
    A.V m₀ b k i = accUpTo (fun m => A.seg m₀ b (i - m)) (min (2 ^ k) (i + 1)) := by
  intro k
  induction k with
  | zero => intro i; simp [V, accUpTo, show min 1 (i + 1) = 1 by omega]
  | succ k ih =>
    intro i
    have hp : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by rw [Nat.pow_succ]; omega
    by_cases hi : 2 ^ k ≤ i
    · rw [show A.V m₀ b (k + 1) i = A.V m₀ b k i + A.V m₀ b k (i - 2 ^ k) by simp [V, hi], ih, ih,
        show min (2 ^ (k + 1)) (i + 1) = 2 ^ k + min (2 ^ k) (i - 2 ^ k + 1) by omega,
        show min (2 ^ k) (i + 1) = 2 ^ k by omega, accUpTo_add]
      congr 1
      exact accUpTo_congr fun m _ => by congr 1; omega
    · rw [show A.V m₀ b (k + 1) i = A.V m₀ b k i by simp [V, hi], ih,
        show min (2 ^ (k + 1)) (i + 1) = i + 1 by omega, show min (2 ^ k) (i + 1) = i + 1 by omega]

/-! ### The phases: 0 loads; `2i+1` reads `s[tid - 2^i]`; `2i+2` adds it; `2R+1` stores -/

/-- What thread `t` touches in phase `p`. -/
def foot (t : Tid) (p : Nat) : Foot :=
  if p = 0 then
    { r := fun l => l.1 = .global ∧ t.ctaid.x.toNat * A.B.toNat + t.tid.x.toNat < A.n.toNat ∧
        covers (elem A.x (t.ctaid.x.toNat * A.B.toNat + t.tid.x.toNat)) 4 l.2
      w := fun l => l.1 = .shared ∧ covers (elem A.sb t.tid.x.toNat) 4 l.2 }
  else if p = 2 * A.R + 1 then
    { r := fun l => l.1 = .shared ∧ t.ctaid.x.toNat * A.B.toNat + t.tid.x.toNat < A.n.toNat ∧
        covers (elem A.sb t.tid.x.toNat) 4 l.2
      w := fun l => l.1 = .global ∧ t.ctaid.x.toNat * A.B.toNat + t.tid.x.toNat < A.n.toNat ∧
        covers (elem A.out (t.ctaid.x.toNat * A.B.toNat + t.tid.x.toNat)) 4 l.2 }
  else if p % 2 = 1 then
    { r := fun l => l.1 = .shared ∧ 2 ^ (p / 2) ≤ t.tid.x.toNat ∧
        covers (elem A.sb (t.tid.x.toNat - 2 ^ (p / 2))) 4 l.2
      w := fun _ => False }
  else
    { r := fun _ => False
      w := fun l => l.1 = .shared ∧ covers (elem A.sb t.tid.x.toNat) 4 l.2 }

/-- The outputs of CTA `b` after the last round. -/
def outs (m₀ : Mem) (b : Nat) : Mem :=
  cells (elem A.out (b * A.B.toNat)) (min A.B.toNat (A.n.toNat - b * A.B.toNat)) (A.V m₀ b A.R) m₀

/-- CTA `b`'s view when phase `p` starts. -/
def mem (m₀ : Mem) (sh₀ : Dim3 → Mem) (b : Dim3) : Nat → Heap
  | 0 => ⟨m₀, sh₀ b⟩
  | p + 1 =>
    ⟨if p = 2 * A.R + 1 then A.outs m₀ b.x.toNat else m₀,
     cells A.sb A.B.toNat (A.V m₀ b.x.toNat (p / 2)) (sh₀ b)⟩

def regsOk (t : Tid) (s : TState) : Prop :=
  s.r "%r1" = ext32 A.B ∧ s.r "%r2" = ext32 t.tid.x ∧
  s.r "%r3" = ext32 (BitVec.ofNat 32 (t.ctaid.x.toNat * A.B.toNat + t.tid.x.toNat)) ∧
  s.r "%r6" = ext32 (BitVec.ofNat 32 (A.sb.toNat + 4 * t.tid.x.toNat)) ∧
  s.r "%r15" = ext32 (BitVec.ofNat 32 A.sb.toNat) ∧ s.r "%rd2" = A.out ∧
  s.p "%p1" = decide (A.n.toNat ≤ t.ctaid.x.toNat * A.B.toNat + t.tid.x.toNat)

/-- The registers at the start of each phase. -/
def T (m₀ : Mem) (t : Tid) (p : Nat) (s : TState) : Prop :=
  if p = 0 then s.pc = 0
  else A.regsOk t s ∧
    if p % 2 = 1 then
      (if p = 1 then s.pc = 19 else s.pc = 34 ∧ s.r "%r26" = ext32 (BitVec.ofNat 32 (2 ^ (p / 2 - 1))))
    else
      s.pc = 30 ∧ s.r "%r26" = ext32 (BitVec.ofNat 32 (2 ^ (p / 2 - 1))) ∧
        s.r "%r27" = ext32 (A.rv m₀ t.ctaid.x.toNat (p / 2 - 1) t.tid.x.toNat)

def phased (m₀ : Mem) (sh₀ : Dim3 → Mem) : Phased where
  P := fun _ => 2 * A.R + 2
  F := A.foot
  T := A.T m₀
  N := fun _ _ => 40
  M := A.mem m₀ sh₀
  bpc := fun _ p => if p = 0 then 18 else if p % 2 = 1 then 29 else 33
  Cell := fun _ => False
  Δ := fun _ _ _ => 0

/-- After the last round, `s[i]` is the prefix sum of the segment up to `i`. -/
theorem V_final (m₀ : Mem) (b : Nat) {i : Nat} (hi : i < 2 ^ A.R) :
    A.V m₀ b A.R i = accUpTo (fun j => A.seg m₀ b j) (i + 1) := by
  rw [A.V_window, show min (2 ^ A.R) (i + 1) = i + 1 by omega, accUpTo_rev (fun j => A.seg m₀ b j)]
  exact accUpTo_congr fun m hm => by congr 1

theorem launch_oneD : A.launch.OneD A.G A.B := ⟨rfl, rfl⟩

theorem sb_facts (hpre : A.Pre) : A.sb.toNat % 4 = 0 ∧ A.sb.toNat + 4096 ≤ 2 ^ 32 :=
  hpre.2.2.2.2.2.2.2.2.2.2.2.1 ⟨"_ZZ4scanE1s", 4, 4096⟩ (by simp [K, Ptx.Kernels.ScanNvcc.scan])

theorem thread_facts (hpre : A.Pre) {t : Tid} (ht : t ∈ A.launch.threads) :
    t.ctaid.x.toNat < A.G.toNat ∧ t.tid.x.toNat < A.B.toNat ∧ A.B.toNat ≤ 1024 ∧
      t.ctaid.x.toNat * A.B.toNat + t.tid.x.toNat < A.G.toNat * A.B.toNat ∧
      A.G.toNat * A.B.toNat ≤ 2 ^ 32 ∧
      t.ctaid.y = 0 ∧ t.ctaid.z = 0 ∧ t.tid.y = 0 ∧ t.tid.z = 0 := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := A.launch_oneD.thread ht
  exact ⟨h1, h2, hpre.2.1, gid_lt_of h1 h2, hpre.2.2.2.2.1, h3, h4, h5, h6⟩

theorem gid_toNat {t : Tid} (hcB : t.ctaid.x.toNat * A.B.toNat + t.tid.x.toNat < A.G.toNat * A.B.toNat)
    (hGB : A.G.toNat * A.B.toNat ≤ 2 ^ 32) :
    (t.ctaid.x * A.B + t.tid.x).toNat = t.ctaid.x.toNat * A.B.toNat + t.tid.x.toNat := by
  rw [BitVec.toNat_add, BitVec.toNat_mul, Nat.mod_eq_of_lt (a := t.ctaid.x.toNat * A.B.toNat) (by omega),
    Nat.mod_eq_of_lt (by omega)]

omit A in
theorem lo32_ofInt_zero : lo32 (BitVec.ofInt 64 0) = 0 := by decide

set_option maxHeartbeats 4000000 in
theorem phase0 (hpre : A.Pre) (m₀ : Mem) (sh₀ : Dim3 → Mem) {t : Tid} (ht : t ∈ A.launch.threads)
    (s : TState) (hs : A.T m₀ t 0 s) :
    Run K (A.launch.allocs K) (A.launch.ctx t) (A.foot t 0) (fun _ => False) add32
      ((A.phased m₀ sh₀).J K A.launch t 0) 40 s (A.mem m₀ sh₀ t.ctaid 0) (fun _ => 0) := by
  obtain ⟨pc, r, p⟩ := s
  simp only [T, ↓reduceIte] at hs; subst hs
  obtain ⟨hc, hi, hB, hcB, hGB, -, -, -, -⟩ := A.thread_facts hpre ht
  obtain ⟨sal, sbb⟩ := A.sb_facts hpre
  have fx := hpre.2.2.2.2.2.2.1
  have xal := hpre.2.2.2.2.2.2.2.1
  have fsb : Fits A.sb 1024 := by unfold Fits; omega
  have fsbB : Fits A.sb A.B.toNat := by unfold Fits at fsb ⊢; omega
  have hcB' : t.ctaid.x.toNat * A.B.toNat < 2 ^ 32 := by omega
  have hg := A.gid_toNat hcB hGB
  refine (wpR_sound (cut := fun _ => false) ?_).weaken fun s h d hq => hq.1
  simp only [ptx_eval, K, Ptx.Kernels.ScanNvcc.scan, launch, params, mem, Phased.J, phased,
    List.map_cons, List.map_nil, foot, ↓reduceIte]
  simp only [show A.sh "_ZZ4scanE1s" = A.sb from rfl]
  ptx_branches4
  all_goals ptx_addrs4 [A.sb, A.x] [t.tid.x.toNat, t.ctaid.x.toNat * A.B.toNat + t.tid.x.toNat]
  all_goals (try and_intros)
  all_goals first
    | trivial
    | (exfalso; omega)
    | exact accessOk_elem_mem (N := 1024) (by simp) fsb sal (by omega)
    | exact accessOk_elem_mem (N := A.n.toNat) (by simp) fx xal (by omega)
    | exact fun y hy => ⟨rfl, hy⟩
    | exact fun y hy => ⟨trivial, hy⟩
    | exact fun y hy => .inl ⟨rfl, by omega, hy⟩
    | exact fun y hy => .inl ⟨trivial, by omega, hy⟩
    | (rintro ⟨sp, y⟩ ⟨hsp, hy⟩
       try simp only at hsp
       subst hsp
       refine wr_cells fsbB hi hy ?_
       simp only [V, seg, Nat.zero_div, lo32_ext32, lo32_rd_b4, lo32_ofInt_zero]
       split <;> first | rfl | (exfalso; omega))
    | (simp only [T, regsOk, upd, String.reduceEq, ↓reduceIte, true_and, and_true,
         show (1 : Nat) ≠ 0 by decide, Nat.one_mod]
       all_goals (try and_intros)
       all_goals first
         | ptx_reg4
         | (rw [Ptx.Auto.ule_toNat, hg]))

theorem pow_lt (hpre : A.Pre) {i : Nat} (hi : i < A.R) : 2 ^ i < A.B.toNat := by
  rcases hpre.2.2.2.1 with h | h
  · omega
  · exact Nat.lt_of_le_of_lt (Nat.pow_le_pow_right (by decide) (by omega)) h

theorem foot_read (t : Tid) {i : Nat} (hi : i < A.R) : A.foot t (2 * i + 1) =
    { r := fun l => l.1 = .shared ∧ 2 ^ i ≤ t.tid.x.toNat ∧ covers (elem A.sb (t.tid.x.toNat - 2 ^ i)) 4 l.2
      w := fun _ => False } := by
  simp only [foot, show 2 * i + 1 ≠ 0 by omega, show 2 * i + 1 ≠ 2 * A.R + 1 by omega, ↓reduceIte,
    show (2 * i + 1) % 2 = 1 by omega, show (2 * i + 1) / 2 = i by omega]

theorem foot_add (t : Tid) {i : Nat} (hi : i < A.R) : A.foot t (2 * i + 2) =
    { r := fun _ => False, w := fun l => l.1 = .shared ∧ covers (elem A.sb t.tid.x.toNat) 4 l.2 } := by
  simp only [foot, show 2 * i + 2 ≠ 0 by omega, show 2 * i + 2 ≠ 2 * A.R + 1 by omega, ↓reduceIte,
    show (2 * i + 2) % 2 = 0 by omega, show ¬ (0 = 1) by decide]

theorem foot_store (t : Tid) : A.foot t (2 * A.R + 1) =
    { r := fun l => l.1 = .shared ∧ t.ctaid.x.toNat * A.B.toNat + t.tid.x.toNat < A.n.toNat ∧
        covers (elem A.sb t.tid.x.toNat) 4 l.2
      w := fun l => l.1 = .global ∧ t.ctaid.x.toNat * A.B.toNat + t.tid.x.toNat < A.n.toNat ∧
        covers (elem A.out (t.ctaid.x.toNat * A.B.toNat + t.tid.x.toNat)) 4 l.2 } := by
  simp only [foot, show 2 * A.R + 1 ≠ 0 by omega, ↓reduceIte]

/-- The entry state of an odd phase `2i + 1`: at the barrier after the load
(`i = 0`) or at the loop's second barrier with the previous offset. -/
theorem T_odd {m₀ : Mem} {t : Tid} {i pc : Nat} {r : String → Val} {p : String → Bool}
    (hs : A.T m₀ t (2 * i + 1) ⟨pc, r, p⟩) :
    (r "%r1" = ext32 A.B ∧ r "%r2" = ext32 t.tid.x ∧
      r "%r3" = ext32 (BitVec.ofNat 32 (t.ctaid.x.toNat * A.B.toNat + t.tid.x.toNat)) ∧
      r "%r6" = ext32 (BitVec.ofNat 32 (A.sb.toNat + 4 * t.tid.x.toNat)) ∧
      r "%r15" = ext32 (BitVec.ofNat 32 A.sb.toNat) ∧ r "%rd2" = A.out ∧
      p "%p1" = decide (A.n.toNat ≤ t.ctaid.x.toNat * A.B.toNat + t.tid.x.toNat)) ∧
    ((i = 0 ∧ pc = 19) ∨ (1 ≤ i ∧ pc = 34 ∧ r "%r26" = ext32 (BitVec.ofNat 32 (2 ^ (i - 1))))) := by
  simp only [T, regsOk, show 2 * i + 1 ≠ 0 by omega, ↓reduceIte, show (2 * i + 1) % 2 = 1 by omega,
    show (2 * i + 1) / 2 = i by omega] at hs
  refine ⟨hs.1, ?_⟩
  by_cases h : i = 0
  · subst h; exact .inl ⟨rfl, by simpa using hs.2⟩
  · simp only [show 2 * i + 1 ≠ 1 by omega, ↓reduceIte] at hs
    exact .inr ⟨by omega, hs.2⟩

set_option maxHeartbeats 4000000 in
theorem phase_read (hpre : A.Pre) (m₀ : Mem) (sh₀ : Dim3 → Mem) {t : Tid} (ht : t ∈ A.launch.threads)
    {i : Nat} (hiR : i < A.R) (s : TState) (hs : A.T m₀ t (2 * i + 1) s) :
    Run K (A.launch.allocs K) (A.launch.ctx t) (A.foot t (2 * i + 1)) (fun _ => False) add32
      ((A.phased m₀ sh₀).J K A.launch t (2 * i + 1)) 40 s (A.mem m₀ sh₀ t.ctaid (2 * i + 1))
      (fun _ => 0) := by
  obtain ⟨hc, hi, hB, hcB, hGB, -, -, -, -⟩ := A.thread_facts hpre ht
  obtain ⟨sal, sbb⟩ := A.sb_facts hpre
  have fsb : Fits A.sb 1024 := by unfold Fits; omega
  have fsbB : Fits A.sb A.B.toNat := by unfold Fits at fsb ⊢; omega
  have hpw := A.pow_lt hpre hiR
  have hpw2 : i ≥ 1 → 2 ^ (i - 1) * 2 = 2 ^ i := fun h => by
    rw [← Nat.pow_succ]; congr 1; omega
  have hmid : 2 * i / 2 = i := by omega
  have hp0 : i = 0 → 2 ^ i = 1 := fun h => by rw [h]
  have hB2 : 2 ≤ A.B.toNat := by
    have := A.pow_lt hpre (i := 0) (by omega); simp at this; omega
  obtain ⟨pc, r, p⟩ := s
  obtain ⟨⟨hr1, hr2, hr3, hr6, hr15, hrd2, hp1⟩, ⟨hi0, rfl⟩ | ⟨hi1, rfl, hr26⟩⟩ := A.T_odd hs
  all_goals rw [A.foot_read t hiR]
  all_goals refine (wpR_sound (cut := fun _ => false) ?_).weaken fun s h d hq => hq.1
  all_goals simp only [ptx_eval, K, Ptx.Kernels.ScanNvcc.scan, launch, params, mem, Phased.J, phased,
    List.map_cons, List.map_nil, hr1, hr2, hr3, hr6, hr15, hrd2, ↓reduceIte, A.foot_read t hiR,
    show 2 * i + 1 ≠ 0 by omega, show (2 * i + 1) % 2 = 1 by omega, hmid,
    show 2 * i ≠ 2 * A.R + 1 by omega]
  all_goals try simp only [hr26]
  all_goals simp only [show A.sh "_ZZ4scanE1s" = A.sb from rfl]
  all_goals ptx_branches4
  all_goals ptx_addrs4 [A.sb] [t.tid.x.toNat - 2 ^ i]
  all_goals (try and_intros)
  all_goals first
    | trivial
    | (exfalso; omega)
    | (intro _ h; exact h.elim)
    | exact accessOk_elem_mem (N := 1024) (by simp) fsb sal (by omega)
    | exact fun y hy => .inl ⟨trivial, by omega, hy⟩
    | exact fun y hy => .inl ⟨rfl, by omega, hy⟩
    | (simp only [T, regsOk, upd, String.reduceEq, ↓reduceIte, true_and, and_true,
         show 2 * i + 1 + 1 ≠ 0 by omega, show (2 * i + 1 + 1) % 2 = 0 by omega,
         show ¬ ((0 : Nat) = 1) by decide, show (2 * i + 1 + 1) / 2 - 1 = i by omega]
       all_goals (try and_intros)
       all_goals first
         | ptx_reg4
         | rfl
         | (rw [rd_b4, rd32_cells fsbB (by omega)]
            simp only [rv, show 2 ^ i ≤ t.tid.x.toNat by omega, ↓reduceIte])
         | (simp only [rv, lo32_ofInt_zero, show ¬ 2 ^ i ≤ t.tid.x.toNat by omega, ↓reduceIte]
            first | done | rfl))

theorem T_even {m₀ : Mem} {t : Tid} {i pc : Nat} {r : String → Val} {p : String → Bool}
    (hs : A.T m₀ t (2 * i + 2) ⟨pc, r, p⟩) :
    (r "%r1" = ext32 A.B ∧ r "%r2" = ext32 t.tid.x ∧
      r "%r3" = ext32 (BitVec.ofNat 32 (t.ctaid.x.toNat * A.B.toNat + t.tid.x.toNat)) ∧
      r "%r6" = ext32 (BitVec.ofNat 32 (A.sb.toNat + 4 * t.tid.x.toNat)) ∧
      r "%r15" = ext32 (BitVec.ofNat 32 A.sb.toNat) ∧ r "%rd2" = A.out ∧
      p "%p1" = decide (A.n.toNat ≤ t.ctaid.x.toNat * A.B.toNat + t.tid.x.toNat)) ∧
    pc = 30 ∧ r "%r26" = ext32 (BitVec.ofNat 32 (2 ^ i)) ∧
      r "%r27" = ext32 (A.rv m₀ t.ctaid.x.toNat i t.tid.x.toNat) := by
  simp only [T, regsOk, show 2 * i + 2 ≠ 0 by omega, ↓reduceIte, show (2 * i + 2) % 2 = 0 by omega,
    show ¬ ((0 : Nat) = 1) by decide, show (2 * i + 2) / 2 - 1 = i by omega] at hs
  exact hs

set_option maxHeartbeats 4000000 in
theorem phase_add (hpre : A.Pre) (m₀ : Mem) (sh₀ : Dim3 → Mem) {t : Tid} (ht : t ∈ A.launch.threads)
    {i : Nat} (hiR : i < A.R) (s : TState) (hs : A.T m₀ t (2 * i + 2) s) :
    Run K (A.launch.allocs K) (A.launch.ctx t) (A.foot t (2 * i + 2)) (fun _ => False) add32
      ((A.phased m₀ sh₀).J K A.launch t (2 * i + 2)) 40 s (A.mem m₀ sh₀ t.ctaid (2 * i + 2))
      (fun _ => 0) := by
  obtain ⟨hc, hi, hB, hcB, hGB, -, -, -, -⟩ := A.thread_facts hpre ht
  obtain ⟨sal, sbb⟩ := A.sb_facts hpre
  have fsb : Fits A.sb 1024 := by unfold Fits; omega
  have fsbB : Fits A.sb A.B.toNat := by unfold Fits at fsb ⊢; omega
  have hpw := A.pow_lt hpre hiR
  obtain ⟨pc, r, p⟩ := s
  obtain ⟨⟨hr1, hr2, hr3, hr6, hr15, hrd2, hp1⟩, rfl, hr26, hr27⟩ := A.T_even hs
  rw [A.foot_add t hiR]
  refine (wpR_sound (cut := fun _ => false) ?_).weaken fun s h d hq => hq.1
  simp only [ptx_eval, K, Ptx.Kernels.ScanNvcc.scan, launch, params, mem, Phased.J, phased,
    List.map_cons, List.map_nil, hr1, hr2, hr3, hr6, hr15, hrd2, hr26, hr27, ↓reduceIte,
    A.foot_add t hiR, show 2 * i + 2 ≠ 0 by omega, show (2 * i + 2) % 2 = 0 by omega,
    show ¬ ((0 : Nat) = 1) by decide, show (2 * i + 1) / 2 = i by omega,
    show (2 * i + 2) / 2 = i + 1 by omega, show 2 * i + 1 ≠ 2 * A.R + 1 by omega,
    show 2 * i + 2 ≠ 2 * A.R + 1 by omega]
  simp only [show A.sh "_ZZ4scanE1s" = A.sb from rfl]
  ptx_branches4
  all_goals ptx_addrs4 [A.sb] [t.tid.x.toNat]
  all_goals (try and_intros)
  all_goals first
    | trivial
    | (exfalso; omega)
    | exact accessOk_elem_mem (N := 1024) (by simp) fsb sal (by omega)
    | exact fun y hy => .inr ⟨trivial, hy⟩
    | exact fun y hy => .inr ⟨rfl, hy⟩
    | exact fun y hy => ⟨trivial, hy⟩
    | exact fun y hy => ⟨rfl, hy⟩
    | (rintro ⟨sp, y⟩ ⟨hsp, hy⟩
       try simp only at hsp
       subst hsp
       refine wr_cells fsbB hi hy ?_
       simp only [lo32_ext32, lo32_rd_b4]
       rw [rd32_cells fsbB hi]
       simp only [V, rv]
       split <;> simp)
    | (simp only [T, regsOk, upd, String.reduceEq, ↓reduceIte, true_and, and_true,
         show 2 * i + 2 + 1 ≠ 0 by omega, show (2 * i + 2 + 1) % 2 = 1 by omega,
         show 2 * i + 2 + 1 ≠ 1 by omega, show (2 * i + 2 + 1) / 2 - 1 = i by omega]
       all_goals (try and_intros)
       all_goals first | ptx_reg4 | rfl | assumption)

set_option maxHeartbeats 4000000 in
theorem phase_store (hpre : A.Pre) (m₀ : Mem) (sh₀ : Dim3 → Mem) {t : Tid} (ht : t ∈ A.launch.threads)
    (s : TState) (hs : A.T m₀ t (2 * A.R + 1) s) :
    Run K (A.launch.allocs K) (A.launch.ctx t) (A.foot t (2 * A.R + 1)) (fun _ => False) add32
      ((A.phased m₀ sh₀).J K A.launch t (2 * A.R + 1)) 40 s (A.mem m₀ sh₀ t.ctaid (2 * A.R + 1))
      (fun _ => 0) := by
  obtain ⟨hc, hi, hB, hcB, hGB, -, -, -, -⟩ := A.thread_facts hpre ht
  obtain ⟨sal, sbb⟩ := A.sb_facts hpre
  have fsb : Fits A.sb 1024 := by unfold Fits; omega
  have fsbB : Fits A.sb A.B.toNat := by unfold Fits at fsb ⊢; omega
  have fout := hpre.2.2.2.2.2.2.2.2.1
  have oal := hpre.2.2.2.2.2.2.2.2.2.1
  have hBR := hpre.2.2.1
  have hpw2 : A.R ≥ 1 → 2 ^ (A.R - 1) * 2 = 2 ^ A.R := fun h => by
    rw [← Nat.pow_succ]; congr 1; omega
  have hR0 : A.R = 0 → A.B.toNat = 1 := fun h => by rw [h] at hBR; have := hpre.1; simp at hBR; omega
  have hmid : 2 * A.R / 2 = A.R := by omega
  have hcB' : t.ctaid.x.toNat * A.B.toNat < 2 ^ 32 := by omega
  obtain ⟨pc, r, p⟩ := s
  obtain ⟨⟨hr1, hr2, hr3, hr6, hr15, hrd2, hp1⟩, ⟨hi0, rfl⟩ | ⟨hi1, rfl, hr26⟩⟩ := A.T_odd hs
  · have hB1 := hR0 hi0
    rw [A.foot_store t]
    refine (wpR_sound (cut := fun _ => false) ?_).weaken fun s h d hq => hq.1
    simp only [ptx_eval, K, Ptx.Kernels.ScanNvcc.scan, launch, params, mem, Phased.J, phased,
      List.map_cons, List.map_nil, hr1, hr2, hr3, hr6, hr15, hrd2, hp1, ↓reduceIte, A.foot_store t,
      hmid, show 2 * A.R ≠ 2 * A.R + 1 by omega, show ¬ (2 * A.R + 1 + 1 < 2 * A.R + 2) by omega]
    all_goals simp only [show A.sh "_ZZ4scanE1s" = A.sb from rfl]
    all_goals ptx_branches4
    all_goals ptx_addrs4 [A.sb, A.out] [t.tid.x.toNat, t.ctaid.x.toNat * A.B.toNat + t.tid.x.toNat]
    all_goals (try and_intros)
    all_goals first
      | trivial
      | (exfalso; omega)
      | exact accessOk_elem_mem (N := 1024) (by simp) fsb sal (by omega)
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
         rw [rd32_cells fsbB hi])
  · have h1 := hpw2 hi1
    have h2 : 2 ^ (A.R - 1) < A.B.toNat := by rcases hpre.2.2.2.1 with h | h <;> omega
    rw [A.foot_store t]
    refine (wpR_sound (cut := fun _ => false) ?_).weaken fun s h d hq => hq.1
    simp only [ptx_eval, K, Ptx.Kernels.ScanNvcc.scan, launch, params, mem, Phased.J, phased,
      List.map_cons, List.map_nil, hr1, hr2, hr3, hr6, hr15, hrd2, hp1, hr26, ↓reduceIte, A.foot_store t,
      hmid, show 2 * A.R ≠ 2 * A.R + 1 by omega, show ¬ (2 * A.R + 1 + 1 < 2 * A.R + 2) by omega]
    all_goals simp only [show A.sh "_ZZ4scanE1s" = A.sb from rfl]
    all_goals ptx_branches4
    all_goals ptx_addrs4 [A.sb, A.out] [t.tid.x.toNat, t.ctaid.x.toNat * A.B.toNat + t.tid.x.toNat]
    all_goals (try and_intros)
    all_goals first
      | trivial
      | (exfalso; omega)
      | exact accessOk_elem_mem (N := 1024) (by simp) fsb sal (by omega)
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
         rw [rd32_cells fsbB hi])

/-! ### The side conditions of the phase theorem -/

theorem tid_ne (hpre : A.Pre) {t u : Tid} (ht : t ∈ A.launch.threads) (hu : u ∈ A.launch.threads)
    (hc : t.ctaid = u.ctaid) (htu : t ≠ u) : t.tid.x.toNat ≠ u.tid.x.toNat := by
  intro h
  obtain ⟨-, -, -, -, -, -, -, ht5, ht6⟩ := A.thread_facts hpre ht
  obtain ⟨-, -, -, -, -, -, -, hu5, hu6⟩ := A.thread_facts hpre hu
  apply htu
  rcases t with ⟨tc, ⟨tx, ty, tz⟩⟩; rcases u with ⟨uc, ⟨ux, uy, uz⟩⟩
  simp only at hc h ht5 ht6 hu5 hu6
  subst hc ht5 ht6 hu5 hu6
  rw [BitVec.eq_of_toNat_eq h]

theorem cta_ne (hpre : A.Pre) {t u : Tid} (ht : t ∈ A.launch.threads) (hu : u ∈ A.launch.threads)
    (hc : t.ctaid ≠ u.ctaid) : t.ctaid.x.toNat ≠ u.ctaid.x.toNat := by
  intro h
  obtain ⟨-, -, -, -, -, ht3, ht4, -, -⟩ := A.thread_facts hpre ht
  obtain ⟨-, -, -, -, -, hu3, hu4, -, -⟩ := A.thread_facts hpre hu
  apply hc
  rcases t with ⟨⟨tx, ty, tz⟩, _⟩; rcases u with ⟨⟨ux, uy, uz⟩, _⟩
  simp only at h ht3 ht4 hu3 hu4
  subst ht3 ht4 hu3 hu4
  rw [BitVec.eq_of_toNat_eq h]

/-- The thread with index `i` in CTA `b`. -/
def th (b : Dim3) (i : Nat) : Tid := ⟨b, ⟨BitVec.ofNat 32 i, 0, 0⟩⟩

theorem th_mem (hpre : A.Pre) {b : Dim3} (hb : ∃ t ∈ A.launch.threads, t.ctaid = b) {i : Nat}
    (hi : i < A.B.toNat) : th b i ∈ A.launch.threads ∧ (th b i).tid.x.toNat = i := by
  obtain ⟨t, ht, rfl⟩ := hb
  have hB := hpre.2.1
  have hti : (BitVec.ofNat 32 i).toNat = i := by simp; omega
  refine ⟨?_, hti⟩
  have := ht
  rw [mem_threads] at this ⊢
  obtain ⟨h1, h2, h3, _, _, _⟩ := this
  refine ⟨h1, h2, h3, ?_, ?_, ?_⟩
  · show (BitVec.ofNat 32 i).toNat < A.B.toNat; rw [hti]; exact hi
  · show (0 : BitVec 32).toNat < (1 : BitVec 32).toNat; decide
  · show (0 : BitVec 32).toNat < (1 : BitVec 32).toNat; decide

/-- Phase `p < 2R + 2` is the load, a read, an add, or the store. -/
theorem phase_cases {p : Nat} (hp : p < 2 * A.R + 2) :
    p = 0 ∨ (∃ i < A.R, p = 2 * i + 1) ∨ (∃ i < A.R, p = 2 * i + 2) ∨ p = 2 * A.R + 1 := by
  rcases Nat.mod_two_eq_zero_or_one p with h | h
  · by_cases h0 : p = 0
    · exact .inl h0
    · exact .inr (.inr (.inl ⟨p / 2 - 1, by omega, by omega⟩))
  · by_cases hR : p = 2 * A.R + 1
    · exact .inr (.inr (.inr hR))
    · exact .inr (.inl ⟨p / 2, by omega, by omega⟩)

theorem ok (hpre : A.Pre) (m₀ : Mem) (sh₀ : Dim3 → Mem) (r₀ : Tid → String → Val)
    (p₀ : Tid → String → Bool) : (A.phased m₀ sh₀).Ok K A.launch r₀ p₀ m₀ sh₀ := by
  obtain ⟨sal, sbb⟩ := A.sb_facts hpre
  have fsb : Fits A.sb 1024 := by unfold Fits; omega
  have hBle := hpre.2.1
  have hB1 := hpre.1
  have fsbB : Fits A.sb A.B.toNat := by unfold Fits at fsb ⊢; omega
  have fx := hpre.2.2.2.2.2.2.1
  have fout := hpre.2.2.2.2.2.2.2.2.1
  have hsep := hpre.2.2.2.2.2.2.2.2.2.2.1
  refine ⟨fun _ _ => by simp [phased], fun _ _ => by simp [phased, T], fun _ _ _ => rfl, ?_, ?_, ?_, ?_,
    fun _ _ _ _ h => h.elim, fun _ _ h => h.elim⟩
  · intro t ht k hk s hs
    simp only [phased] at hk ⊢
    rcases A.phase_cases hk with rfl | ⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩ | rfl
    · exact A.phase0 hpre m₀ sh₀ ht s hs
    · exact A.phase_read hpre m₀ sh₀ ht hi s hs
    · exact A.phase_add hpre m₀ sh₀ ht hi s hs
    · exact A.phase_store hpre m₀ sh₀ ht s hs
  · intro b k x hb hk hno
    simp only [phased] at hk hno ⊢
    have hb' := hb
    obtain ⟨t₀, ht₀, rfl⟩ := hb'
    obtain ⟨sp, y⟩ := x
    have cellOf : ∀ (h : (y - A.sb).toNat < 4 * A.B.toNat),
        th t₀.ctaid ((y - A.sb).toNat / 4) ∈ A.launch.threads ∧
          (th t₀.ctaid ((y - A.sb).toNat / 4)).tid.x.toNat = (y - A.sb).toNat / 4 ∧
          covers (elem A.sb ((y - A.sb).toNat / 4)) 4 y :=
      fun h => ⟨(A.th_mem hpre hb (i := (y - A.sb).toNat / 4) (by omega)).1,
        (A.th_mem hpre hb (i := (y - A.sb).toNat / 4) (by omega)).2, covers_of_lt fsbB h⟩
    rcases A.phase_cases hk with rfl | ⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩ | rfl
    · cases sp with
      | global =>
        simp only [mem, Heap.get, Heap.at]
        repeat' split
        all_goals first | rfl | (exfalso; omega)
      | shared =>
        show cells A.sb A.B.toNat _ (sh₀ t₀.ctaid) y = sh₀ t₀.ctaid y
        unfold cells; split
        · next h =>
          obtain ⟨hm, hti, hcv⟩ := cellOf h
          have hnw := hno _ hm rfl
          simp only [foot, ↓reduceIte] at hnw
          exact absurd ⟨by trivial, by rw [hti]; exact hcv⟩ hnw
        · rfl
    · cases sp with
      | global =>
        simp only [mem, Heap.get, Heap.at]
        repeat' split
        all_goals first | rfl | (exfalso; omega)
      | shared =>
        show cells _ _ (A.V m₀ _ ((2 * i + 1) / 2)) _ y = cells _ _ (A.V m₀ _ (2 * i / 2)) _ y
        rw [show (2 * i + 1) / 2 = i by omega, show 2 * i / 2 = i by omega]
    · cases sp with
      | global =>
        simp only [mem, Heap.get, Heap.at]
        repeat' split
        all_goals first | rfl | (exfalso; omega)
      | shared =>
        show cells _ _ (A.V m₀ _ ((2 * i + 2) / 2)) _ y = cells _ _ (A.V m₀ _ ((2 * i + 1) / 2)) _ y
        unfold cells; split
        · next h =>
          obtain ⟨hm, hti, hcv⟩ := cellOf h
          have hnw := hno _ hm rfl
          rw [A.foot_add _ hi] at hnw
          exact absurd ⟨rfl, by rw [hti]; exact hcv⟩ hnw
        · rfl
    · cases sp with
      | shared =>
        show cells _ _ (A.V m₀ _ ((2 * A.R + 1) / 2)) _ y = cells _ _ (A.V m₀ _ (2 * A.R / 2)) _ y
        rw [show (2 * A.R + 1) / 2 = A.R by omega, show 2 * A.R / 2 = A.R by omega]
      | global =>
        show (if 2 * A.R + 1 = 2 * A.R + 1 then _ else m₀) y = (if 2 * A.R = 2 * A.R + 1 then _ else m₀) y
        simp only [↓reduceIte, show 2 * A.R ≠ 2 * A.R + 1 by omega]
        show cells _ _ _ m₀ y = m₀ y
        unfold cells; split
        · next h =>
          exfalso
          have hcnt : (y - elem A.out (t₀.ctaid.x.toNat * A.B.toNat)).toNat / 4 <
              min A.B.toNat (A.n.toNat - t₀.ctaid.x.toNat * A.B.toNat) := by omega
          have hm := A.th_mem hpre hb (i := (y - elem A.out (t₀.ctaid.x.toNat * A.B.toNat)).toNat / 4)
            (by omega)
          have hnw := hno _ hm.1 rfl
          rw [A.foot_store] at hnw
          have hf := fits_tail fout (c := t₀.ctaid.x.toNat * A.B.toNat)
            (M := min A.B.toNat (A.n.toNat - t₀.ctaid.x.toNat * A.B.toNat)) (by omega)
          have hlt : t₀.ctaid.x.toNat * A.B.toNat +
              (y - elem A.out (t₀.ctaid.x.toNat * A.B.toNat)).toNat / 4 < A.n.toNat := by omega
          refine hnw ⟨rfl, ?_, ?_⟩
          · show t₀.ctaid.x.toNat * A.B.toNat + (th t₀.ctaid _).tid.x.toNat < _
            rw [hm.2]; exact hlt
          show covers (elem A.out ((th t₀.ctaid _).ctaid.x.toNat * A.B.toNat +
            (th t₀.ctaid _).tid.x.toNat)) 4 y
          rw [hm.2, show (th t₀.ctaid _).ctaid = t₀.ctaid from rfl, ← elem_elem]
          exact covers_of_lt hf h
        · rfl
  · intro t ht u hu htu hc k hk x hw htc
    simp only [phased] at hk hw htc
    have hne := A.tid_ne hpre ht hu hc htu
    obtain ⟨htc', hti, -, -, -, -⟩ := A.thread_facts hpre ht
    obtain ⟨huc', hui, -, -, -, -⟩ := A.thread_facts hpre hu
    have hcx : t.ctaid.x.toNat = u.ctaid.x.toNat := by rw [hc]
    obtain ⟨sp, y⟩ := x
    rcases A.phase_cases hk with rfl | ⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩ | rfl
    · simp only [foot, ↓reduceIte] at hw htc
      obtain ⟨hsp, hcv⟩ := hw
      rcases htc with ⟨hsp', -⟩ | ⟨-, hcv'⟩
      · simp only at hsp hsp'; rw [hsp] at hsp'; cases hsp'
      · exact elem_disjoint fsbB hti hui hne hcv hcv'
    · rw [A.foot_read _ hi] at hw; exact hw
    · rw [A.foot_add _ hi] at hw htc
      rcases htc with h | ⟨-, hcv'⟩
      · exact h
      · exact elem_disjoint fsbB hti hui hne hw.2 hcv'
    · rw [A.foot_store] at hw htc
      obtain ⟨hsp, hlt, hcv⟩ := hw
      rcases htc with ⟨hsp', -⟩ | ⟨-, hlt', hcv'⟩
      · simp only at hsp hsp'; rw [hsp] at hsp'; cases hsp'
      · exact elem_disjoint fout hlt hlt' (by rw [hcx]; omega) hcv hcv'
  · intro t ht u hu hc k hk j' hj a hw htc
    simp only [phased] at hk hj hw htc
    have hcne := A.cta_ne hpre ht hu hc
    obtain ⟨htc', hti, -, -, -, -⟩ := A.thread_facts hpre ht
    obtain ⟨huc', hui, -, -, -, -⟩ := A.thread_facts hpre hu
    have hkS : k = 2 * A.R + 1 := by
      rcases A.phase_cases hk with rfl | ⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩ | rfl
      · simp only [foot, ↓reduceIte] at hw; exact absurd hw.1 nofun
      · rw [A.foot_read _ hi] at hw; exact hw.elim
      · rw [A.foot_add _ hi] at hw; exact absurd hw.1 nofun
      · rfl
    subst hkS
    rw [A.foot_store] at hw
    obtain ⟨-, hlt, hcv⟩ := hw
    -- two global indices of different CTAs differ
    have hgid : t.ctaid.x.toNat * A.B.toNat + t.tid.x.toNat ≠ u.ctaid.x.toNat * A.B.toNat + u.tid.x.toNat := by
      intro h
      apply hcne
      have e1 := Nat.mul_add_div (show 0 < A.B.toNat by omega) t.ctaid.x.toNat t.tid.x.toNat
      have e2 := Nat.mul_add_div (show 0 < A.B.toNat by omega) u.ctaid.x.toNat u.tid.x.toNat
      rw [Nat.div_eq_of_lt hti, Nat.add_zero] at e1
      rw [Nat.div_eq_of_lt hui, Nat.add_zero] at e2
      rw [Nat.mul_comm] at e1 e2
      rw [← e1, ← e2, h]
    rcases A.phase_cases hj with rfl | ⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩ | rfl
    · simp only [foot, ↓reduceIte] at htc
      rcases htc with ⟨-, hlt', hcv'⟩ | ⟨h, -⟩
      · exact elem_disjoint₂ fout fx (by omega) hlt hlt' hcv hcv'
      · exact absurd h nofun
    · rw [A.foot_read _ hi] at htc
      rcases htc with ⟨h, -⟩ | h
      · exact absurd h nofun
      · exact h
    · rw [A.foot_add _ hi] at htc
      rcases htc with h | ⟨h, -⟩
      · exact h
      · exact absurd h nofun
    · rw [A.foot_store] at htc
      rcases htc with ⟨h, -⟩ | ⟨-, hlt', hcv'⟩
      · exact absurd h nofun
      · exact elem_disjoint fout hlt hlt' hgid hcv hcv'

end Args

/-- The scan is correct for every launch in `Pre`: blocks of `B ≤ 1024`
threads with `R` the number of rounds (`B ≤ 2^R`, and `2^(R-1) < B` unless
`R = 0`), `G·B ≤ 2^32` threads covering `n`, input and output arrays of `n`
elements that fit, are aligned and do not overlap, and any placement of the
shared array. Under every initial memory, shared memory and register
content, and every execution: no fault or diverged barrier, progress,
bounded executions, phase-relative race freedom, a finished execution
exists, and when all threads are done every `out[i]` (`i < n`) is the sum of
`x[j]` from the start of `i`'s block to `i`, and no other byte has changed. -/
theorem scan_correct (A : Args) (hpre : A.Pre) (m₀ : Mem) (sh₀ : Dim3 → Mem)
    (r₀ : Tid → String → Val) (p₀ : Tid → String → Bool) :
    let L := A.launch
    let c₀ := Cfg.init r₀ p₀ m₀ sh₀
    (∀ c, Reach K L c₀ c → ¬ Faults K L c) ∧
    (∀ c, Reach K L c₀ c → Done K L c ∨ ∃ c', Step K L c c') ∧
    (∃ bound, ∀ j c, Steps K L j c₀ c → j ≤ bound) ∧
    RaceFree K L c₀ ∧
    (∃ c, Reach K L c₀ c ∧ Done K L c) ∧
    (∀ c, Reach K L c₀ c → Done K L c →
      (∀ i < A.n.toNat, rd32 c.mem (elem A.out i) =
        accUpTo (fun j => rd32 m₀ (elem A.x (i / A.B.toNat * A.B.toNat + j))) (i % A.B.toNat + 1)) ∧
      (∀ y, (∀ i < A.n.toNat, ¬ covers (elem A.out i) 4 y) → c.mem y = m₀ y)) := by
  intro L c₀
  have R := Phased.phase_sound (A.ok hpre m₀ sh₀ r₀ p₀)
  have hB1 := hpre.1
  have hBle := hpre.2.1
  have hBR := hpre.2.2.1
  have hnGB := hpre.2.2.2.2.2.1
  have fout := hpre.2.2.2.2.2.2.2.2.1
  refine ⟨R.noFault, R.progress, R.bounded, R.raceFree,
    Phased.exists_done_of R.progress R.bounded, fun c hc hd => ?_⟩
  obtain ⟨hw, hun, -⟩ := R.final c hc hd
  refine ⟨fun i hi => ?_, fun y hy => hun y ?_ (fun _ h => h.elim)⟩
  · -- thread `i % B` of CTA `i / B` wrote `out[i]` in the last phase
    have hq : i / A.B.toNat < A.G.toNat := by
      rw [Nat.div_lt_iff_lt_mul (by omega)]; omega
    have hr : i % A.B.toNat < A.B.toNat := Nat.mod_lt _ (by omega)
    have hgi : i / A.B.toNat * A.B.toNat + i % A.B.toNat = i := by
      rw [Nat.mul_comm]; exact Nat.div_add_mod i A.B.toNat
    generalize i / A.B.toNat = q at hq hgi ⊢
    generalize i % A.B.toNat = r at hr hgi ⊢
    subst hgi
    let t : Tid := ⟨⟨BitVec.ofNat 32 q, 0, 0⟩, ⟨BitVec.ofNat 32 r, 0, 0⟩⟩
    have hc' : t.ctaid.x.toNat = q := by
      have := A.G.isLt; show (BitVec.ofNat 32 _).toNat = _; simp; omega
    have ht' : t.tid.x.toNat = r := by
      show (BitVec.ofNat 32 _).toNat = _; simp; omega
    have ht : t ∈ L.threads := by
      rw [mem_threads]
      simp only [Launch.Thread, L, Args.launch]
      refine ⟨by rw [hc']; exact hq, by simp [t], by simp [t], by rw [ht']; exact hr, by simp [t],
        by simp [t]⟩
    have hmem : ∀ a, covers (elem A.out (q * A.B.toNat + r)) 4 a → c.mem a = _ := fun a hcv => by
      refine hw t ht (2 * A.R + 1) (by simp [Args.phased]) a ?_
      show (A.foot t (2 * A.R + 1)).w (.global, a)
      rw [A.foot_store, hc', ht']
      exact ⟨rfl, hi, hcv⟩
    rw [rd32_congr hmem]
    simp only [Args.phased, Args.mem, ↓reduceIte, hc', Args.outs]
    rw [← elem_elem,
      rd32_cells (fits_tail fout (c := q * A.B.toNat) (M := _) (by omega)) (by omega),
      A.V_final m₀ _ (by omega)]
    refine accUpTo_congr fun j hj => ?_
    simp only [Args.seg]
    rw [if_pos (by omega)]
  · intro t ht k hk hwk
    simp only [Args.phased] at hk hwk
    rcases A.phase_cases hk with rfl | ⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩ | rfl
    · simp only [Args.foot, ↓reduceIte] at hwk; exact absurd hwk.1 nofun
    · rw [A.foot_read _ hi] at hwk; exact hwk
    · rw [A.foot_add _ hi] at hwk; exact absurd hwk.1 nofun
    · rw [A.foot_store] at hwk
      exact hy _ hwk.2.1 hwk.2.2

/-- The precondition is satisfiable: 3 blocks of 6 threads (3 rounds) over
16 elements, the shared array at offset 0. -/
example : (Args.mk 3 6 3 16 0x1000 0x2000 (fun _ => 0)).Pre := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, by decide, by simp [Fits], by decide,
    by simp [Fits], by decide, by decide, ?_, ?_⟩
  · intro v hv
    simp [K, Ptx.Kernels.ScanNvcc.scan] at hv; subst hv; decide
  · simp [K, Ptx.Kernels.ScanNvcc.scan]

end Ptx.Examples.Scan
