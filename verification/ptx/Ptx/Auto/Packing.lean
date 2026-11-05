/-
Byte packing contracts over the existing PTX/SIMT model. One thread owns a
chunk; accesses remain naturally aligned u32 loads/stores. Observable output
bits are specified from input bytes, independently of candidate instructions.
-/
import Ptx.Auto.Map

namespace Ptx.Auto.Packing
open Ptx

inductive Op where
  | pack | unpack | threshold
  deriving DecidableEq, Repr

def Op.iw : Op → Nat | .unpack => 1 | _ => 8
def Op.count (op : Op) (n : Nat) : Nat := if op = .unpack then n / 8 else 8*n
def Op.index (op : Op) (i j : Nat) : Nat := if op = .unpack then i / 8 else 8*i+j

structure Spec where
  op : Op
  input : String
  output : String
  length : String

namespace Spec

variable (S : Spec) (A : Args)

def launch : Launch :=
  { grid := ⟨A.G, 1, 1⟩, block := ⟨A.B, 1, 1⟩,
    params := fun p => if p = S.input then A.base S.input else
      if p = S.output then A.base S.output else if p = S.length then ext32 A.n else 0,
    alloc := [⟨A.base S.input, 4 * (S.op.count A.n.toNat)⟩,
      ⟨A.base S.output, 4 * (A.n.toNat)⟩] }

def Pre : Prop :=
  Fits (A.base S.input) (S.op.count A.n.toNat) ∧
  Fits (A.base S.output) (A.n.toNat) ∧
  (A.base S.input).toNat % 4 = 0 ∧ (A.base S.output).toNat % 4 = 0 ∧
  ((A.base S.input).toNat + 4 * (S.op.count A.n.toNat) ≤ (A.base S.output).toNat ∨
   (A.base S.output).toNat + 4 * (A.n.toNat) ≤ (A.base S.input).toNat) ∧
  (S.op = .unpack → A.n.toNat % 8 = 0) ∧
  A.n.toNat ≤ A.G.toNat * A.B.toNat ∧ A.G.toNat * A.B.toNat ≤ 2^31

/-- Bit k of output word j in group i. Little bit order within each byte.
Packing tests the entire uint8 value for nonzero. Threshold uses x > 127.
Unpacking writes one byte 0 or 1 per input bit, so seven bits are zero. -/
def bit (m : Mem) (i k : Nat) : Bool :=
  match S.op with
  | .pack => m (A.base S.input + BitVec.ofNat 64 (32*i+k)) != 0
  | .threshold => (m (A.base S.input + BitVec.ofNat 64 (32*i+k))).getLsbD 7
  | .unpack => k % 8 == 0 &&
      (rd32 m (elem (A.base S.input) (i/8))).getLsbD (4*(i%8) + k/8)

def R (i : Nat) (x : Addr) : Prop :=
  i < A.n.toNat ∧ ∃ j < S.op.iw, covers (elem (A.base S.input) (S.op.index i j)) 4 x

def W (i : Nat) (x : Addr) : Prop :=
  i < A.n.toNat ∧ covers (elem (A.base S.output) i) 4 x

def Post (m₀ : Mem) (i : Nat) (m : Mem) : Prop :=
  i < A.n.toNat → ∀ k < 32,
    (rd32 m (elem (A.base S.output) i)).getLsbD k = S.bit A m₀ i k

def Correct (K : Kernel) : Prop :=
  K.shared = [] ∧ ∀ (A : Args) (m₀ : Mem) (s₀ : Dim3 → Mem)
      (r₀ : Tid → String → Val) (p₀ : Tid → String → Bool), S.Pre A →
    let L := S.launch A
    let c₀ := Cfg.init r₀ p₀ m₀ s₀
    (∀ c, Reach K L c₀ c → ¬ Faults K L c) ∧
    (∀ c, Reach K L c₀ c → Done K L c ∨ ∃ c', Step K L c c') ∧
    (∃ bound, ∀ j c, Steps K L j c₀ c → j ≤ bound) ∧
    RaceFree K L c₀ ∧ (∃ c, Reach K L c₀ c ∧ Done K L c) ∧
    (∀ c, Reach K L c₀ c → Done K L c →
      (∀ i, S.Post A m₀ i c.mem) ∧
      (∀ x, (∀ i, ¬ S.W A i x) → c.mem x = m₀ x))

def ThreadOk (K : Kernel) : Prop :=
  ∀ A, S.Pre A → ∀ m₀, ∀ t ∈ (S.launch A).threads, ∀ r p,
    Safe K (S.launch A).alloc ((S.launch A).ctx t)
      (S.R A (gid A.B t)) (S.W A (gid A.B t))
      (fun s m => action K ((S.launch A).ctx t) s = .done ∧ S.Post A m₀ (gid A.B t) m)
      ⟨0,r,p⟩ m₀

theorem oneD : (S.launch A).OneD A.G A.B := ⟨rfl,rfl⟩

theorem correct_of {S : Spec} {K : Kernel} (hsh : K.shared = []) (h : S.ThreadOk K) :
    S.Correct K := by
  refine ⟨hsh, ?_⟩
  intro A m₀ s₀ r₀ p₀ hp L c₀
  obtain ⟨fi, fo, ai, ao, sep, htail, hn, hmax⟩ := hp
  have hd := S.oneD A
  have solo : ∀ t ∈ L.threads, ∃ k,
      Solo K L.alloc (L.ctx t) (S.R A (gid A.B t)) (S.W A (gid A.B t))
        (s0 r₀ p₀ m₀ t) m₀ k ∧
      S.Post A m₀ (gid A.B t) (trace K L.alloc (L.ctx t) k (s0 r₀ p₀ m₀ t) m₀).2 :=
    fun t ht => (h A ⟨fi,fo,ai,ao,sep,htail,hn,hmax⟩ m₀ t ht (r₀ t) (p₀ t)).solo
  have disj : ∀ t ∈ L.threads, ∀ u ∈ L.threads, t ≠ u → ∀ x,
      S.W A (gid A.B t) x → ¬ S.R A (gid A.B u) x ∧ ¬ S.W A (gid A.B u) x := by
    intro t ht u hu htu x ⟨hit, hx⟩
    have ne : gid A.B t ≠ gid A.B u := fun e => htu (hd.gid_inj ht hu e)
    refine ⟨?_, ?_⟩
    · rintro ⟨hiu,k,hk,hkcv⟩
      apply elem_disjoint₂ fo fi (by omega) hit ?_ hx hkcv
      cases hop : S.op <;> simp_all [Op.count, Op.index, Op.iw] <;> omega
    · rintro ⟨hiu,hkcv⟩
      exact elem_disjoint fo hit hiu ne hx hkcv
  obtain ⟨bound, g⟩ := grid_sound solo disj s₀
  refine ⟨g.noFault, g.progress, ⟨bound,g.bounded⟩, g.raceFree, g.exists_done, ?_⟩
  intro c hr hdone
  obtain ⟨own, frame⟩ := g.final c hr hdone
  refine ⟨?_, fun x hx => frame x fun t ht hw => hx _ hw⟩
  intro i hi k hk
  have hiGB : i < A.G.toNat * A.B.toNat := by omega
  obtain ⟨hm,hg⟩ := hd.owner_mem hiGB
  obtain ⟨M, hP, hM⟩ := own _ hm
  rw [hg] at hP
  rw [rd32_congr (fun x hx => hM x (by rw [hg]; exact ⟨hi,hx⟩))]
  exact hP hi k hk


theorem access_input {S : Spec} {A : Args} (hp : S.Pre A) {i : Nat}
    (hi : i < S.op.count A.n.toNat) :
    accessOk (S.launch A).alloc (elem (A.base S.input) i) .b4 = true := by
  simp only [accessOk, launch, Size.bytes_b4, Bool.and_eq_true, beq_iff_eq,
    aligned_elem hp.1 hi hp.2.2.1, true_and, List.any_cons, List.any_nil, Bool.or_false]
  simp [holds_elem hp.1 hi]

theorem access_output {S : Spec} {A : Args} (hp : S.Pre A) {i : Nat}
    (hi : i < A.n.toNat) :
    accessOk (S.launch A).alloc (elem (A.base S.output) i) .b4 = true := by
  simp only [accessOk, launch, Size.bytes_b4, Bool.and_eq_true, beq_iff_eq,
    aligned_elem hp.2.1 hi hp.2.2.2.1, true_and, List.any_cons, List.any_nil, Bool.or_false]
  simp [holds_elem hp.2.1 hi]

theorem load_foot {S : Spec} {A : Args} {i j : Nat} (hi : i < A.n.toNat) (hj : j < S.op.iw) :
    InFoot (S.R A i) (S.W A i)
      ⟨.global, elem (A.base S.input) (S.op.index i j), .b4, .read⟩ :=
  ⟨rfl, nofun, fun _ hx => .inr ⟨rfl, hi, j, hj, hx⟩⟩

theorem store_foot {S : Spec} {A : Args} {i : Nat} (hi : i < A.n.toNat) :
    InFoot (S.R A i) (S.W A i)
      ⟨.global, elem (A.base S.output) i, .b4, .write⟩ :=
  ⟨rfl, nofun, fun _ hx => .inl ⟨hi, hx⟩⟩

theorem rd32_wr_indices {base : Addr} {N i j : Nat} (hf : Fits base N)
    (hi : i < N) (hj : j < N) (m : Mem) (v : Val) :
    rd32 (wr m (elem base i) .b4 v) (elem base j) =
      if i = j then lo32 v else rd32 m (elem base j) := by
  split
  · rename_i h; subst h; exact rd32_wr_same _ _ _
  · rename_i h
    exact rd32_wr_disjoint (fun x hx => elem_disjoint hf hj hi (Ne.symm h) hx)

end Spec

end Ptx.Auto.Packing
