/- Launch/allocation domain for direct OSS incKernel translation validation.
There is deliberately no function describing the expected output. -/
import Ptx.Auto.Map
import Ptx.Logic.Relational

namespace Ptx.Auto.OssInc
open Ptx

structure Spec where
  input : String
  output : String
  length : String
  repeats : String

namespace Spec
variable (S : Spec) (A : Args)

def launch : Launch :=
  { grid := ⟨A.G,1,1⟩, block := ⟨A.B,1,1⟩,
    params := fun p => if p = S.input then A.base S.input else
      if p = S.output then A.base S.output else if p = S.length then ext32 A.n else if p = S.repeats then 5 else 0,
    alloc := [⟨A.base S.input,4*A.n.toNat⟩,⟨A.base S.output,4*A.n.toNat⟩] }

def Pre : Prop :=
  Fits (A.base S.input) A.n.toNat ∧ Fits (A.base S.output) A.n.toNat ∧
  (A.base S.input).toNat % 4 = 0 ∧ (A.base S.output).toNat % 4 = 0 ∧
  ((A.base S.input).toNat + 4*A.n.toNat ≤ (A.base S.output).toNat ∨
    (A.base S.output).toNat + 4*A.n.toNat ≤ (A.base S.input).toNat) ∧
  A.n.toNat < 2^31 ∧ A.n.toNat ≤ A.G.toNat*A.B.toNat ∧ A.G.toNat*A.B.toNat ≤ 2^31

def R (i : Nat) (x : Addr) : Prop :=
  i < A.n.toNat ∧ covers (elem (A.base S.input) i) 4 x

def W (i : Nat) (x : Addr) : Prop :=
  i < A.n.toNat ∧ covers (elem (A.base S.output) i) 4 x

/-- Every valid parameter valuation, arbitrary input/global memory and initial
register/predicate/shared memory, and every independent pair of completed
interleavings. Total correctness of each side is part of the statement. -/
def Equivalent (original optimized : Kernel) : Prop :=
  ∀ (A : Args) (m : Mem) (sh : Dim3 → Mem)
    (r : Tid → String → Val) (p : Tid → String → Bool), S.Pre A →
    Relational.Equivalent original optimized (S.launch A) (Cfg.init r p m sh)
      (fun t => S.W A (gid A.B t))

theorem oneD : (S.launch A).OneD A.G A.B := ⟨rfl,rfl⟩

theorem disjoint {S : Spec} {A : Args} (hp : S.Pre A) :
    ∀ t ∈ (S.launch A).threads, ∀ u ∈ (S.launch A).threads, t ≠ u → ∀ x,
      S.W A (gid A.B t) x → ¬ S.R A (gid A.B u) x ∧ ¬ S.W A (gid A.B u) x := by
  have hsep := hp.2.2.2.2.1
  have htail := hp.2.2.2.2.2.1
  intro t ht u hu htu x ⟨hi,hx⟩
  have ne : gid A.B t ≠ gid A.B u := fun e => htu ((S.oneD A).gid_inj ht hu e)
  refine ⟨?_,?_⟩
  · rintro ⟨hj,hcov⟩
    exact elem_disjoint₂ hp.2.1 hp.1 (by omega) hi (by omega) hx hcov
  · rintro ⟨hj,hcov⟩
    exact elem_disjoint hp.2.1 hi hj ne hx hcov

theorem access_input {S : Spec} {A : Args} (hp : S.Pre A) {i : Nat} (hi : i < A.n.toNat) :
    accessOk (S.launch A).alloc (elem (A.base S.input) i) .b4 = true := by
  have htail := hp.2.2.2.2.2.1
  have h : i < A.n.toNat := hi
  simp only [accessOk,launch,Size.bytes_b4,Bool.and_eq_true,beq_iff_eq,
    aligned_elem hp.1 h hp.2.2.1,true_and,List.any_cons,List.any_nil,Bool.or_false]
  simp [holds_elem hp.1 h]

theorem access_output {S : Spec} {A : Args} (hp : S.Pre A) {i : Nat} (hi : i < A.n.toNat) :
    accessOk (S.launch A).alloc (elem (A.base S.output) i) .b4 = true := by
  simp only [accessOk,launch,Size.bytes_b4,Bool.and_eq_true,beq_iff_eq,
    aligned_elem hp.2.1 hi hp.2.2.2.1,true_and,List.any_cons,List.any_nil,Bool.or_false]
  simp [holds_elem hp.2.1 hi]

theorem load_foot {S : Spec} {A : Args} {i : Nat} (hi : i < A.n.toNat) :
    InFoot (S.R A i) (S.W A i) ⟨.global,elem (A.base S.input) i,.b4,.read⟩ :=
  ⟨rfl,nofun,fun _ hx => .inr ⟨rfl,hi,hx⟩⟩

theorem store_foot {S : Spec} {A : Args} {i : Nat} (hi : i < A.n.toNat) :
    InFoot (S.R A i) (S.W A i) ⟨.global,elem (A.base S.output) i,.b4,.write⟩ :=
  ⟨rfl,nofun,fun _ hx => .inl ⟨hi,hx⟩⟩
end Spec
end Ptx.Auto.OssInc
