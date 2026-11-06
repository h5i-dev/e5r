/- Proposed first public-API domain, bound to the two exact exported entries.
No theorem of Obligation is supplied or claimed. Preconditions constrain only
launch/input storage and values; they do not assume safety, read-only execution,
race freedom, termination, table preservation or equivalence. -/
import ExactTable
import FiniteScale

namespace FP4Whole.FP32
open Ptx

def original : Kernel := FP4Original.«_Z20kDequantizeBlockwiseIfLi512ELi64ELi8ELi1EEvPfPhS0_PT_ii»
def edited : Kernel := FP4Edited.«_Z20kDequantizeBlockwiseIfLi512ELi64ELi8ELi1EEvPfPhS0_PT_ii»

theorem exact_parameter_abi : original.params = edited.params := rfl
theorem exact_shared_layout_declarations : original.shared = edited.shared := rfl

/-- The real emitted entries never load their declared codebook pointer. -/
def codeUnusedB (K : Kernel) : Bool := K.body.all fun st =>
  match st.instr with
  | .ld .param _ _ (.param name _) => name != original.name ++ "_param_0"
  | _ => true

theorem exact_unused_code_parameter : codeUnusedB original && codeUnusedB edited = true := by
  decide +kernel

def param (i : Nat) : String := original.name ++ "_param_" ++ toString i

/-- First scope: public blocksize1024, positive n<2^31, arbitrary tails. Eager
scale reads need exactly ceil(n/1024) finite scales, with no padded extra slots. -/
structure Args where
  n : Nat
  packed : Addr
  scales : Addr
  output : Addr
  unusedCode : Addr
  symbols : String → Addr

def Args.tiles (A : Args) : Nat := (A.n + 1023) / 1024

def Args.caller (A : Args) : List Region :=
  [⟨A.packed, (A.n+1)/2⟩, ⟨A.scales, 4*A.tiles⟩, ⟨A.output, 4*A.n⟩]

def Args.statics (A : Args) : List Region :=
  FP4Original.module.globals.map (fun g => ⟨A.symbols g.name, g.bytes.length⟩)

def Args.launch (A : Args) (nan : Tid → TState → Val) : Launch where
  grid := ⟨BitVec.ofNat 32 A.tiles, 1, 1⟩
  block := ⟨64, 1, 1⟩
  params := fun p =>
    if p = param 0 then A.unusedCode else
    if p = param 1 then A.packed else
    if p = param 2 then A.scales else
    if p = param 3 then A.output else
    if p = param 4 then 1024 else
    if p = param 5 then BitVec.ofNat 64 A.n else 0
  alloc := A.caller ++ A.statics
  shared := A.symbols
  nan := nan

def separated (a b : Region) : Prop :=
  a.base.toNat + a.size ≤ b.base.toNat ∨ b.base.toNat + b.size ≤ a.base.toNat

/-- Exact allocations, finite user scales, initialized original module state.
The code pointer is unused by this entry; no valid allocation is demanded for it.
Shared initial bytes and all initial registers/predicates remain arbitrary. -/
def Args.Pre (A : Args) (m : Mem) (nan : Tid → TState → Val) : Prop :=
  0 < A.n ∧ A.n < 2^31 ∧
  A.scales.toNat % 4 = 0 ∧ A.output.toNat % 4 = 0 ∧
  (∀ r ∈ A.caller ++ A.statics, r.base.toNat + r.size ≤ 2^64) ∧
  (A.caller ++ A.statics).Pairwise separated ∧
  LayoutOk original A.symbols ∧
  FP4Original.module.GlobalsReady (A.launch nan) m ∧
  ∀ i < A.tiles, FP4Sign.Finite32 (rd32 m (A.scales + BitVec.ofNat 64 (4*i))).toNat

def Args.outputBytes (A : Args) : Addr → Prop := covers A.output (4*A.n)

/-- OPEN target over actual independently completed executions and Total for
both exact kernels. Merely compiling this proposition proves none of it. The
official checker still needs a corresponding exact-module domain binding. -/
def Obligation : Prop :=
  ∀ (A : Args) (m : Mem) (sh : Dim3 → Mem)
    (r : Tid → String → Val) (p : Tid → String → Bool) (nan : Tid → TState → Val),
    A.Pre m nan →
    Warp.Equivalent original edited (A.launch nan) (Warp.State.init r p m sh) A.outputBytes

/-- The first scope does not hide a padding assumption for scale storage. -/
theorem eager_scale_bound (A : Args) (cta lane : Nat)
    (hc : cta < A.tiles) (hl : lane < 64) :
    (cta*1024 + lane*16)/1024 < A.tiles := by
  have hlocal : lane*16 < 1024 := by omega
  have heq : (cta*1024 + lane*16)/1024 = cta := by omega
  rw [heq]; exact hc

#print axioms eager_scale_bound
end FP4Whole.FP32
