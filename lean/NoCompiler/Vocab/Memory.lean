import NoCompiler.Vocab.Word

/-
Spec vocabulary: memory, regions and frames.

The predicates a specification states about memory are the core's:
`arr64 m a xs` (words), `readBytes m a n = xs` (bytes), `Region`,
`Region.Disjoint`, `Region.within`, and `writtenTo` for the trace
(NoCompiler/Trace.lean). What is here is the lemmas that use them:

* a buffer, or an array, survives a change of memory outside it (framing);
* disjointness, pointwise;
* a function's permission: what its own regions and its stack let it read
  and write, and that a function with no writes and no stack writes nothing
  (the frame of a call to it);
* the stack frame below the entry `sp`: its slots, and a callee's stack
  inside the caller's.
-/
namespace NoCompiler.Vocab
open NoCompiler

/-! ## Framing -/

/-- A byte buffer survives any change to memory outside it. -/
theorem readBytes_frame {m m' : Word → Byte} {a : Word} {n : Nat} (hn : n < 2 ^ 64)
    (h : ∀ x, (⟨a, n⟩ : Region).mem x → m' x = m x) : readBytes m' a n = readBytes m a n := by
  apply readBytes_congr
  intro k hk
  apply h
  show (_ - a).toNat < n
  rw [add_ofNat_sub_toNat a (by omega)]; exact hk

/-- `Region.Disjoint` as the pointwise statement specs about callers use. -/
theorem _root_.NoCompiler.Region.Disjoint.not_mem {r r' : Region} (hd : r.Disjoint r') {x : Word} (hx : r.mem x) :
    ¬ r'.mem x := by
  unfold Region.Disjoint at hd; unfold Region.mem at *
  intro hx'
  have e : (x - r.base).toNat + (r.base - r'.base).toNat = (x - r'.base).toNat ∨
      (x - r.base).toNat + (r.base - r'.base).toNat = (x - r'.base).toNat + 2 ^ 64 := by
    rw [BitVec.toNat_sub, BitVec.toNat_sub, BitVec.toNat_sub]
    have := BitVec.isLt x; have := BitVec.isLt r.base; have := BitVec.isLt r'.base
    omega
  have e2 : (r'.base - r.base).toNat + (r.base - r'.base).toNat = 0 ∨
      (r'.base - r.base).toNat + (r.base - r'.base).toNat = 2 ^ 64 := by
    rw [BitVec.toNat_sub, BitVec.toNat_sub]
    have := BitVec.isLt r.base; have := BitVec.isLt r'.base
    omega
  have := BitVec.isLt (x - r.base); have := BitVec.isLt (x - r'.base)
  omega

/-! ## A function's permission -/

namespace Spec
variable {α : Type}

theorem canWrite_of_mem {sp : Spec α} {a : α} {s : State} {r : Region} {x : Word} {w : Nat}
    (hr : r ∈ sp.writes a s) (hc : r.covers x w) : (sp.perm a s).canWrite x w :=
  .inr ⟨r, by simp [NoCompiler.Spec.perm, hr], hc⟩

theorem canRead_of_mem {sp : Spec α} {a : α} {s : State} {r : Region} {x : Word} {w : Nat}
    (hr : r ∈ sp.reads a s) (hc : r.covers x w) : (sp.perm a s).canRead x w :=
  .inr ⟨r, by simp [NoCompiler.Spec.perm, hr], hc⟩

theorem canWrite_stack {sp : Spec α} {a : α} {s : State} {x : Word} {w : Nat}
    (hc : (NoCompiler.Spec.stackRegion s sp.stack).covers x w) : (sp.perm a s).canWrite x w :=
  .inr ⟨_, by simp [NoCompiler.Spec.perm], hc⟩

/-- A function that may write no region and no stack writes nothing: at a
    call to it, the caller's memory comes back unchanged. -/
theorem not_writable_of_nil {sp : Spec α} {a : α} {s : State} (hw : sp.writes a s = [])
    (hs : sp.stack = 0) (x : Word) : ¬ (sp.perm a s).writable x := by
  rintro ⟨r, hr, hm⟩
  simp only [NoCompiler.Spec.perm, hw, hs, List.nil_append, List.mem_singleton] at hr
  subst hr
  simp [Region.mem, NoCompiler.Spec.stackRegion] at hm

end Spec

/-! ## The stack frame -/

/-- A slot of `w` bytes at offset `off` of the frame `fb = sp - n`. -/
theorem stack_covers {s : State} {n off w : Nat} {fb : Word}
    (hF : s.reg Reg.sp - BitVec.ofNat 64 n = fb) (h : off + w ≤ n) (hn : n < 2 ^ 64) :
    (Spec.stackRegion s n).covers (fb + BitVec.ofNat 64 off) w := by
  unfold Region.covers Spec.stackRegion
  simp only [hF]
  rw [add_ofNat_sub_toNat fb (by omega)]; omega

/-- A callee entered with `sp = fb`, the caller's `sp - n`, using `k` bytes
    of stack, stays inside the caller's `N ≥ n + k` bytes. -/
theorem stack_within {s t : State} {n k N : Nat} {fb : Word}
    (hF : s.reg Reg.sp - BitVec.ofNat 64 n = fb) (ht : t.reg Reg.sp = fb) (h : n + k ≤ N)
    (hN : N < 2 ^ 64) : (Spec.stackRegion t k).within (Spec.stackRegion s N) := by
  unfold Region.within Spec.stackRegion
  simp only [ht]
  rw [← hF]
  have e : s.reg Reg.sp - BitVec.ofNat 64 n - BitVec.ofNat 64 k -
      (s.reg Reg.sp - BitVec.ofNat 64 N) = BitVec.ofNat 64 (N - (n + k)) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
    have := BitVec.isLt (s.reg Reg.sp)
    rw [Nat.mod_eq_of_lt (a := n) (by omega), Nat.mod_eq_of_lt (a := k) (by omega),
      Nat.mod_eq_of_lt (a := N) (by omega), Nat.mod_eq_of_lt (a := N - (n + k)) (by omega)]
    omega
  rw [e, toNat_ofNat_of_lt (by omega)]; omega

end NoCompiler.Vocab
