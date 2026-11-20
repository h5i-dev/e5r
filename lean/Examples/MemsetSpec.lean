import NoCompiler.Vocab

/-
The specification of `void *memset(void *p, int c, u64 n)`, shared by the
proof about the hand-written structured-assembly build
(Examples/Memset.lean, from examples/asm/memset.s) and the one about the
clang build (Examples/MemsetCc.lean, from examples/asm/memset.c).
-/
namespace Examples.Memset
open NoCompiler

structure Args where
  p : Word
  c : Word
  n : Nat

/-- a0 = p, a1 = c, a2 = n: afterwards the `n` bytes at `p` are all `c`'s low
    byte, and a0 = p. It writes those bytes and nothing else, and uses no
    stack. -/
def spec : Spec Args where
  pre := fun ⟨p, c, n⟩ s =>
    s.reg Reg.a0 = p ∧ s.reg Reg.a1 = c ∧ s.reg Reg.a2 = BitVec.ofNat 64 n ∧ n < 2 ^ 64
  post := fun ⟨p, c, n⟩ _ s' =>
    s'.reg Reg.a0 = p ∧ readBytes s'.mem p n = List.replicate n (BitVec.ofNat 8 c.toNat)
  writes := fun ⟨p, _, n⟩ _ => [⟨p, n⟩]

/-! ## Facts the proofs use -/

/-- One more byte of the fill. -/
theorem fill_succ {L : List Byte} {k n : Nat} (b : Byte) (hk : k < n) (hl : L.length = n)
    (h : L.take k = List.replicate k b) : (L.set k b).take (k + 1) = List.replicate (k + 1) b := by
  rw [Vocab.take_set_succ _ _ _ (by omega), h, List.replicate_succ']

/-- The last byte of the fill. -/
theorem fill_last {L : List Byte} {k n : Nat} (b : Byte) (hk : k + 1 = n) (hl : L.length = n)
    (h : L.take k = List.replicate k b) : L.set k b = List.replicate n b := by
  have := fill_succ b (by omega) hl h
  rwa [hk, List.take_of_length_le (by simp; omega)] at this

end Examples.Memset
