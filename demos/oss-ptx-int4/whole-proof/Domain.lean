/- Address-domain obligations from the unchanged emitted FP4 entry.
These do not execute or replace the kernel. They make the eager scale load
precondition explicit before whole-kernel safety can be claimed. -/
import Ptx.Semantics.Memory

namespace FP4Domain

/-- Host grid in the pinned ops.cu dispatch. -/
def ctas (n : Nat) : Nat := (n + 1023) / 1024
/-- Quantizer's logical absmax tensor length. -/
def scales (n blocksize : Nat) : Nat := (n + blocksize - 1) / blocksize
/-- r297=512*ctaid; r293=8*tid; r47=r297+r293; r48=r47>>log2(blocksize/2).
For the public power-of-two sizes this is the corresponding division. -/
def eagerScale (blocksize cta tid : Nat) : Nat := (512*cta + 8*tid) / (blocksize / 2)

/-- Large public block sizes cover all eager scale reads even for arbitrary
positive tails, using exactly the logical absmax allocation. -/
theorem large_blocks_cover (n blocksize cta tid : Nat) (hn : 0 < n)
    (hb : blocksize = 1024 ∨ blocksize = 2048 ∨ blocksize = 4096)
    (hc : cta < ctas n) (ht : tid < 64) :
    eagerScale blocksize cta tid < scales n blocksize := by
  rcases hb with rfl | rfl | rfl <;>
    simp only [eagerScale, scales, ctas] at * <;> omega

/-- At smaller public block sizes, a full 1024-output tail tile also suffices.
No tensor allocator padding is assumed by this fact. -/
theorem full_tiles_cover (tiles blocksize cta tid : Nat)
    (hb : blocksize = 32 ∨ blocksize = 64 ∨ blocksize = 128 ∨ blocksize = 256 ∨ blocksize = 512)
    (hc : cta < tiles) (ht : tid < 64) :
    eagerScale blocksize cta tid < scales (1024*tiles) blocksize := by
  rcases hb with rfl | rfl | rfl | rfl | rfl <;>
    simp only [eagerScale, scales] <;> omega

/-- A valid small public shape does not by itself establish eager-load safety.
Actual backing allocations can be larger, but that must be a stated premise. -/
theorem small_tail_requires_coverage :
    ctas 1 = 1 ∧ scales 1 32 = 1 ∧ eagerScale 32 0 2 = 1 := by decide

theorem logical_scale_region_excludes_read :
    Ptx.accessOk [⟨0x2000, 4⟩] 0x2004 .b4 = false := by decide

#print axioms large_blocks_cover
#print axioms full_tiles_cover
#print axioms small_tail_requires_coverage
end FP4Domain
