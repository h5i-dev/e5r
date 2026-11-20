import Examples.MemsetCc.Image
import Examples.MemsetSpec

/- `memset` from examples/asm/memset.c as `nocompiler cc -O2` compiled it
   (examples/elf/memset_cc.elf), against the specification the hand-written
   build (Examples/Memset.lean) is proved against. The loop is clang's: the
   count is decremented first, the pointer advanced through a4. -/
namespace Examples.Memset
open NoCompiler NoCompiler.Vocab Examples.MemsetCc.Image

set_option maxHeartbeats 20000000 in
theorem memset_cc_verified : Verified code memset_dom memset_entry (spec) := by
  rintro ⟨p, c, n⟩ s he ⟨ha0, ha1, ha2, hn⟩
  nocompiler_auto memset_func s he
    loop_inv 0x11198 (fun u => ∃ k L, u.reg 13 = p + BitVec.ofNat 64 k ∧ u.reg 12 = BitVec.ofNat 64 (n - k) ∧
        k < n ∧ u.reg 10 = p ∧ u.reg 11 = c ∧ readBytes u.mem p n = L ∧
        L.take k = List.replicate k (BitVec.ofNat 8 c.toNat))
      measure (fun u => (u.reg 12).toNat)
  case entry_ret_0x111ac => rw [show n = 0 by omega]; rfl
  case entry_to_0x11198_0 => exact Nat.zero_mod _
  case entry_to_0x11198_1 => rw [Nat.sub_zero]
  case entry_to_0x11198_2 => omega
  case entry_to_0x11198_3 => rfl
  case «0x11198_to_0x11198» => exact fill_succ _ (by omega) (h6 ▸ Auto.readBytes_length _ _ _) h7
  case «0x11198_ret_0x111ac» => exact fill_last _ (by omega) (h6 ▸ Auto.readBytes_length _ _ _) h7
