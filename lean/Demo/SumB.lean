import Demo.SumSpec
import Demo.Sum.ImageB

namespace Demo.Sum
open E5R Demo.Sum.ImageB

/-- `sum` as `e5r cc -O2` compiled it (demo/elf/sum.b.elf), from its block/loop tree. -/
theorem sum_b : Verified code sum_dom sum_entry spec := by
  rintro ⟨a, xs⟩ s he ⟨ha0, ha1, hlen, hal, harr⟩
  e5r_auto sum_func s he
    loop_inv 0x11198 (fun u => ∃ m, u.reg 11 = BitVec.ofNat 64 m ∧ 0 < m ∧ m ≤ xs.length ∧
        u.reg 10 = a + BitVec.ofNat 64 (8 * (xs.length - m)) ∧
        u.reg 12 = sumW (xs.take (xs.length - m)) ∧ u.mem = s.mem)
      measure (fun u => (u.reg 11).toNat)
  case entry_ret_0x111b0 => exact (sumW_nil xs hb).symm
  case entry_to_0x11198 => rfl
  case «0x11198_to_0x11198» => rw [sumW_step xs m (by omega) (by omega)]; exact BitVec.add_comm _ _
  case «0x11198_ret_0x111b0» =>
    rw [sumW_last xs m (by omega) (by omega)]; exact BitVec.add_comm _ _
