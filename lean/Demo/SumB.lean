import Demo.SumSpec
import Demo.Sum.ImageB

namespace Demo.Sum
open NoCompiler Demo.Sum.ImageB

/-- `sum` as `nocompiler cc -O2` compiled it (examples/demo/elf/sum.b.elf), from its block/loop tree. -/
theorem sum_b : VerifiedImg code sum_dom sum_entry spec := by
  rintro ⟨a, xs⟩ s he ⟨ha0, ha1, hlen, hal, harr⟩
  nocompiler_auto sum_func s he
    loop_inv $l1 (fun u => ∃ m, u.reg 11 = BitVec.ofNat 64 m ∧ 0 < m ∧ m ≤ xs.length ∧
        u.reg 10 = a + BitVec.ofNat 64 (8 * (xs.length - m)) ∧
        u.reg 12 = sumW (xs.take (xs.length - m)) ∧ u.mem = s.mem)
      measure (fun u => (u.reg 11).toNat)
  case entry_ret_x20 => exact (sumW_nil xs (by omega)).symm
  case entry_to_l1 => rfl
  case l1_to_l1 => rw [sumW_step xs m (by omega) (by omega)]; exact BitVec.add_comm _ _
  case l1_ret_x20 =>
    rw [sumW_last xs m (by omega) (by omega)]; exact BitVec.add_comm _ _
