import Demo.SumSpec
import Demo.Sum.ImageA

namespace Demo.Sum
open NoCompiler Demo.Sum.ImageA

/-- `sum` as plain clang -O2 -march=rv64gc compiled it (examples/demo/elf/sum.a.elf). -/
theorem sum_a : VerifiedC code sum_dom sum_entry spec := by
  rintro ⟨a, xs⟩ s he ⟨ha0, ha1, hlen, hal, harr⟩
  nocompiler_auto_c sum_entry sum_size s he
    loop_inv 0x11194 (fun u => ∃ m, u.reg 11 = BitVec.ofNat 64 m ∧ 0 < m ∧ m ≤ xs.length ∧
        u.reg 10 = a + BitVec.ofNat 64 (8 * (xs.length - m)) ∧
        u.reg 12 = sumW (xs.take (xs.length - m)) ∧ u.mem = s.mem)
      measure (fun u => (u.reg 11).toNat)
  case entry_ret_x10 => exact (sumW_nil xs (by omega)).symm
  case entry_to_x4 => rfl
  case x4_to_x4 => rw [sumW_step xs m (by omega) (by omega)]
  case x4_ret_x10 =>
    rw [sumW_last xs m (by omega) (by omega)]
