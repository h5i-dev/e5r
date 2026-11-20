import Demo.SumA
import NoCompiler.Auto

namespace Demo.Sum
open NoCompiler Demo.Sum.ImageA

/-- `sum2` and the function it calls: its code region, as `nocompiler export` writes it for
    the nocompiler build (the ordinary build has no metadata to compute it from). -/
def sum2_domA : Dom := [(sum_entry, sum_size), (sum2_entry, sum2_size)]

/-- `sum2` as plain clang -O2 -march=rv64gc compiled it (examples/demo/elf/sum.a.elf): two
    calls to `sum`, a 32-byte frame, compressed code. -/
theorem sum2_a : VerifiedC code sum2_domA sum2_entry spec2 := by
  rintro ⟨a, xs, b, ys⟩ s he ⟨ha0, ha1, ha2, ha3, hl1, hl2, hal1, hal2, harr1, harr2, hd1, hd2⟩
  nocompiler_auto_c sum2_entry sum2_size s he calls [sum_a]
  case entry_ret_x28 => exact BitVec.add_comm _ _

end Demo.Sum
