import Examples.Chunks.SumB
import NoCompiler.Auto

/-! Demo/Sum2B.lean on the chunk image (see Examples/Chunks/SumB.lean). -/
namespace Examples.Chunks.Sum
open NoCompiler Demo.Sum Examples.Chunks.SumBImage

/-- `sum2` as `nocompiler cc -O2` compiled it (examples/demo/elf/sum.b.elf): two calls to `sum`,
    a 32-byte frame. -/
theorem sum2_b : VerifiedImg code sum2_dom sum2_entry spec2 := by
  rintro ⟨a, xs, b, ys⟩ s he ⟨ha0, ha1, ha2, ha3, hl1, hl2, hal1, hal2, harr1, harr2, hd1, hd2⟩
  nocompiler_auto sum2_func s he calls [sum_b]
  case entry_ret_x50 => exact BitVec.add_comm _ _

end Examples.Chunks.Sum
