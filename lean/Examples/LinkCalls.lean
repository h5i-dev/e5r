import Examples.Link
import Examples.Sum2
import Examples.Link.Img1
import Examples.Link.Img2

/-
Criterion 3 for a function with calls (docs/isa/v1-results.md): `sum2`,
which calls `sum` twice, in both links of examples/link.

What is proved, and what is not:

* `sum` at each link is `Examples.Link.sum_relocatable`, the one theorem over
  every layout, instantiated there (`sum_here`).
* `sum2` is proved at each link by the same proof text (the block between
  the PROOF markers, identical in both namespaces;
  crates/nocompiler/tests/module.rs checks it), elaborated against that
  link's image, with that link's `sum_here` as the callee. The proof names no
  address. This is the same proof re-checked per layout, not one theorem
  over every layout: that needs the call distance at a symbolic layout
  (docs/isa/v1-results.md, criterion 3).

The images are `nocompiler export`s of the two binaries; the audit checks
them against the ELF files, and `code_eq` against the module linked at the
binary's layout.
-/
open NoCompiler

namespace Examples.Link.L1
open Examples.Link.Img1 Examples.Sum2

theorem code_eq : code = One.module.link One.layout := by
  show (⟨_, _⟩ : Code) = ⟨_, _⟩; congr 1 <;> decide +kernel

theorem sum_here : VerifiedImg code sum_dom sum_entry Examples.Sum.spec := by
  have h := Examples.Link.sum_link1
  rw [← code_eq, show One.module.dom One.layout "sum" = sum_dom by decide +kernel,
    show One.layout.addr "sum" = sum_entry by decide +kernel] at h
  exact h

-- PROOF
theorem sum2_here : VerifiedImg code sum2_dom sum2_entry spec2 := by
  rintro ⟨a, xs, b, ys⟩ s he ⟨ha0, ha1, ha2, ha3, hl1, hl2, hal1, hal2, harr1, harr2, hd1, hd2⟩
  nocompiler_auto sum2_func s he calls [sum_here]
  all_goals exact BitVec.add_comm _ _
-- END PROOF

end Examples.Link.L1

namespace Examples.Link.L2
open Examples.Link.Img2 Examples.Sum2

theorem code_eq : code = Two.module.link Two.layout := by
  show (⟨_, _⟩ : Code) = ⟨_, _⟩; congr 1 <;> decide +kernel

theorem sum_here : VerifiedImg code sum_dom sum_entry Examples.Sum.spec := by
  have h := Examples.Link.sum_link2
  rw [← code_eq, show Two.module.dom Two.layout "sum" = sum_dom by decide +kernel,
    show Two.layout.addr "sum" = sum_entry by decide +kernel] at h
  exact h

-- PROOF
theorem sum2_here : VerifiedImg code sum2_dom sum2_entry spec2 := by
  rintro ⟨a, xs, b, ys⟩ s he ⟨ha0, ha1, ha2, ha3, hl1, hl2, hal1, hal2, harr1, harr2, hd1, hd2⟩
  nocompiler_auto sum2_func s he calls [sum_here]
  all_goals exact BitVec.add_comm _ _
-- END PROOF

end Examples.Link.L2
