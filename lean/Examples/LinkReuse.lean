import Examples.Link
import NoCompiler.RefineReuse

/-
Reuse of unchanged code (docs/isa/ledger.md, `Verified.of_sub`): `sum`'s
theorem about the module of examples/elf/sum.link1.elf carries to another
module that holds `sum` unchanged, with the functions in another order and
another function added, so `sum` sits elsewhere at every layout. This is not
`M ++ M'`, so `Verified.mono` does not apply. The side conditions are decided
by comparing `RFunc`s.
-/
namespace Examples.LinkReuse
open NoCompiler Examples.Link

def extra : RFunc where
  name := "extra"
  words := [0x00000513#32, 0x00008067#32]   -- li a0, 0; ret

/-- The module's functions reversed, with `extra` in front. -/
def module' : Module where
  funcs := extra :: One.module.funcs.reverse

theorem sum_reused : Verified module' "sum" (fun _ => Examples.Sum.spec) :=
  Verified.of_sub (by decide) (by decide) sum_relocatable

/-- The same functions in the other order. -/
def moduleRev : Module where
  funcs := One.module.funcs.reverse

/-- At sum.link1.elf's layout, `sum` in `moduleRev`'s image refines `sum` in
    the module's own image: decided by comparing `RFunc`s and checking the
    layout, with A's run from `sum_relocatable`. -/
theorem sum_refines_rev : Refines Examples.Sum.spec (One.module.link One.layout)
    (One.module.dom One.layout "sum") (One.layout.addr "sum")
    (moduleRev.link One.layout) (One.module.dom One.layout "sum") (One.layout.addr "sum") :=
  Refines.of_sub_verified (sp := fun _ => Examples.Sum.spec) (by decide +kernel) (by decide +kernel)
    (fun _ h => h) (by decide) (by decide) sum_relocatable

/-- Control: with one word of `sum` changed, the side condition fails. -/
example : ¬ ∀ g ∈ One.module.funcs,
    g ∈ ({ funcs := One.module.funcs.map fun f =>
      if f.name = "sum" then { f with words := f.words.set 0 0x00000013#32 } else f } : Module).funcs := by
  decide

end Examples.LinkReuse
