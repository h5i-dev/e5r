import Examples.Sum
import Examples.Link.One
import Examples.Link.Two
import NoCompiler.Relocate

/-
Criterion 3 of docs/isa/v1.md: the same object, linked two ways
(examples/link/build.sh), and one proof for both.

`sum_relocatable` says `sum` meets its specification wherever the module is
linked. It is not a new proof of `sum`: it is `Examples.Sum.sum_verified`, the
proof about examples/elf/sum.elf, carried to every layout by
`Verified.of_leaf` (NoCompiler/Relocate.lean), because `sum` has no
relocations and none of its instructions sees where it is. The two
instances below are the same theorem at the two layouts; nocompiler-audit
checks that the module linked at each is that binary's `.text` and data.

`sum2` and `_start` call `sum`: their words differ between the layouts
(the call distance), and relocating their proofs needs the call lemmas at a
symbolic layout (T1). Not done here.
-/
namespace Examples.Link
open NoCompiler

/-- The two binaries are made from one object. -/
theorem same_module : One.module = Two.module := by decide +kernel

/-- `sum` as the module has it. -/
def sumF : RFunc where
  name := "sum"
  words := [0x00000613#32, 0x00058c63#32, 0x00053683#32, 0x00c68633#32, 0xfff58593#32, 0x00850513#32,
    0xfe0598e3#32, 0x00060513#32, 0x00008067#32]

theorem sumF_mem : sumF ∈ One.module.funcs := by decide

/-- `sum`'s specification looks at a0, a1 and memory only: not at the pc or ra. -/
theorem spec_shiftInv : Examples.Sum.spec.ShiftInv where
  pre := by
    rintro ⟨a, xs⟩ s δ
    simp only [Examples.Sum.spec, State.shift_mem, State.shift_reg _ _ (by decide : (10 : Reg) ≠ 1),
      State.shift_reg _ _ (by decide : (11 : Reg) ≠ 1)]
  post := by
    rintro ⟨a, xs⟩ s t δ
    simp only [Examples.Sum.spec, State.shift_reg _ _ (by decide : (10 : Reg) ≠ 1)]
  onExit := fun _ _ _ _ => Iff.rfl
  reads := fun _ _ _ => rfl
  writes := fun _ _ _ => rfl

theorem sumF_free : ∀ w ∈ sumF.words, (decode w).all Instr.pcFree = true :=
  List.all_eq_true.1 (by rfl : sumF.words.all (fun w => (decode w).all Instr.pcFree) = true)

theorem sumF_words : ∀ i, i < sumF.words.length →
    Examples.Sum.Image.code.fetch (Examples.Sum.Image.sum_entry + BitVec.ofNat 64 (4 * i)) =
      some (sumF.words.getD i 0) := by decide +kernel

theorem sum_verified' : VerifiedImg Examples.Sum.Image.code
    [(Examples.Sum.Image.sum_entry, 4 * sumF.words.length)] Examples.Sum.Image.sum_entry Examples.Sum.spec := by
  have : [(Examples.Sum.Image.sum_entry, 4 * sumF.words.length)] = Examples.Sum.Image.sum_dom := by decide
  rw [this]; exact Examples.Sum.sum_verified

/-- `sum` is verified at every layout of the module. -/
theorem sum_relocatable : Verified One.module "sum" (fun _ => Examples.Sum.spec) :=
  Verified.of_leaf (f := sumF) sumF_mem rfl sumF_free (c₀ := Examples.Sum.Image.code)
    (e₀ := Examples.Sum.Image.sum_entry) (by decide) (by decide) sumF_words (by decide)
    spec_shiftInv sum_verified'

/-- At the layout of examples/elf/sum.link1.elf. -/
theorem sum_link1 : VerifiedImg (One.module.link One.layout) (One.module.dom One.layout "sum")
    (One.layout.addr "sum") Examples.Sum.spec :=
  sum_relocatable.img (by decide +kernel)

/-- At the layout of examples/elf/sum.link2.elf: the same theorem. -/
theorem sum_link2 : VerifiedImg (Two.module.link Two.layout) (Two.module.dom Two.layout "sum")
    (Two.layout.addr "sum") Examples.Sum.spec :=
  same_module ▸ sum_relocatable.img (by decide +kernel)

/-- T6: linked with anything else, `sum` keeps its theorem. -/
theorem sum_in_any_program (M' : Module) :
    Verified (One.module ++ M') "sum" (fun _ => Examples.Sum.spec) :=
  sum_relocatable.mono

end Examples.Link
