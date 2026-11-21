import Examples.Link
import Examples.Link.OneChunks
import Examples.Link.TwoChunks

/-
Modules in chunks (lean/NoCompiler/ModuleChunks.lean) on the two links of
examples/link: the chunk modules are the modules (`Module.ofChunks` decodes
them to `One.module` and `Two.module`, decided by the kernel), and `sum`'s
theorem carries from the first link's module to the second's by comparing
numbers (`Verified.of_chunks`). The 87,242-instruction measurement uses the
same definitions (docs/isa/ledger.md).
-/
namespace Examples.LinkChunks
open NoCompiler Examples.Link

/-- The chunks decode to the module of sum.link1.elf. -/
theorem one_eq : OneChunks.module = One.module := by decide +kernel

/-- And of sum.link2.elf. -/
theorem two_eq : TwoChunks.module = Two.module := by decide +kernel

theorem sum_one : Verified (Module.ofChunks OneChunks.funcs OneChunks.datas) "sum"
    (fun _ => Examples.Sum.spec) := by
  have h := sum_relocatable
  rw [← one_eq] at h
  exact h

/-- `sum`'s theorem at every layout of the second link's module: the side
    condition compares the first module's chunks with the second's. -/
theorem sum_two : Verified (Module.ofChunks TwoChunks.groups.flatten TwoChunks.datas) "sum"
    (fun _ => Examples.Sum.spec) :=
  Verified.of_groups (ks := [(1, 0), (0, 0), (0, 0)]) (by decide +kernel) sum_one

/-- The same with the flat check (`RChunk.subSeq`). -/
theorem sum_two' : Verified (Module.ofChunks TwoChunks.funcs TwoChunks.datas) "sum"
    (fun _ => Examples.Sum.spec) :=
  Verified.of_chunks (ks := [0, 0, 0]) (by decide +kernel) sum_one

/-- At sum.link1.elf's layout, `sum` in the second link's module image
    refines `sum` in the first's. -/
theorem sum_refines : Refines Examples.Sum.spec
    ((Module.ofChunks OneChunks.funcs OneChunks.datas).link One.layout)
    ((Module.ofChunks OneChunks.funcs OneChunks.datas).dom One.layout "sum") (One.layout.addr "sum")
    ((Module.ofChunks TwoChunks.funcs TwoChunks.datas).link One.layout)
    ((Module.ofChunks OneChunks.funcs OneChunks.datas).dom One.layout "sum") (One.layout.addr "sum") :=
  Refines.of_chunks (sp := fun _ => Examples.Sum.spec) (ka := [0, 0, 0]) (kb := [0, 0, 0])
    (by rw [show Module.ofChunks OneChunks.funcs OneChunks.datas = One.module from one_eq]; decide +kernel)
    (by rw [show Module.ofChunks TwoChunks.funcs TwoChunks.datas = Two.module from two_eq]
        decide +kernel)
    (by decide +kernel) (by decide +kernel) sum_one

/-- The second link's functions in the other order: `sum2`, `sum`, `_start`. -/
def revGroups : List (List RChunk) := [[TwoChunks.f_2, TwoChunks.f_1, TwoChunks.f_0]]

/-- `_start` calls `sum`, which now comes first: a theorem about `_start`'s
    closure module (here a hypothesis) still carries, the closure found in
    the new order (`of_groups_perm`). -/
theorem start_reordered {α : Type} {sp : Layout → Spec α}
    (h : Verified (Module.ofChunks [OneChunks.f_0, OneChunks.f_1] OneChunks.datas) "_start" sp) :
    Verified (Module.ofChunks revGroups.flatten TwoChunks.datas) "_start" sp :=
  Verified.of_groups_perm (fs' := [OneChunks.f_1, OneChunks.f_0]) (ks := [(1, 1), (0, 0)])
    (by decide +kernel) (by decide +kernel) h

/-- Control: in the old order, the closure is not a sublist of the new one. -/
theorem start_unordered_fails :
    RChunk.subSeqG [OneChunks.f_0, OneChunks.f_1] [(1, 2), (0, 0)] [] revGroups = false := by
  decide +kernel

/-- Control: one bit of `sum`'s words changed, and the check fails. -/
theorem changed_fails :
    RChunk.subSeqG [{ OneChunks.f_1 with bits := OneChunks.f_1.bits ^^^ 1 }] [(1, 1)] [] TwoChunks.groups
      = false := by
  decide +kernel

/-- `sum` alone at its place in the groups: the check passes. -/
theorem sum_at : RChunk.subSeqG [OneChunks.f_1] [(1, 1)] [] TwoChunks.groups = true := by decide +kernel

/-- Control: at the wrong position (skipping none, so against `_start`). -/
theorem misplaced_fails : RChunk.subSeq [OneChunks.f_1] [0] TwoChunks.funcs = false := by
  decide +kernel

/-- A relocation with a negative addend, packed as `module::pack_relocs`
    packs it (crates/nocompiler/tests/module.rs checks the same number). -/
theorem reloc_negative :
    RChunk.reloc ⟨0, 0, 0, 1, 0x00000000000002400002000004000008, [0x41]⟩ 0 =
      { off := 8, kind := .pcrelLoI, sym := "A", addend := -5, hiOff := 4 } := by
  decide +kernel

end Examples.LinkChunks
