import Examples.Sum
import Examples.Link.Img2
import NoCompiler.RefineLockstep

/-
Refinement, first example (docs/isa/refine.md): `sum` as linked in
examples/elf/sum.link2.elf refines `sum` in examples/elf/sum.elf. The two
are the same instructions at different addresses, so a lockstep
certificate proves it, checked by the kernel; every register is live (the
instructions are identical, so liveness is not needed).

B's code is the `nocompiler export` of examples/elf/sum.link2.elf
(Examples/Link/Img2.lean, audited against the ELF). Then `Refines.verified`
carries `sum`'s proof over: a second, independent route to what
`Examples.Link.sum_link2` proves by translation, for the callers whose
return address is outside A's code.
-/
namespace Examples.Refine.Relink
open NoCompiler NoCompiler.Lockstep

def cA : Code := Examples.Sum.Image.code
def DA : Dom := Examples.Sum.Image.sum_dom
def eA : Word := Examples.Sum.Image.sum_entry
def cB : Code := Examples.Link.Img2.code
def DB : Dom := Examples.Link.Img2.sum_dom
def eB : Word := Examples.Link.Img2.sum_entry

abbrev allRegs : List Reg :=
  [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28,
    29, 30, 31]

/-- Pair i: B's i-th instruction with A's. -/
def cert : Cert := ⟨(List.range 9).map fun i =>
  ⟨eB + BitVec.ofNat 64 (4 * i), eA + BitVec.ofNat 64 (4 * i), allRegs⟩, []⟩

theorem cert_ok : check cA cB DA DB eA eB cert = true := by decide +kernel

/-- A runs: `sum` is verified (decision 2026-11-21 (3): a refinement carries this). -/
theorem sum_runs : ARuns Examples.Sum.spec cA DA eA := ARuns.of_verified Examples.Sum.sum_verified

theorem sum_link2_refines : Refines Examples.Sum.spec cA DA eA cB DB eB :=
  Refines.of_lockstep (k := cert) sum_runs cert_ok

theorem spec_pcFree : Examples.Sum.spec.PcFree where
  pre := fun _ _ _ => Iff.rfl
  post := fun _ _ _ _ => Iff.rfl
  onExit := fun _ _ _ _ => Iff.rfl
  reads := fun _ _ _ => rfl
  writes := fun _ _ _ => rfl

/-- `sum`'s postcondition sees only what a caller observes. -/
theorem spec_obsInv : Examples.Sum.spec.ObsInv := by
  rintro ⟨a, xs⟩ s ta tb ⟨_, hx, ho⟩ hd
  rcases hd with ⟨hxa, hpc, hpres, hpost⟩ | ⟨hxa, hex⟩
  · obtain ⟨hp, hr, _⟩ := ho hxa
    have hreg : ∀ r ∈ retRegs ++ preservedRegs, tb.reg r = ta.reg r := fun r h => (hr r h).symm
    refine .inl ⟨hx ▸ hxa, hp ▸ hpc, fun r h => ?_, ?_⟩
    · rw [hreg r (List.mem_append_right _ h)]; exact hpres r h
    · show tb.reg Reg.a0 = _
      rw [hreg 10 (by simp [retRegs])]; exact hpost
  · exact .inr ⟨hx ▸ hxa, hex⟩

/-- `sum` at the layout of examples/elf/sum.link2.elf, from its proof at
    examples/elf/sum.elf, through refinement: for callers whose return address
    is not in A's code `[0x11190, 0x111b4)` (`Spec.avoid`). -/
theorem sum_link2' : VerifiedImg cB DB eB (Examples.Sum.spec.avoid DA) :=
  sum_link2_refines.verified Examples.Sum.sum_verified spec_pcFree spec_obsInv

/-! ## Negative controls: B with one word changed is rejected by the check. -/

/-- B with the word at `sum + 4 * i` replaced. -/
def mutB (i : Nat) (w : BitVec 32) : Code :=
  ⟨cB.base, cB.words.set! ((eB - cB.base).toNat / 4 + i) w⟩

-- add a2, a3, a2 becomes sub
example : check cA (mutB 3 0x40c68633#32) DA DB eA eB cert = false := by decide +kernel
-- ld a3, 0(a0) becomes lw
example : check cA (mutB 2 0x00052683#32) DA DB eA eB cert = false := by decide +kernel
-- bne a1, zero, loop becomes beq
example : check cA (mutB 6 0xfe0588e3#32) DA DB eA eB cert = false := by decide +kernel
-- the stride 8 becomes 4
example : check cA (mutB 5 0x00450513#32) DA DB eA eB cert = false := by decide +kernel
-- the unmutated B passes (the controls are about the mutation)
example : check cA (mutB 3 0x00c68633#32) DA DB eA eB cert = true := by decide +kernel

end Examples.Refine.Relink
