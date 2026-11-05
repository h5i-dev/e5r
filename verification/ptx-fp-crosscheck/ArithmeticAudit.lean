import Fp.Theorems.Addition
import Fp.Theorems.Subtraction
import Fp.Theorems.Multiplication
import Fp.Theorems.Division
import Fp.Theorems.FMA
import Fp.Theorems.Sqrt
import Fp.PackUnpackNormalize
import Crosscheck
import Symbolic
import SpecBridge
import Lean
open Lean Elab Command

elab "#audit_arithmetic" : command => do
  let allowed := [``propext, ``Quot.sound, ``Classical.choice]
  let accepted := [``Fp.add_eq_add, ``Fp.sub_eq_sub, ``Fp.mul_eq_mul,
    ``Fp.div_eq_div, ``Fp.fma_eq_fma, ``Fp.sqrt_eq_sqrt,
    ``Crosscheck.mul_intermediate_roundtrip, ``Crosscheck.mul_chain,
    ``Crosscheck.reference_eq_upstream, ``Crosscheck.f32_reference, ``Crosscheck.f64_reference,
    ``Crosscheck.agrees_iff_reference]
  for n in accepted do
    let axioms ← liftCoreM (collectAxioms n)
    logInfo m!"{n}: {axioms}"
    for a in axioms do
      unless allowed.contains a do throwError "unaccepted axiom {a} in {n}"
  let n := ``EUnpackedFloat.pack_unpack
  let axioms ← liftCoreM (collectAxioms n)
  logInfo m!"REJECTED normalization theorem {n}: {axioms}"
  unless axioms.any (fun a => !allowed.contains a) do
    throwError "expected the pinned normalization theorem to have an extra axiom"

#audit_arithmetic
