import Crosscheck
import Lean
open Lean Elab Command

elab "#audit_crosscheck" : command => do
  let env ← getEnv
  let allowed := [``propext, ``Quot.sound, ``Classical.choice]
  let mut checked : Nat := 0
  let mut upstreamChecked : Nat := 0
  let mut upstreamRejected : Array Name := #[]
  for (n, ci) in env.constants.map₁.toList do
    let some idx := env.getModuleIdxFor? n | continue
    let mod := env.header.moduleNames[idx.toNat]!
    let own := mod.getRoot ∈ [`Ptx, `Crosscheck]
    unless own || mod.getRoot == `Fp do continue
    let axioms ← liftCoreM (collectAxioms n)
    let bad := axioms.filter (fun a => !allowed.contains a)
    if own then
      if let .axiomInfo _ := ci then throwError "{n} is an axiom in {mod}"
      unless bad.isEmpty do throwError "{n} ({mod}) depends on {bad}"
      checked := checked + 1
    else
      upstreamChecked := upstreamChecked + 1
      unless bad.isEmpty do upstreamRejected := upstreamRejected.push n
  logInfo m!"accepted: {checked} Ptx/Crosscheck declarations, standard axioms only"
  logInfo m!"upstream inventory: {upstreamChecked} declarations, {upstreamRejected.size} with nonstandard dependencies (NOT accepted)"
  for n in upstreamRejected do
    logInfo m!"excluded {n}: {← liftCoreM (collectAxioms n)}"
  for n in [``PackedFloat.add, ``PackedFloat.sub, ``PackedFloat.mul,
      ``PackedFloat.div, ``PackedFloat.fma, ``sqrt] do
    let axioms ← liftCoreM (collectAxioms n)
    logInfo m!"used arithmetic definition {n}: {axioms}"
    for a in axioms do
      unless allowed.contains a do throwError "used definition {n} depends on {a}"

#audit_crosscheck
#print axioms Crosscheck.observe_equiv
#print axioms Crosscheck.observe_neg_neg
#print axioms Crosscheck.production_add_nan
#print axioms Crosscheck.f32_subnormal_add
#print axioms Crosscheck.f64_subnormal_add
#print axioms Crosscheck.f32_tie_even
#print axioms Crosscheck.f64_tie_even
#print axioms Crosscheck.f32_fma_cancellation
#print axioms Crosscheck.f32_signed_zero_add
#print axioms Crosscheck.f64_signed_zero_add
