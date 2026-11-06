/-
Narrow `or.pred` frontend extension: the four Boolean cases execute through
`action`/`stepMem` and `ret` in the Lean kernel. NVIDIA PTX ISA 9.2 §9.7.8.2
specifies `d = a | b`, including predicate registers.
-/
import Ptx.Semantics.Instruction

namespace Ptx.Examples.PredicateOr
open Ptx

private def K (guard : Option Guard := none) (dst : String := "%p0") : Kernel where
  name := "predicate_or"
  params := []
  regs := [⟨.pred, "%p", some 4⟩]
  body := [⟨guard, .por dst "%p1" "%p2"⟩, ⟨none, .ret⟩]
  labels := []

private def ctx : Ctx where
  tid := ⟨0, 0, 0⟩
  ntid := ⟨1, 1, 1⟩
  ctaid := ⟨0, 0, 0⟩
  nctaid := ⟨1, 1, 1⟩
  params := fun _ => 0

private def initial (a b : Bool) : TState where
  pc := 0
  r := fun _ => 123
  p := fun n => if n = "%p1" then a else if n = "%p2" then b else n == "%p3"

private def run (a b : Bool) (guard : Option Guard := none) (dst : String := "%p0") :
    Option (Bool × Nat × Val × Bool) :=
  match stepMem (K guard dst) [] ctx (initial a b) (fun _ => 42) with
  | .ok s m =>
    match stepMem (K guard dst) [] ctx s m with
    | .halted => some (s.p dst, s.pc, s.r "%r0", s.p "%p3")
    | _ => none
  | _ => none

/-- All four input combinations reach `ret` with the expected result, exactly
one PC advance, unchanged data register, and unchanged other predicate. -/
theorem truth_table :
    run false false = some (false, 1, 123, true) ∧
    run false true = some (true, 1, 123, true) ∧
    run true false = some (true, 1, 123, true) ∧
    run true true = some (true, 1, 123, true) := by decide

theorem guarded_truth_table :
    run false false (some ⟨"%p3", false⟩) = some (false, 1, 123, true) ∧
    run false true (some ⟨"%p3", false⟩) = some (true, 1, 123, true) ∧
    run true false (some ⟨"%p3", false⟩) = some (true, 1, 123, true) ∧
    run true true (some ⟨"%p3", false⟩) = some (true, 1, 123, true) := by decide

theorem false_guard_skips :
    run true true (some ⟨"%p3", true⟩) = some (false, 1, 123, true) := by decide

theorem source_destination_alias :
    run false true none "%p1" = some (true, 1, 123, true) ∧
    run true false none "%p2" = some (true, 1, 123, true) := by decide

/-- Universal execution equation; all memory and data registers are framed. -/
theorem por_step (c : Ctx) (s : TState) (al : List Region) (m : Mem)
    (hpc : s.pc = 0) :
    stepMem (K none "%p0") al c s m =
      .ok (s.setp "%p0" (s.p "%p1" || s.p "%p2")) m := by
  simp [stepMem, action, K, hpc, guardHolds, exec]

#print axioms truth_table
#print axioms guarded_truth_table
#print axioms false_guard_skips
#print axioms source_destination_alias
#print axioms por_step
end Ptx.Examples.PredicateOr
