/-
Explicit by-value kernel parameters, following NVIDIA's public PTX ISA
kernel-function-parameters and addresses-as-operands specifications.
The scalar theorem preserves the old instruction equation for every launch.
-/
import Ptx.Semantics.SIMT

namespace Ptx.Examples.AggregateParam

def kernel : Kernel where
  name := "aggregate"
  params := [("n", .u32)]
  aggregateParams := [⟨"a", 8, 32⟩, ⟨"b", 8, 24⟩]
  paramOrder := [.aggregate 0, .scalar 0, .aggregate 1]
  regs := [⟨.b64, "%rd", some 3⟩, ⟨.b32, "%r", none⟩]
  body := [⟨none, .ld .param .u64 "%rd0" (.param "a" 24)⟩, ⟨none, .ret⟩]
  labels := []

def ctx : Ctx where
  tid := ⟨0, 0, 0⟩
  ntid := ⟨1, 1, 1⟩
  ctaid := ⟨0, 0, 0⟩
  nctaid := ⟨1, 1, 1⟩
  params := fun n => if n = "n" then 0xabcdef0123456789 else 0xffffffffffffffff
  byteParams := fun n i =>
    if n = "a" ∧ i < 32 then BitVec.ofNat 8 i
    else if n = "b" ∧ i < 24 then BitVec.ofNat 8 (64 + i)
    else if n = "n" ∧ i < 8 then 255 else 0

theorem scalar_exec_compatible (K : Kernel) (c : Ctx) (s : TState) (t : Ty) (n d : String)
    (h : K.aggregateParams = []) :
    exec K c s (.ld .param t d (.param n 0)) =
      .next (s.set d (fit t (c.params n))) := by
  simp [exec, h]

theorem scalar_offset_fault (K : Kernel) (c : Ctx) (s : TState) (t : Ty)
    (n d : String) (off : Int) (h : K.aggregateParams = []) (hoff : off ≠ 0) :
    exec K c s (.ld .param t d (.param n off)) = .fault := by
  simp [exec, paramValue, h, hoff]

/-- A parameter load advances once, frames every memory byte, and performs
no global/shared memory action, for arbitrary ABI bytes and register state. -/
theorem aggregate_step (c : Ctx) (s : TState) (al : List Region) (m : Mem)
    (hpc : s.pc = 0) :
    stepMem kernel al c s m =
      .ok (s.set "%rd0" (paramRead (c.byteParams "a") 24 .b8)) m := by
  simp [stepMem, action, kernel, hpc, guardHolds, exec, paramValue, Ty.size, Ty.width]

theorem launch_bytes (L : Launch) (t : Tid) : (L.ctx t).byteParams = L.byteParams := rfl

theorem concrete_bytes :
    paramValue kernel ctx .u64 "a" 0 = some 0x0706050403020100 ∧
    paramValue kernel ctx .u64 "a" 24 = some 0x1f1e1d1c1b1a1918 ∧
    paramValue kernel ctx .u64 "b" 16 = some 0x5756555453525150 ∧
    paramValue kernel ctx .u32 "n" 0 = some 0x23456789 := by decide

theorem rejected_bounds :
    paramValue kernel ctx .u64 "a" (-8) = none ∧
    paramValue kernel ctx .u64 "a" 1 = none ∧
    paramValue kernel ctx .u64 "a" 28 = none ∧
    paramValue kernel ctx .u64 "a" 32 = none ∧
    paramValue kernel ctx .u32 "n" 4 = none := by decide

#print axioms scalar_exec_compatible
#print axioms scalar_offset_fault
#print axioms aggregate_step
#print axioms launch_bytes
#print axioms concrete_bytes
#print axioms rejected_bounds

end Ptx.Examples.AggregateParam
