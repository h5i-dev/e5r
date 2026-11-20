import NoCompiler.Step

/-
An executable run of the deterministic semantics, for the differential test
against qemu-riscv64 (crates/nocompiler/tests/semantics.rs). Not used by proofs.
-/
namespace NoCompiler

/-- Execute from `s` until the next ECALL (returned, not executed), a fault
    (`none`), or `fuel` instructions. -/
def runToEcall (c : Code) : Nat → State → Option State
  | 0, _ => none
  | n + 1, s =>
    match c.instr s.pc with
    | some .ecall => some s
    | some i => (exec i s).bind (runToEcall c n)
    | none => none

/-- Memory holding `bytes` from `base` and zero elsewhere. -/
def memOf (base : Word) (bytes : ByteArray) : Word → Byte := fun a =>
  let o := (a - base).toNat
  if o < bytes.size then BitVec.ofNat 8 (bytes.get! o).toNat else 0

def hexBytes (bs : List Byte) : String :=
  String.join (bs.map fun b =>
    let n := b.toNat
    let d := fun k => if k < 10 then Char.ofNat (48 + k) else Char.ofNat (87 + k)
    String.ofList [d (n / 16), d (n % 16)])

end NoCompiler
