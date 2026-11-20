import Examples.Sum.Image

/-
Negative controls for the Lean checker of rules R4 to R6
(NoCompiler/Frame.lean; docs/isa/v1.md, criterion 6): the faults of
crates/nocompiler/tests/levels.rs, made in `sum2`'s words, against the frame
and certificate recorded for the unmutated code. Each must cost `sum2` level
L2, and the unmutated code must keep it. All by `decide`, so the kernel
evaluates the checker; nothing here trusts the Rust checker.
-/
namespace Examples.FrameControls
open NoCompiler Examples.Sum.Image

/-- `code` with the word at `pc` replaced. -/
def patch (pc : Word) (w : BitVec 32) : Code :=
  ⟨code.base, code.words.set! ((pc - code.base).toNat / 4) w⟩

def l2 (c : Code) : Bool := Struct.level c sum2_func entries sum2_frame sum2_cert == some .l2

-- The unmutated code.
example : l2 code = true := by decide
-- A restore removed: `ld s0, 16(sp)` at 0x111f4 becomes a nop.
example : l2 (patch 0x111f4#64 0x00000013#32) = false := by decide
-- A save slot written mid-function: `mv s2, a0` at 0x111d8 becomes `sd a0, 16(sp)`.
example : l2 (patch 0x111d8#64 0x00a13823#32) = false := by decide
-- A slot's address taken: `mv a0, s1` at 0x111dc becomes `addi a0, sp, 16`.
example : l2 (patch 0x111dc#64 0x01010513#32) = false := by decide
-- gp written: `mv s0, a3` at 0x111c8 becomes `addi gp, a3, 0`.
example : l2 (patch 0x111c8#64 0x00068193#32) = false := by decide
-- sp stored: `mv s2, a0` becomes `sd sp, 0(a0)`.
example : l2 (patch 0x111d8#64 0x00253023#32) = false := by decide
-- Past the entry sp: `ld ra, 24(sp)` at 0x111f0 becomes `ld ra, 40(sp)`.
example : l2 (patch 0x111f0#64 0x02813083#32) = false := by decide
-- The frame not given back: `addi sp, sp, 32` at 0x11200 becomes `addi sp, sp, 16`.
example : l2 (patch 0x11200#64 0x01010113#32) = false := by decide

end Examples.FrameControls
