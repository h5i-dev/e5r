/-
  The RMK qemu-riscv-rynk replay on QEMU virt (see tools/Replay.lean).

  Initial conditions, all explicit:
  * the image is `RamElf.imageOf` of the packed ELF (Projects/rmk/QemuRiscvRynk/Image.lean,
    written by tools/pack_elf.py); the board is `QemuVirtRv32.board rwBase`;
  * the replay starts at the first QEMU state at the ELF entry (QEMU's reset ROM at 0x1000 is
    not modeled), with QEMU's registers and CSRs there;
  * RAM starts as QEMU loads it: the writable PT_LOADs' file bytes, zero elsewhere;
  * the semihosting `ebreak`s listed below are QEMU's steps (memory-free operations only).
-/
import tools.Replay
import Theories.RamElf
import Theories.Board.QemuVirtRv32
import Projects.rmk.QemuRiscvRynk.Image
open E5R

def image : RamElf.Image := RamElf.imageOf QemuVirtRv32.dramBase 0x1000000 Rmk.QemuRiscvRynk.elf

/-- RAM as QEMU loads it: writable segments' file bytes, zero elsewhere. -/
def ram0 (a : Word) : BitVec 8 :=
  match image.rw.find? fun (base, bytes, _) => base ≤ a.toNat ∧ a.toNat < base + bytes.length with
  | some (base, bytes, _) => BitVec.ofNat 8 (bytes.getD (a.toNat - base) 0)
  | none => 0

def main (args : List String) : IO UInt32 := do
  let some path := args.head? | IO.eprintln "usage: replay_virt TRACE [SEMIHOST_PC...]"; return 2
  if !RamElf.accepts QemuVirtRv32.dramBase 0x1000000 Rmk.QemuRiscvRynk.elf then
    IO.eprintln "TRACE OR TOOL ERROR: the RAM-image reader refuses the ELF"; return 2
  let semis := (args.drop 1).filterMap fun s => (String.toNat? s).map (BitVec.ofNat 32)
  -- Device register 0x10000000 is the UART's transmit holding register.
  Replay.Mmio.replay (QemuVirtRv32.board image.rwBase) image.ro 0x10000000 path
    (ram0 := ram0) (start := some (BitVec.ofNat 32 image.entry)) (semihost := semis)
