/-
  A small check of the pinned RMK image (`jobs/rmk-qemu-virt-image.json`):
  the layout and the first instruction bytes of the image the checker's
  reader defines. (`fetch` at the entry is not stated: it computes the length
  of the 135 KB code segment, which exceeded the kernel's memory limit here.) It is a statement about image contents only. It says nothing
  about what RMK does, and is not a safety property.

  ELF: rmk 71556128fa72881fc35f0bf6c292d5e28ad9568d,
  examples/use_rust/qemu-riscv-rynk, release, sha256 f39d833f...3c30.
-/
import Theories.Platform
import Projects.ramimage.ImageFidelity

namespace E5R.RmkImage.Check
open E5R

/-- The read-only image is two segments, at the ELF's first two PT_LOAD
    addresses, the first one executable. -/
theorem segments :
    (E5R.RmkImage.image.ro.map fun s => (s.base, s.exec)) =
      [(0x80000000, true), (0x800210dc, false)] := by
  decide +kernel

/-- The entry point's first four bytes in the image are those of
    `lui ra, 0x80000` (0x800000b7, little-endian), the first instruction. -/
theorem entry_bytes :
    ((E5R.RmkImage.image.ro.headD ⟨0, [], false⟩).bytes.take 4) = [0xb7, 0x00, 0x00, 0x80] := by
  decide +kernel

end E5R.RmkImage.Check
