#!/usr/bin/env bash
# Recheck this bundle with only Lean (the version in lean-toolchain).
set -euo pipefail
cd "$(dirname "$0")"
sha256sum -c --quiet SHA256SUMS
python3 -I check-packing.py Projects/rmk/Elf.lean build/rmk-qemu-riscv-rynk.elf
for m in Theories/Hart.lean Theories/Platform.lean Theories/Logic.lean Theories/FlashElf.lean Theories/RamElf.lean Theories/Board/QemuVirtRv32.lean Projects/rmk/Elf.lean Projects/rmk/ElfFidelity.lean Projects/rmk/Run.lean Projects/rmk/Fetch.lean Projects/rmk/Cobs/Fetch.lean Projects/rmk/Cobs/Basic.lean Projects/rmk/Cobs/Empty.lean Projects/rmk/Cobs/Scan.lean Projects/rmk/Cobs/Copy.lean Projects/rmk/Cobs/Spec.lean Projects/rmk/Cobs/Loop.lean Projects/rmk/Cobs/Decode.lean Projects/rmk/Cobs/Wrapper.lean Projects/ramimage/Cobs.lean; do
  LEAN_PATH=. lean -j1 -o "${m%.lean}.olean" "$m"
done
LEAN_PATH=. lean -j1 Audit.lean > axioms.actual
diff axioms.expected axioms.actual
echo "recheck: every theorem checked, with exactly the recorded axioms"
