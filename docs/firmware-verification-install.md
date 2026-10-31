# Installing the firmware verification toolchain

The steps below install everything that
`scripts/check-firmware-verification.sh` needs on Ubuntu 24.04 (x86-64), the
configuration CI uses. Every version is pinned, and the checks refuse other
versions where it matters.

| Tool | Version | Why it is pinned |
| --- | --- | --- |
| Lean | 4.35.0 (`verification/rv32/lean-toolchain`) | The kernel that checks the proofs |
| Rust | 1.98.1 with `riscv32imac-unknown-none-elf` and `llvm-tools` | The firmware's bytes, and therefore every proof, depend on it |
| GNU binutils (RISC-V) | 2.42 | Assembling the differential test programs |
| QEMU | 8.2.2 (`qemu-riscv32`, `qemu-system-riscv32`) | Independent execution for the differential tests |

## 1. System packages

```sh
sudo apt-get install -y --no-install-recommends \
  binutils-riscv64-linux-gnu qemu-user qemu-system-misc python3 curl git
```

On other distributions install the same versions, or set `CROSS_COMPILE`,
`QEMU_RISCV32` and `QEMU_SYSTEM_RISCV32` to where they are.

## 2. Rust

```sh
curl -sSf https://sh.rustup.rs | sh -s -- -y --default-toolchain stable
rustup toolchain install 1.98.1 --profile minimal \
  --target riscv32imac-unknown-none-elf --component llvm-tools
```

## 3. Lean

```sh
curl -sSfL https://raw.githubusercontent.com/leanprover/elan/v4.1.2/elan-init.sh -o elan-init.sh
sh elan-init.sh -y --default-toolchain none
```

elan reads `verification/rv32/lean-toolchain` and downloads Lean 4.35.0 the
first time `lean` runs in that directory.

## 4. Check everything

```sh
git clone https://github.com/h5i-dev/e5r && cd e5r
./scripts/check-firmware-verification.sh
```

The script first builds `e5r-verify` (release profile). Then it rebuilds
the firmware and the clamp fixture and checks every job from source. Last,
it runs the negative controls and the two QEMU differential tests. On the
development host this takes about 15 minutes, with a peak of about 1 GB of
resident memory. Each Lean step runs with one worker and a 5 GiB
resident-memory limit.

Results land in `verification/rv32/build/results/`. Check that a stored
result still describes the sources with
`target/release/e5r-verify verify-result FILE`.

## Without network access

A machine with only Lean installed can recheck a bundle produced elsewhere.
See "Rechecking without e5r" in
[firmware-verification.md](firmware-verification.md). Rebuilding the
firmware itself needs its crates. Run `cargo fetch` (or `cargo vendor`) in
`verification/rv32/firmware/hifive1-embassy` while online.
