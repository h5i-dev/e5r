#!/usr/bin/env python3
"""Build h5i's thermostat for QEMU virt, with host paths removed from the ELF."""
import os
from pathlib import Path
import subprocess

ROOT = Path(__file__).resolve().parents[1]
FIRMWARE = ROOT / 'verification/rv32/firmware/thermostat'
H5I = ROOT.parent / 'h5i'


def main():
    version = subprocess.check_output(['rustc', '--version'], text=True)
    if not version.startswith('rustc 1.99.1 '):
        raise SystemExit('This ELF pin requires rustc 1.99.1; select it with rustup.')
    kernel = H5I / 'examples/embedded/thermostat/kernel/src/lib.rs'
    if '#[unsafe(export_name = "thermostat_heater_on")]' not in kernel.read_text():
        raise SystemExit('Apply verification/rv32/firmware/thermostat/h5i-kernel.patch to ../h5i first.')
    env = os.environ.copy()
    # All crates receive the same flags, including panic location strings.
    remaps = [(H5I, 'h5i'), (FIRMWARE, 'thermostat-rv32'),
              (Path.home() / '.cargo/registry/src', 'cargo-registry')]
    env['CARGO_ENCODED_RUSTFLAGS'] = '\x1f'.join([
        '-C', 'relocation-model=static',
        '-C', 'jump-tables=no',
        '-C', 'llvm-args=-max-store-memcpy=32',
        *(f'--remap-path-prefix={source}={dest}' for source, dest in remaps),
    ])
    subprocess.run(['cargo', 'build', '--release', '--locked', '--target',
                    'riscv32imac-unknown-none-elf'], cwd=FIRMWARE, env=env, check=True)


if __name__ == '__main__':
    main()
