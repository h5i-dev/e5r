# RAM-image export (`e5r-verify ram-image`)

Exports a RAM-resident, statically linked RV32 ELF as the initial RAM a loader
writes, for machines without flash such as QEMU `-M virt -bios none -kernel`.
Built for the RMK milestone (R0-R1 in [`ROADMAP.md`](ROADMAP.md)); the first
target is the pinned `qemu-riscv-rynk` example. It is a loader, not a proof:
nothing about RMK is verified by exporting it.

The flash exporter (`e5r-verify flash`) and the plain V0 export are unchanged
and still refuse this ELF (`physical address 0x80000000 is not in flash`,
`ELF must be between 52 and 65536 bytes`).

## Command

```
e5r-verify ram-image (--ram BASE:SIZE | --board BOARD.json) --mapping paddr=vaddr \
    [--max-file N] [--max-file-bytes N] [--namespace NS] --out DIR IMAGE.elf
```

- `--ram BASE:SIZE` or `--board` (a board JSON with exactly one `"ram"` region):
  the window every `PT_LOAD`, zero-fill included, must lie in. Exactly one.
- `--mapping paddr=vaddr` is required and is the only policy: every `PT_LOAD`
  must have `p_paddr == p_vaddr`. An ELF whose load and run addresses differ
  (a flash image with `.data` copied to RAM) is refused, not reinterpreted.
- Budgets, explicit and bounded: `--max-file` (default 1 MiB, ceiling 16 MiB)
  caps the ELF size; `--max-file-bytes` (default 512 KiB, ceiling 4 MiB) caps
  the materialised bytes: `p_filesz` of writable segments plus `p_memsz` of
  read-only ones (their zero-fill becomes image bytes in Lean). Writable
  zero-fill is never materialised, so it is bounded only by the RAM window.
- `DIR` must not exist. Everything is validated before it is created, so a
  refusal writes nothing. Exit status 0 only on success.

Output:

| file | content |
| --- | --- |
| `manifest.json` | `e5r.ram-image.v1`, below |
| `seg-<i>.bin` | `ELF[p_offset, p_offset + p_filesz)` of program header `i`, exactly |
| `image.lean` | only the packed file: `import Theories.RamElf`, then in namespace NS `def elf : E5R.RamElf.File := ⟨len, [w0, w1, ...]⟩`, word `i` = Σ_{k<64} byte(64i+k)·256^k (decimal; the last word is short). Packing is one function, `ram::pack`. |

## What the image means

For each `PT_LOAD`: `RAM[p_vaddr, p_vaddr + p_filesz)` = the blob and
`RAM[p_vaddr + p_filesz, p_vaddr + p_memsz)` = 0. RAM outside the segments is
unconstrained. `manifest.json` lists the assumptions a proof over the image must
state or discharge; the exporter establishes only A1's byte equations:

- **A1 initial RAM**: the equations above.
- **A2 fetch coherence**: R/W/X are ELF metadata. On `virt` RAM is writable and
  executable (no PMP under `-bios none`), so a model that fetches from the
  exported bytes describes QEMU only while no store or AMO writes an executable
  segment. That is a proof obligation, not a property of the image.
- **A3 entry**: QEMU starts at its reset ROM (0x1000), which jumps to `e_entry`
  with `a0 = mhartid`, `a1 = device-tree address`, `a2 = 0x1028`, `t0 = entry`.
- **A4 loader**: QEMU places `p_filesz` bytes at `p_paddr` and zero-fills to
  `p_memsz`.
- **A5 machine RAM**: the window must lie inside the machine's RAM, and no other
  blob QEMU loads may overlap a segment. QEMU `virt` defaults to 128 MiB
  (0x80000000..0x88000000) and puts the device tree at 0x87e00000; RMK's linker
  script uses only the first 16 MiB. With `-m 16M` the device tree lands inside
  RMK's `.stack` and QEMU itself refuses to start.

## Validation

Every refusal names the rule. Header: ELF32, little-endian, `EV_CURRENT`,
`ET_EXEC`, `EM_RISCV`, `e_flags` only `EF_RISCV_RVC` (soft-float, no RVE/TSO),
52/32-byte header sizes, 1..=16 program headers inside the file. Program headers:
`PT_NULL`, `PT_GNU_STACK` (not executable) and one `PT_RISCV_ATTRIBUTES` are
accepted, `PT_LOAD` is exported, any other type (dynamic, interp, TLS, phdr...)
is refused. Each `PT_LOAD`: readable, flags within RWX, not W+X;
`0 < p_memsz`, `p_filesz <= p_memsz`; `p_offset + p_filesz` inside the file
(checked addition); `p_paddr == p_vaddr`; `[p_vaddr, p_vaddr + p_memsz)` inside
the RAM window (no 32-bit wraparound); `p_align` 0, 1 or a power of two with
`p_vaddr ≡ p_offset`. Segments ascend and are disjoint over `p_memsz`, so the
zero-fill of one cannot overlap the bytes of the next. The entry is 2-aligned
and its first halfword lies in the file bytes of an executable segment.
`rw_base`, the end of the highest read-only segment, must lie inside the RAM
window with RAM left above it, and every writable segment must start at or above
it: the checker models read-only segments as the immutable image and
`[rw_base, RAM end)` as RAM.
`Tag_RISCV_arch` must start with `rv32`. Finally e5r's analysis loader, a
second reader, must map the same bytes with the same execute bit and see no
relocation or dynamic sections.

## Checking an export independently

- `python3 -I scripts/check-ram-image.py IMAGE.elf DIR`: GNU `readelf -hlW` for
  every header field and the entry, `objcopy -I elf32-little -O binary` (writes
  file-backed contents at their load addresses) and `hashlib` for the bytes.
  `objcopy` needs section headers, which linked firmware has.
- `python3 -I scripts/check-ram-image-lean.py IMAGE.elf DIR RV32_DIR`: unpacks
  every word of `image.lean` in Python and compares all bytes and the sha256
  with the ELF, then compiles `Theories.{Hart,Platform,RamElf}` from `RV32_DIR`
  and the image module with plain `lean`, and has the kernel decide
  (`decide +kernel`) that `RamElf.accepts` holds and that `RamElf.check`
  returns exactly the manifest's entry, PT_LOAD table and `rw_base`.
- `python3 -I scripts/check-ram-image-negative.py E5R_VERIFY IMAGE.elf RV32_DIR`:
  11 header mutations of the ELF (load != run address, W+X, overlap, odd or
  stray entry, past RAM, truncated, float ABI, PT_DYNAMIC, filesz > memsz,
  writable below read-only); each must be refused by `ram-image` (nothing
  written) and the kernel must prove `accepts = false` for the reader. The
  unmutated file is the positive control.
- `QEMU=.../qemu-system-riscv32 python3 -I scripts/check-ram-image-qemu.py
  IMAGE.elf DIR [QEMU args]`: boots QEMU halted (`-S`) after its loader ran,
  checks `info roms` (segments exactly as in the manifest, nothing overlapping
  them), dumps each segment with `pmemsave` (blob bytes then zeros), and checks
  the reset ROM jumps to the manifest's entry.

## The pinned RMK example

ELF: rmk `71556128fa72881fc35f0bf6c292d5e28ad9568d`,
`examples/use_rust/qemu-riscv-rynk`, `RUSTUP_TOOLCHAIN=1.98.1 cargo build
--release --locked` (built by the review worker, see its `review/rmk/README.md`),
454 024 bytes, sha256
`f39d833f520ba4de6c7085423a8dc3ee475ec19bdfb55c10c81c6ae868f43c30`.

```
e5r-verify ram-image --ram 0x80000000:0x1000000 --mapping paddr=vaddr \
    --namespace Rmk.QemuRiscvRynk --out OUT rmk-qemu-riscv
OUT: 4 PT_LOADs, 170955 file bytes, 16606256 zero bytes, ELF sha256 f39d833f...
```

| PT_LOAD | range | filesz | memsz | flags | sha256 of file bytes |
| --- | --- | --- | --- | --- | --- |
| 0 `.text .init.rust` | 0x80000000.. | 0x210da | 0x210da | R X | `6327ee65f6d15f1d968ca2dab4da23a132f84faf7e9cb4b8551417547e4b1b3b` |
| 1 `.rodata .eh_frame` | 0x800210dc.. | 0x8aec | 0x8aec | R | `8bcc02e1e8b9254ed68d9f61f3711bc108c2262ceb2523693666d095ebaf449a` |
| 2 `.data` | 0x80029bc8.. | 0x5 | 0x5 | RW | `0bd288cecce2dfc6c9b9245ab747a10870f84c16e986e61b259603b59cf1f3b9` |
| 3 `.bss .uninit .heap .stack` | 0x80029bd0..0x81000000 | 0 | 0xfd6430 | RW | (empty) |

`--ram` is the linker script's 16 MiB (`memory.x`), the tighter of it and QEMU's
128 MiB. The manifest, `SHA256SUMS` of every output (including `image.lean`) and both
oracle transcripts are in
[`verification/rv32/ram-image/rmk-qemu-riscv-rynk/`](../verification/rv32/ram-image/rmk-qemu-riscv-rynk/).
Two exports, and one of a copy at another path, are byte-identical. The unit
test `ram::tests::pinned_rmk_qemu_riscv_rynk` re-checks the layout and hashes
when `E5R_RMK_ELF` names the ELF (it passes vacuously otherwise).

## Handoff to the Lean side

The image the model runs is **defined** by the checker's reader,
`E5R.RamElf.imageOf base size elf` (`Theories/RamElf.lean`, written
independently of this Rust), so `image.lean` carries only the file. Nothing the
exporter parses is trusted by Lean; the manifest's `entry`, `segments` and
`rw_base` are a cross-check, which `check-ram-image-lean.py` turns into
kernel-checked theorems. What links the Lean literal to the ELF is the packing:
checked over every byte by the Python unpacker above (and equal to the checker's
own packing of the same ELF).

Measured on the pinned RMK ELF against `RamElf.lean` at support-lean4
`d96ca45` (Lean v4.35.0): the module elaborates in ~9-10 s / ~730 MB; the
kernel decides `accepts = true` and the manifest agreement in 2-16 s / ~550 MB.
`image.lean` is 1.1 MB, regenerated rather than committed (its sha256 is in
`SHA256SUMS`).

These theorems are about the reader's output on these bytes. They are not a
proof of anything RMK does, and the reset-state facts (A3: registers at entry,
A5: QEMU's RAM size and device-tree placement) remain board assumptions.

Where the two readers differ (from reading `RamElf.lean`; the Rust side is the
stricter one, and the image is the reader's): the reader does not check
`p_align`, a `PT_GNU_STACK`'s flags, `Tag_RISCV_arch`, section headers
(relocations), or `PT_NULL` fields; it lets the entry lie in a read-only
segment's zero-fill (Rust requires its file bytes); its read-only budget is
4 MiB of `p_memsz` (Rust: `--max-file-bytes`, default 512 KiB of materialised
bytes).
