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

## Verification jobs over RAM images (`image.kind: "ram"`)

`e5r-verify check JOB.json` runs RAM-image jobs alongside flash ones. The job
format is still `e5r.verify.job.v1`; one field is added:

```json
"image": { "kind": "ram", "module": "Projects.ramimage.Image", "namespace": "E5R.RmkImage" }
```

`kind` absent means `"flash"`, and flash jobs run exactly as before (their
results carry `"image": null`). A `ram` job:

1. needs a board whose JSON says `"image_placement": "ram"` and has one `"ram"`
   region and no `"image"` region (`boards/qemu-virt-rv32.json`); a flash job
   on such a board, or a RAM job on a flash board, is an `error`;
2. deletes the previous generated files, then exports with the board's window
   (`ram::ram_image`); a refusal is `unsupported`;
3. writes `<module>.lean` (the packed `E5R.RamElf.File`),
   `build/jobs/<id>/ram-image.json` (the manifest) and `<module>Fidelity.lean`:
   ```lean
   def image : E5R.RamElf.Image := E5R.RamElf.imageOf BASE SIZE elf
   theorem image_accepted : E5R.RamElf.accepts BASE SIZE elf = true := by decide +kernel
   theorem image_agrees : (match E5R.RamElf.check BASE SIZE elf with ...) = true  -- = manifest
   theorem image_entry : image.entry = ENTRY := by decide +kernel
   theorem image_rwBase : image.rwBase = RWBASE := by decide +kernel
   ```
   in the image's namespace. Proof modules import the fidelity module and state
   properties of `NS.image` (the checker's reader applied to the file), with
   the board `E5R.QemuVirtRv32.board NS.image.rwBase`;
4. checks the model (plus `Theories/RamElf.lean`), board, image, fidelity and
   job modules from source, replays them with `leanchecker`, and audits the
   axioms of the job's theorems and of the four binding theorems.

What is trusted where: the image is whatever `RamElf.imageOf` makes of the
file, so the Lean reader is authoritative. The exporter's parse enters only as
`image_agrees`, a theorem the kernel must check; if the two readers disagree the
job is `failed`. What remains outside Lean is the link from the ELF file to the
`File` literal: the Rust packer, the ELF's sha256 pinned in the job, and, in a
bundle, `check-packing.py`, which `recheck.sh` runs to unpack every word and
compare it with the bundled ELF.

Pinning: the result's `inputs.image` records the sha256 of the packed module,
the fidelity module and the manifest, and `verify-result` reports
`stale: generated image` when any of them changes; bundles include all three.

The RMK job (`verification/rv32/jobs/rmk/rmk-qemu-virt-image.json`, outside
`jobs/*.json` so CI, which has no RMK ELF, does not run it) needs the pinned ELF
at `verification/rv32/build/rmk-qemu-riscv-rynk.elf`:

```
cd verification/rv32
cp <rmk>/examples/use_rust/qemu-riscv-rynk/target/riscv32imac-unknown-none-elf/release/rmk-qemu-riscv \
   build/rmk-qemu-riscv-rynk.elf
e5r-verify check jobs/rmk/rmk-qemu-virt-image.json --out build/rmk-result.json   # proved
e5r-verify verify-result build/rmk-result.json                                   # current
```

It proves six theorems (the four bindings, plus `Projects/ramimage/Entry.lean`:
the read-only segments' bases and exec bits, and the first four bytes at the
entry) in about 48 s with a peak of 724 MB. They describe the image, not what
RMK does; nothing here is a safety property. Stating `fetch` at the entry by
`decide +kernel` exhausted the kernel's memory, because looking a byte up in a
segment computes the length of the whole 135 KB segment; proofs over this
image need a cheaper path to its bytes (main's model).

`python3 -I scripts/test-ram-image-job.py E5R_VERIFY IMAGE.elf` runs the
lifecycle tests (19 cases, about 90 s): a proved job and a current result;
the fidelity theorems with a wrong entry, `rwBase` or exec bit failing in
`image_agrees` while the unmodified copy checks; an edited packed module or
manifest making the result stale; a changed ELF against its pin (`error`), an
ELF the exporter refuses (`unsupported`, with no generated module left behind),
a RAM job on a flash board, a flash job on a RAM board, an unknown kind, a
missing ELF or proof module, a forbidden command (`error`), and a proof that
does not check (`failed`). The transcript and the RMK job's result are in
`verification/rv32/ram-image/rmk-qemu-riscv-rynk/`.

## The RMK memmove job (`jobs/rmk/rmk-memmove-small.json`)

This job checks the peer's proof of the emitted `memmove` for copies of fewer
than 16 bytes (`Projects/rmk/MemmoveSmall.lean`, `E5R.Rmk.Memmove.contract`)
against the image the runner generates. Its `image.module` is
`Projects.rmk.Elf` in namespace `E5R.Rmk.Image`, which is the module the
proofs already import (`Projects/rmk/Fetch.lean`). So the runner's packed file
is the only image input. `Projects/rmk/gen_elf.py`, which wrote that module by
hand, is not used, and a run replaces any `Elf.lean` it left (the file is
gitignored).

`Projects/ramimage/Memmove.lean` connects the proofs to the runner's binding.
`img_eq : E5R.Rmk.img = E5R.Rmk.Image.image.ro` holds by `rfl`, and
`board_eq : E5R.Rmk.B = QemuVirtRv32.board E5R.Rmk.Image.image.rwBase` follows
from `image_rwBase`. `E5R.RmkMemmove.contract` restates the contract over that
image and board: from every machine meeting `Memmove.Pre` (pc at the trampoline
0x80020c1e, a quiet core, n < 16, dst and src in model RAM, aligned save slots
in RAM and separate from dst and src, an even return address), a quiet,
deterministic run reaches `Memmove.Post` (at `ra`, callee-saved registers and sp
restored, CSRs unchanged, RAM outside the save slots equal to the memmove of
the entry RAM, overlap in both directions). It covers this function, nothing
more about RMK. The job's `symbols` pin both proof addresses (0x80020c1e,
0x80020d9e) to the ELF's `memmove` symbols.

Result (`verification/rv32/ram-image/rmk-qemu-riscv-rynk/rmk-memmove-small.result.json`):
`proved` in 237 s. It checks eight theorems (the contract, the restated
contract, the two equalities and the four image bindings), with the axioms
`propext`, `Classical.choice` and `Quot.sound`. Every module is replayed by
`leanchecker`. `e5r-verify bundle` plus `recheck.sh` recheck it offline in
137 s.

Limits. The runner enforces `rss_mib` by sampling resident memory and passes
`-M (rss_mib − 512)` to Lean. It never sets an address-space limit:
Lean reserves far more virtual memory than it touches, so `ulimit -v` at
24–40 GB makes it fail with "failed to create thread" even though RSS stays
below 1 GB for most modules. One module is heavy: `Projects/rmk/Fetch.lean`
peaks at 6.5 GB RSS for 50 s, in the proof and again in its `leanchecker`
replay. With `rss_mib` 6144 (Lean `-M 5632`) it fails with "(kernel) excessive
memory consumption", so the job sets 10240.

Controls (`python3 -I scripts/test-rmk-memmove-job.py E5R_VERIFY [BUNDLE]`,
transcript `memmove-job-controls.txt`):
- One instruction of memmove changed (0x80020da6 `sub a3,a0,a1` → `sub a5,a0,a1`):
  - with the pin, this is an `error`;
  - without it, the image exports and the reader accepts it, but the
    instruction fact for 0x80020da6 fails (`failed`).
- A stale proof address is an `error`.
- The image declared as flash is an `error`.
- A claim that model RAM starts 4 bytes later is `failed`.
- In a bundle, one changed word of the packed file fails at the checksums. With
  the checksum forged as well, it fails at `check-packing.py`.

## The RMK memmove contractB job (`jobs/rmk/rmk-memmove-contractB.json`)

This job checks the peer's `E5R.Rmk.Memmove.contractB`
(`Projects/rmk/MemmoveContract.lean`, peer commit `60d2f96`) on the runner's
image. It is **bounded, not full memmove**. `PreB` admits n < 16 in either
direction, or n ≥ 16 copied forward ((dst − src) ≥ n, unsigned) with
src ≡ dst (mod 4). The n ≥ 16 backward path and the misaligned forward path are
not covered. The other conditions are as the peer states them:
- pc at the trampoline 0x80020c1e and a quiet core;
- dst and src in model RAM;
- aligned save slots in RAM, with the stack separated from dst and src;
- an even return address.

`PostB` is the ABI frame (all registers but t0–t6 and a1–a7 preserved), with
CSRs unchanged and RAM outside the save slots equal to the memmove of the entry
RAM.

`Projects/ramimage/MemmoveB.lean` restates it over the runner's image and board
(`E5R.RmkMemmoveB.contractB`), reusing `img_eq` and `board_eq`. The job audits
both contracts, the two equalities and the four image bindings: `proved` in
377 s, peak 6.5 GB RSS (in `Fetch.lean`), standard axioms only. Its bundle
rechecks offline in 220 s, including the packing check. After merging the
peer's larger `MemmoveFetch.lean` (259 instruction facts), the n < 16 job still
proves (`rmk-memmove-small.result.json`).

Mutations (`python3 -I scripts/test-rmk-memmoveB-job.py E5R_VERIFY`, transcript
`memmoveB-mutations.txt`). Each proof mutation edits a copy of the peer's
module, never the module itself. "Rejected" means status `failed`, with the
first Lean error in the named theorem:

| Mutation | Result |
| --- | --- |
| unmodified copy (control) | `proved` |
| `PreB` without src ≡ dst (mod 4) | rejected in `contractB` |
| `PreB` without "forward" | rejected in `contractB` |
| `PreB.dstSep` weakened to `True` | rejected in `contractB` |
| `PostB` claiming a1 preserved | rejected in `finishB` |
| word-loop `sw a2,0(t5)` → `sw a3,0(t5)` in the ELF, unpinned | rejected at instruction fact `f80020ec4` |
| a job module that does not exist | `error` (a tool or job problem, not a rejection) |

A rejected mutation shows that the proof needs that condition. It does not show
that the weakened statement is false.
