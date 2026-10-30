# R0 reproducibility audit: RMK `qemu-riscv-rynk` (independent of main's receipt)

Exporter/runner worker, 2026-10-29. This audits main's R0 recipe and receipt
(`verification/rv32/rmk/build-canonical.sh`, `R0-receipt.md`, support-lean4
`6de3a30`) with my own builds and comparison tools. Nothing here verifies RMK;
it only says which bytes a recipe produces, and how two builds differ.

Target: rmk `71556128fa72881fc35f0bf6c292d5e28ad9568d`,
`examples/use_rust/qemu-riscv-rynk`, `Cargo.lock` sha256 `4d994f17…c49c`.
Toolchain 1.98.1 (rustc `48a229cea`, cargo `797e8a9bc`, LLVM 22.1.8) is used
read-only through `RUSTUP_TOOLCHAIN`. Each build uses `--release --locked`, a
fresh shallow checkout and a fresh private `CARGO_HOME` under `/dev/shm`,
removed after the build. The full environment is in `env-canonical.txt`.

The original ELF `f39d833f…` was preserved before any build, at
`~/.local/state/e5r-claude-rmk-export-20261029T174012Z/rmk-qemu-riscv-f39d833f.elf`
and in the RMK jobs' `build/` directory.

## Build matrix (`scripts/rmk-r0/run-matrix.sh`, log `build-matrix.log`)

| Build | Recipe | Checkout path | Remap | sha256 |
| --- | --- | --- | --- | --- |
| main canonical #1, #2 | main's `build-canonical.sh`, verbatim | `/dev/shm/e5r-rmk-canonical/rmk` | yes | `5871dceee5aa302705f4d3ef423ee6765951c0c7d314e996559641630bf16a06` (both) |
| mine, canonical path | `scripts/rmk-r0/build.sh` (written separately) | `/dev/shm/e5r-rmk-canonical/rmk` | yes | `5871dcee…` (same bytes) |
| mine, recon path | `build.sh plain` | `/dev/shm/e5r-rmk-recon/rmk` | no | `e95989308a27531733b766913d2e2d01f88bfdebd0f1c044368d667c3bccc39a` (= main's recon row) |
| mine, path A | `build.sh remap` | `/dev/shm/e5r-claude-r0x/a/rmkA/rmk` | yes | `48aefe786b47aea76da66e6c352426deb058b504b410ec1d81436e33b25ae9c1` |
| mine, path B | `build.sh remap` | `/dev/shm/e5r-claude-r0x/b-longer-name/rmkB/rmk` | yes | `8a57bf625572d1240c30fbf37ad81fa87eb33c2aaa4f503c3a86f5ec171265ff` |
| mine, path A | `build.sh plain` | `/dev/shm/e5r-claude-r0x/a/rmkA/rmk` | no | `321a40dc8d00cbfde708fb5fbeef3280a325903312e9b694521a9fdcda41dc35` |
| pinned evidence (peer) | recon recipe | `/dev/shm/e5r-isa-review-20261029T042314Z/rmk` | no | `f39d833f520ba4de6c7085423a8dc3ee475ec19bdfb55c10c81c6ae868f43c30` |

Each build took about 21 s.

What this establishes:

* **Canonical recipe:** reproduced three times, by main's script and by a
  separately written one, all on this machine: 5871dcee, byte-identical, with no
  build path embedded.
* **Same path, same bytes:** this held at every path tried. Main's recon row
  e9598930 was reproduced at its path by a different script, at a different
  time.
* **Path independence does not hold**, with or without `--remap-path-prefix`.

## Why the path matters (checked, not assumed)

`cargo build -v` logs give every rustc invocation's `-C metadata`
(`metadata-*.txt`, 191 invocations over 135 crate names).

* **Path changes the metadata of the path crates only.** Between two checkout
  paths, exactly 6 crate names change metadata: the path dependencies `rmk`,
  `rmk_config`, `rmk_macro`, `rmk_types`, the example `rmk_qemu_riscv`, and
  `build_script_build`. All 129 registry crates keep theirs. This holds with
  remapping and without.
* **Remapping changes no metadata.** At one path, remap and plain differ in
  0 crate names.
* **Path changes code, not only layout.** Main's receipt says
  "functions are placed in a different order", which is incomplete:
  * Remapped A vs B differ in 66,551 `.text` bytes (main saw 484 between its two
    paths).
    * Of 456 named functions: 285 have identical bytes, 165 are identical up to
      immediates, 3 differ, and 3 have instance counts that differ.
    * Example: `<Fork as Serialize>::serialize` is 0x106 bytes from A and 0xd6
      from B (`compare-remapA-vs-remapB.txt`).
  * Without remapping, the path also changes `.text` size: 0x210c4 for f39d833f
    vs 0x210f4 for the recon-path build.
    * 28 functions differ; most are serde/postcard monomorphizations in
      `rmk_types`.
    * `compiler_builtins::mem::memmove` moves from 0x80020d9e to 0x80020dce.

  The likely mechanism: symbol names carry the crate hash, and that changes
  codegen-unit partitioning and inlining decisions. The mechanism is inferred;
  the code differences are measured.

## Can f39d833f be rebuilt at its original path?

Not as a clean-room rebuild by me.
* The original checkout and `CARGO_HOME` paths are inside the peer's live tree
  (`/dev/shm/e5r-isa-review-20261029T042314Z/{rmk,cargo-home}`, embedded 24 and
  14 times in the ELF), which I must not change.
* User namespaces are not permitted here (`unshare -rm` fails on `uid_map`), so I
  cannot bind a private scratch tree onto that path. No `proot` or `bwrap` is
  available.
* Rebuilding elsewhere cannot give f39d833f: the matrix shows the bytes follow
  the path.

The peer's own tree holds evidence of a full rebuild there. I only read it:
* Every artifact under `target/riscv32imac-unknown-none-elf/release` (deps,
  build-script outputs, fingerprints) was rewritten between 13:44:59 and
  13:45:40.
* The final fingerprint records `rustflags: []`, i.e. the plain recon recipe.
* The output is the same inode's content, still sha256 f39d833f. I first hashed
  it at mtime 13:07:06 and it now has mtime 13:45:40.

So f39d833f was reproduced at its original path by a full rebuild in the same
target directory and `CARGO_HOME`. That is not a fresh-checkout, fresh-cache
build. A clean confirmation needs the peer, inside its tree, or a machine with
user namespaces.

## Reproducibility boundary (what may be claimed)

* **May be claimed:** `build-canonical.sh` reproduces `5871dcee…` byte for byte
  from a clean checkout and cache on this machine, at the fixed path
  `/dev/shm/e5r-rmk-canonical`, with Rust 1.98.1. Checked three times, by two
  scripts.
* **Must not be claimed:** reproducibility from an arbitrary checkout path; it
  fails, and changes code, not just layout.
* **Untested assumptions:**
  * another machine;
  * another rustup home (the sysroot path is only in a remap flag, and remap does
    not affect metadata, so it is probably harmless, but not tested);
  * another user;
  * a crates.io index state other than today's (`--locked` pins versions; the
    `.crate` checksums are in `Cargo.lock`).
* **f39d833f:** reproducible at its original path (evidence above, not
  clean-room), and nowhere else.

## f39d833f vs canonical 5871dcee (`compare-f39d833f-vs-canonical.txt`)

`scripts/rmk-r0/compare_elf.py`, which matches functions by demangled name, with
crate hashes and `.llvm.<n>` suffixes ignored:

* **ELF layout:**
  * The entry and `.text` (0x210c4 bytes at 0x80000000) have the same address
    and size; 29,460 bytes of `.text` differ.
  * `.rodata` shrinks from 0x7f20 to 0x78e8, because the embedded paths are
    gone.
  * Everything after `.rodata` moves down 0x638 bytes. `rwBase` goes from
    0x80029bc8 to 0x80029590, the read-only PT_LOAD 1 from 0x8aec to 0x84b4
    bytes, and `.stack` grows by the same amount.
  * PT_LOAD 0 is identical in headers.
* **Functions (454):** 138 have identical bytes and 316 are identical up to
  immediates. None differ in instruction sequence; 77 moved.
* **memmove:** the trampoline `memmove` (0x80020c1e+8),
  `compiler_builtins::mem::memmove` (0x80020d9e+0x31c) and
  `compiler_builtins::mem::memcpy` (0x80020c26+0x178) have identical bytes at
  identical addresses.
* **Deframer:** `tail`, `next`, `park_pending`, `unpark_pending` and
  `slice_index_fail` keep their addresses and sizes. 5/52, 6/114, 4/36, 2/26
  and 4/55 of their instructions differ, all `lui`/`addi` constants that address
  `.rodata` (panic-location records).

## Migrating the evidence to 5871dcee: cost and risks (not done)

* **Image job (`jobs/rmk/rmk-qemu-virt-image.json`):** update `elf_sha256`, and
  the expected bytes in `Entry.lean` if any change (the entry bytes are the same).
  The generated fidelity module derives `rwBase` itself.
* **Checked here, without migrating anything:** a throwaway RAM-image job on
  5871dcee (`e5r-verify check`, board `qemu-virt-rv32`) is `proved`. The
  exporter accepts the ELF, and the kernel proves `RamElf.accepts`, the manifest
  agreement, entry 0x80000000, `rwBase` 0x80029590 and the same first four bytes
  at the entry.
* **memmove n<16 proof:** the code it is about is byte-identical at the same
  addresses, so the 40 instruction facts and the loop and contract proofs carry
  over. The data-layout constants do not:
  * `rwBase` 0x80029bc8 in `Fetch.lean` (`B`), `MemmoveSmall.lean` (`Slots`),
    `MemmoveLoops.lean` and `Coherence.lean`;
  * the `.rodata` segment size 35564 (0x8aec) and its shape in `Fetch.lean`
    (`roShape`/`ro_eq`).

  The proof's precondition then admits a stack slightly lower in RAM, a
  different contract instance. This is low effort: re-run the job and review the
  changed constants. The proofs are still checked against the new bytes, not
  assumed equal.
* **Deframer (R2, specification only):** the candidate pcs hold. Every proof
  step through the panic-argument setup would see different constants. This is
  cheap before the proofs exist and costly after.
* **Replay (R1):** must be re-run on the new ELF. Function layout outside the
  read-only image moves.
* **Risk:** the canonical bytes depend on the fixed path. A later change to the
  recipe (another path, toolchain or lock) is another binary, and the evidence
  must follow by hash. The runner's `elf_sha256` pin already refuses a mismatch.

## Tools

* `scripts/rmk-r0/build.sh CHECKOUT_ROOT remap|plain OUT`: one audited build. It
  refuses an existing root, checks the pin and the lock hash, and records the
  environment, the `-v` log and the number of embedded paths.
* `scripts/rmk-r0/run-matrix.sh OUT CANONICAL_SCRIPT`: the matrix above.
* `scripts/rmk-r0/compare_elf.py OLD NEW [--json F] [--focus NAME]...`: section,
  program-header and function comparison. `SHOW=n` prints the first n differing
  instructions of each focused function.
