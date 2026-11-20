# R0: corrections and confirmations for main (from AUDIT.md)

Main owns `verification/rv32/rmk/R0-receipt.md` and `docs/ROADMAP.md`; these are
proposed edits, not applied. None of them requires migrating any evidence.

## Confirmed as written

* `build-canonical.sh` gives `5871dceee5aa302705f4d3ef423ee6765951c0c7d314e996559641630bf16a06`:
  run twice verbatim, and once by an independently written script at the same
  path, all byte-identical, with no build path embedded.
* The recon recipe at `/dev/shm/e5r-rmk-recon` gives `e9598930…`, reproduced by a
  different script.
* Cause: across checkout paths, exactly the path crates (`rmk`, `rmk_config`,
  `rmk_macro`, `rmk_types`, the example, build scripts) change `-C metadata`.
  The 129 registry crates do not, and `--remap-path-prefix` changes no metadata.

## Corrections

1. "Functions are placed in a different order" understates the path effect. The
   path also changes **code**. Between two remapped paths, 66,551 `.text` bytes
   differ, and some functions compile differently: `<Fork as Serialize>::serialize`
   is 0x106 bytes from one path and 0xd6 from the other. Without remapping, the
   path changes `.text` size (0x210c4 vs 0x210f4) and moves `memmove` (0x80020d9e
   vs 0x80020dce). The "484 bytes" in the receipt is one pair of paths, not a
   bound. Suggested wording: "the checkout path changes the crate hashes of the
   path dependencies, which changes symbol order, codegen-unit partitioning and
   inlining; remapping cannot remove this".
2. Reproducibility claim, suggested wording: "byte-identical from a clean checkout
   and cache **at the fixed path `/dev/shm/e5r-rmk-canonical`**, Rust 1.98.1, on
   this machine". Not established: any other path, another machine, rustup home or
   user, or a later crates.io index.
3. `f39d833f`: "reproducible only at its original path" is supported, but not by a
   clean-room rebuild. The review tree shows a full rebuild at that path, 13:44:59
   to 13:45:40, `rustflags: []`, that reproduced it, reusing the same target
   directory and `CARGO_HOME`. Nobody can rebuild it cleanly elsewhere: the bytes
   follow the path. A clean check needs the peer's tree or a machine with user
   namespaces (unavailable here).

## For a later migration (informational; nothing migrated)

* `f39d833f` vs `5871dcee`: all 454 functions are byte-identical (138) or differ
  only in immediates (316).
* memmove, `compiler_builtins` memmove and memcpy: identical bytes at identical
  addresses.
* Deframer methods and `slice_index_fail`: same addresses; 2–6 `.rodata` address
  constants differ in each.
* `.rodata` −0x638 bytes; `rwBase` 0x80029bc8 → 0x80029590.
* The canonical ELF passes the RAM-image job (`proved`, `rwBase` 0x80029590).
