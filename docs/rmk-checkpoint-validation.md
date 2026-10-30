# Integrated RMK checkpoint validation

Integration base: `9bacb95` (support + ISA/encode review + exporter/UART).
The checkpoint source/job changes are in the subsequent preparation commit.

Validation in progress on 2026-10-30:

* `cargo test --release -p e5r-verify -j 2`: 24 passed.
* `cargo fmt --all -- --check`: passed (includes formatting an existing dashboard match).
* `cargo-deny check`: advisories, bans, licenses and sources passed with the
  committed license policy. The advisory database was placed in `/tmp` because
  this machine's NFS home does not support its locking. Cargo also emitted a
  package-cache lock diagnostic; the checker exited 0.
* Full workspace release tests and fresh-source RMK/Lean checkpoint: running.
* Fixture generation: unavailable locally; no AArch64 cross compiler installed.
  Oracle-backed fixture coverage must be checked by CI with the configured tools.

This file will be finalized with the fresh checkpoint result before the
preparation is declared complete. Historical receipts are not substituted.
