# Concrete PTX target scoreboard

Controlled translation-validation screens using project-authored CUDA originals, not production OSS kernels. Transpose starts from textbook naive uncoalesced stores and reaches tuned-CUDA parity. Xorshift is a handpicked fixed64 workload; tuned CUDA often wins. These measurements do not establish superiority over tuned OSS or nvcc broadly. Existing 2f386ea is preserved; new rows require separate exact proof acceptance.

| Target | Correctness | Original parse | Graph GM original/candidate | Largest original/candidate | GM tuned/candidate | Status |
|---|---:|---|---:|---:|---:|---|
| advance256 | 3072 | True | 1.000x | 1.000x | 1.000x | measured miss / timeboxed; UNPROVED |
| transpose | 768 | False | 2.037x | 1.855x | 1.000x | promising, UNPROVED; original outside current parser |
| laplace | 768 | False | 0.861x | 1.014x | 0.998x | measured miss / timeboxed; UNPROVED; original outside current parser |
| xor8 | 3072 | True | 1.048x | 0.999x | 1.007x | measured miss / timeboxed; UNPROVED |
| crc32word | 3072 | True | 1.259x | 1.088x | 1.040x | measured miss / timeboxed; UNPROVED |
| xorshift32x64 | 5120 | True | 1.969x | 1.941x | 0.957x | promising, UNPROVED |

All declared shapes, both graph/device-event regimes, variance, versions, resources and source hashes are in each results/performance.json. CUDA tuned comparators use the same known techniques; gains over original are not labeled PTX-only. Shared-tile shape restrictions and raw CRC semantics are explicit in PLAN.md.

Proof status is separate from GPU tests and timing. Standard allowed axioms only; parser/exporter, nvcc, ptxas/JIT and hardware remain outside Lean.
