# Independent specification to PTX: measured experiment

2026-11-05 UTC. Worktree `ptx-from-spec`, verifier base `b99d7a1`. The experiment produced a directly authored PTX kernel for a restricted real CuPy API composition, an accepted functional/safety proof, and reproducible A10G measurements. No verifier extension was needed. Candidate v1 is the only candidate; no performance tuning revisions were made.

## What the experiment establishes

The candidate implements `cupy.bitwise_xor(x.byteswap(), uint32(mask))` for contiguous 1-D native uint32 input and a disjoint output. It reads each word once and writes once. Standalone byte conversion is represented by mask=0. This is a concrete endian conversion/masking subset, not a general CuPy replacement or an INT4 implementation. It complements the separate bit packing/equivalence experiment. No other worker's candidate was inspected.

The independent [frozen specification](SPEC.md) describes input bytes and the source bit for every output bit. It was committed with the directly authored PTX in `c559e1f` before CUDA baseline authorship/compilation or GPU timing. The candidate uses a two-stage permutation, while the JSON contract expresses four independently placed bytes. `contract_layout` proves the contract equals the frozen bit permutation for all x/mask, and `implementation_contract` uses that bridge in the actual PTX execution proof. Enumerating the 32 possible bit positions leaves both 32-bit input and mask arbitrary; it does not enumerate sample input values.

An initial CuPy 13.6.0 pin was wrong: that version has no byteswap API. Before timing, the pin was explicitly corrected to 14.2.0, whose published API and executable behavior were checked. The mathematical spec, candidate and declared sweep were unchanged. The original frozen file is retained; [API-PIN.md](API-PIN.md) records the correction. The provenance also discloses an incidental API-wrapper excerpt surfaced by web search; no upstream transform kernel algorithm was copied.

## Proved properties

`e5r ptx check --proof E5rProof.lean` accepts `E5rProof.correct : E5rSpec.statement` against PTX SHA256 `00a3aa3c8853ab99495822aa10c28f98a5e88867c43ac036c61ec57cb280587c` and contract SHA256 `bf776281c41e45abecbf18130b156d7e9c0f56f111abb49e05f2f54012035366`.

The existing `MapSpec.Correct` theorem over actual E5R PTX instruction/SIMT semantics proves, for every input/mask/initial output/register state and every modeled interleaving under its preconditions:

- memory access legality and bounds;
- race freedom, progress, a global step bound and existence of a completed execution;
- the independent byte-permutation/XOR result at every output index;
- preservation of every byte outside output, including input.

The domain is all uint32 lengths (including zero) and masks, 4-byte aligned ranges that fit the 64-bit address space and are disjoint, with one-dimensional launches satisfying `n <= G*B <= 2^32`. SPEC.md additionally requires positive hardware launch dimensions; the model theorem also handles empty modeled launches where permitted by its precondition. Real host launches use 256 threads and at least one block. Tails have no memory accesses. The theorem's full domain is much larger than the tested GPU allocations.

Negative controls also passed: a stale PTX proof manifest is refused (`unknown`, not falsely `proved`), and three semantic mutations are formally refuted with Lean-replayed counterexamples. Wrong byte order and wrong index produce `wrong_value`; the dropped-tail mutation produces `fault` on zero-length unsigned underflow. The independent GPU control also detects its dropped final element at length 257. See [negative-controls.json](results/negative-controls.json) and the corresponding `*_refutation.json` files.

The supplied checker replayed **71 proof declarations** through `Kernel.Environment.replay`. The explicit audit covers **81 proof/statement declarations** and records the exact graph of **4,775 transitive dependencies**, including the independent layout bridge. Its only axioms are `propext`, `Quot.sound`, `Classical.choice`. There is no sorry, new axiom, native_decide, bv_decide or compiler-trust shortcut. A separate `leanchecker E5rProof` replay exited successfully; [replay.json](results/replay.json) records the checker binary and module hashes. This is accepted proof evidence, not compilation or test agreement relabeled as proof.

The first accepted check took 384.60 seconds including a fresh full library/checker build ([first-build evidence](results/proof-first-build.json)). The committed final warm check took 40.58 seconds: proof elaboration 11.83 s, supplied replay 23.50 s, plus setup/check overhead. CPU proof jobs were active concurrently; these elapsed times are observations, not benchmark claims. Lean v4.35.0 used one thread, a requested 2,500 MB memory cap and a 600 s per-check timeout. These are checker configuration values: hard memory isolation requires working systemd support in the existing checker; no hard cap is claimed for a fallback environment. [proof.json](results/proof.json), [generated statement](results/E5rSpec.lean) and [dependency audit](results/axiom-audit.json) retain exact evidence. `verify.sh` regenerates these from PTX and JSON rather than trusting the committed generated statement.

## GPU correspondence

On NVIDIA A10G sm_86, driver 595.112.07, CUDA runtime/driver API 13020, the directly loaded PTX driver-JIT output agrees with an independent CPU byte-array reversal/XOR, NumPy and actual CuPy 14.2.0 APIs. The correctness sweep covers **28 lengths x 5 masks x 4 implementations**, including zero, byte-distinct patterns, all single bits, signed-looking uint32 values, block boundaries and tails. Input preservation and surrounding canaries were checked for candidate and CUDA baselines. The three GPU mutants (wrong byte order, wrong index and dropped tail) were all detected. Details are embedded in [benchmark-run1.json](results/benchmark-run1.json).

Separately, ptxas 13.2.51 assembled the same candidate, and its cubin passed ten lengths with the host wrapper on a non-default stream. The wrapper also passes a 4-byte aligned, non-16-byte-aligned case and rejects ten unsupported/invalid call forms, including misalignment, inplace overlap and fractional masks; see [wrapper.json](results/wrapper.json). The wrapper itself is empirically tested, not formally proved.

All GPU activity held exclusive `/mnt/scratch/e5r-gpu-benchmark.lock`. Foreign compute PIDs were checked separately before context creation, for every correctness length and measured batch, and after completion; detection aborts the run. No foreign process was observed in the accepted runs. This check cannot prove the absence of arbitrarily short unobserved workloads or all graphics/system traffic. No other worker processes or GPU settings were changed.

## Performance

The predeclared sweep contains all 12 lengths in SPEC.md. Every result, including zero-length regression, appears in [TIMINGS.md](results/TIMINGS.md); [raw JSON](results/benchmark-run1.json) retains all nine batch samples, standard deviations, minima/maxima and effective throughput for 144 shape/mode/method rows. Methods were randomly ordered with a fixed seed. Each batch contains 100 repetitions. Data and output buffers were preallocated, all kernels warmed, and startup/JIT excluded.

CuPy byteswap has no `out=` parameter. The harness calls the actual pinned `x.byteswap()` API using a scoped allocator that returns a dedicated preallocated temporary, then actual `cp.bitwise_xor(..., out=y)`. The allocator checks the requested size and the temporary remains live throughout. Output is validated before timing. No substitute byte-transform kernel is used for the OSS baseline. The raw method key `cupy_api_fused` names the common fused task, but this baseline executes the two separate API operations.

Competent matching CUDA baselines use `__byte_perm(...,0x0123)` and XOR in one kernel, compiled with `nvcc -O3 -std=c++17 -arch=sm_86 -cubin`. Both scalar and vectorized uint4 versions are shown; the best is used in the ratio. The vectorized baseline is restricted to 16-byte aligned buffers and n <= 2^31; all benchmark arrays meet those restrictions. The candidate and scalar CUDA require only 4-byte alignment. Baselines are comparison artifacts, not formally proved implementations. Standalone CuPy/CUDA byteswap-only numbers are context and perform less work than the fused task.

The principal device comparison uses CUDA graphs containing 100 operations and event timing around replay. Ordinary event timing is also published; it includes Python API/submission gaps between operations, which make small/medium-size OSS event ratios much larger and more variable. Those are not presented as device execution speedups. This host was also running other CPU proof jobs; the raw direct-event outliers are retained. Graph replay removes per-operation Python submission and is the basis for the claims below.

| Elements | PTX graph us | CuPy graph us | CuPy / PTX | Best fused CUDA us | CUDA / PTX | PTX effective GB/s |
| ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| 1,048,576 | 13.906 | 29.594 | 2.128x | 13.824 | 0.994x | 603.24 |
| 4,194,304 | 69.366 | 139.950 | 2.018x | 69.376 | 1.000x | 483.73 |
| 16,777,216 | 273.562 | 550.574 | 2.013x | 273.541 | 1.000x | 490.63 |

The >=1.5x goal versus the actual OSS composition was met at **all three predeclared bandwidth shapes**, geometric mean **2.052x**. The explanation is fusion: the composition reads/writes two full arrays whereas the fused kernel reads/writes one. **Hand-authored PTX did not beat the optimized fused CUDA baseline.** The graph ratios against best CUDA across nonzero shapes range about 0.984x to 1.000x. At zero length, CuPy skips transform kernels; PTX launches a guarded no-op and is slower (0.932 us vs 0.123 us, 0.132x). No result is omitted for missing the goal.

Reported effective bandwidth counts 8*n bytes, one 4-byte read and write. It is an application traffic metric, not a hardware DRAM counter. Repeated graph buffers can reuse cache; cache behavior was not measured with hardware counters. No cold-cache guarantee, power locking, cross-device portability, or statistically significant PTX advantage is claimed.

## Trust boundary and remaining scope

Lean proves the candidate in E5R's existing model; PTX parsing/export and contract translation are reviewed/trusted interfaces and are bound by SHA256. The memory model is the repository's race-free sequential-interleaving fragment, whose correspondence to NVIDIA's weaker PTX memory model is an assumption documented in docs/verification/ptx.md. Hardware allocation validity and absence of concurrent external writes are launch assumptions.

An extra invalid-supplied-proof attempt exposed the existing checker's launcher timeout limitation: a shell descendant could survive the launcher and hold its output pipe open. Only this experiment's verified orphan was stopped. Final controls instead use stale-manifest rejection and automatic semantic refutations with a 120 s budget. The verifier was not modified; this timeout/resource-isolation limitation remains.

ptxas, driver JIT and their SASS output are outside Lean. The empirical tests are specific to this GPU/toolchain. Host validation, Python/CUDA/CuPy/NumPy implementations and the runtime are outside the formal theorem. Signed types, noncontiguous layouts, inplace API behavior, arbitrary dtypes, scale/group transforms and INT4 packing are not supported. This small workload demonstrates the direct-spec workflow and a useful fusion gain; it supplies no evidence that hand assembly generally outperforms CUDA.
