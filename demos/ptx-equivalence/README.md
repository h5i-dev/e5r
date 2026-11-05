# Frozen CUDA PTX → directly edited PTX → direct Lean equivalence

**Accepted direct universal equivalence; no meaningful speedup.** The actual
nvcc-generated original and the directly edited candidate produce identical
complete global memory for every input and valid launch in the stated domain.
The proof is a relation between executions of these two concrete programs.
It does not derive equivalence from two operator-spec correctness theorems.

The operation expands four packed bits into four 0/1 bytes per thread. The
original CUDA uses two spread stages; nvcc emits a bit-field insertion and
shift/or/mask sequence. Direct PTX editing replaces that sequence with a
masked multiply. The matching CUDA comparator expresses this same multiply.
All artifacts are small enough to inspect: [CUDA](original.cu),
[frozen original PTX](original.ptx), [edited PTX](optimized.ptx),
[freeze record](freeze.json), [proof](equivalence.lean),
[checker result](results/proof.json).

## Exact theorem and trust boundary

`E5rProof.correct : Equivalence.Spec.Equivalent domain Original.unpack4 Optimized.unpack4`.
The checker regenerates both kernel definitions from their exact PTX text.
The contract binds the original SHA-256, and the supplied-proof manifest binds
candidate SHA-256, contract SHA-256 and Lean 4.35.0. Every declaration in the
supplied proof is independently replayed. Only `propext`, `Quot.sound` and
`Classical.choice` are allowed; the arithmetic proof enumerates the 16 nibble
values using ordinary kernel `decide`, with no native evaluation axiom.

Quantifiers: every uint32 n divisible by 8; every 1D G,B with
n <= G*B <= 2^31; every aligned, nonwrapping, disjoint input n/8-word and
output n-word allocation; every initial byte of global memory and every
initial register, predicate and shared-memory valuation. Empty input is
included. Parameters are the two pointers and n; unused Args fields impose
no additional input restrictions. Physical CUDA grid/block limits are the
caller's responsibility when running on hardware; the model's larger launch
domain is harmless for the mathematical theorem.

Each side has no faults at any reachable configuration, makes progress,
has a finite bound on all execution lengths, is race free, and has at least
one completed execution. For **every independently chosen pair** of reachable
completed configurations, the entire global-memory functions are equal,
including input and external bytes. Different traces/registers are allowed.
Disjoint footprints additionally prove both programs preserve bytes outside
the output. The nested symbolic proof relates the original's concrete final
store directly to the candidate's; `Relational.equivalent_of_paired` lifts
paired finite solo traces to independent global interleavings. The allocation
domain contains no mathematical output function.

PTX parsing/exporting and statement construction remain trusted frontend
code. PTX model correspondence with NVIDIA execution is tested, not proved.
nvcc's CUDA-to-original-PTX translation, NVIDIA ptxas/driver JIT and hardware
execution are outside the Lean theorem. The theorem concerns the frozen PTX,
not CUDA source correctness. It does not prove compatibility with a full
CuPy API. Independent NumPy/CuPy references are supplemental tests.

The added bfi.b32 frontend form admits immediate fields only, with
position + length <= 32. All 561 admitted field ranges were checked over
160 input pairs against real GPU execution, the Lean definition and an
independent per-bit reference (89,760 cases). Broad initial probes found
out-of-range field discrepancies; those forms remain refused and the
observation is retained in [the boundary record](results/bfi-boundary-observation.json).
No attempt is made to attribute the discrepancy to a particular external layer.
The two frozen programs use only position=14,length=4.

## Measurements

GPU/environment: `NVIDIA A10G, GPU-7e5ae9e3-0b19-7ed6-8641-c17e13519a08, 595.112.07, 23028 MiB, 1710 MHz, 6251 MHz`. CuPy 13.6.0, NumPy 2.2.6, CUDA runtime 12090. nvcc 13.2.51, `-O3 -arch=sm_86`. Seven repeats; preallocated buffers; 20 warmups; 100 ordinary launches/repeat or 1000 graph launches/repeat. The shared host flock was held and foreign compute PIDs were checked throughout.

Times below are device microseconds, median ± sample standard deviation. Speedup = original/candidate. Every predeclared shape is included. [Raw JSON](results/performance.json) retains all seven samples, min/max, synchronized host latency, throughput, launch dimensions, versions and artifact hashes.

### CUDA graph replay

| Output bytes | Original PTX µs | Edited PTX µs | Matching CUDA µs | Speedup |
| ---: | ---: | ---: | ---: | ---: |
| 32 | 1.0229 ± 0.0185 | 1.0189 ± 0.0157 | 1.0199 ± 0.0166 | 1.004× |
| 256 | 1.0312 ± 0.0163 | 1.0281 ± 0.0169 | 1.0291 ± 0.0162 | 1.003× |
| 4,096 | 1.0772 ± 0.0175 | 1.0803 ± 0.0229 | 1.0793 ± 0.0173 | 0.997× |
| 65,536 | 1.1438 ± 0.0160 | 1.1428 ± 0.0165 | 1.1438 ± 0.0167 | 1.001× |
| 1,048,576 | 2.0101 ± 0.0170 | 1.9978 ± 0.0157 | 1.9968 ± 0.0167 | 1.006× |
| 16,777,216 | 39.6749 ± 0.0161 | 39.6349 ± 0.0175 | 39.6380 ± 0.0201 | 1.001× |
| 134,217,728 | 307.7950 ± 0.0166 | 307.5011 ± 0.0230 | 307.4959 ± 0.0230 | 1.001× |

Geometric mean across all seven shapes: **1.002×**; range 0.997–1.006×.

### Ordinary launches (includes host enqueue gaps)

| Output bytes | Original PTX µs | Edited PTX µs | Matching CUDA µs | Speedup |
| ---: | ---: | ---: | ---: | ---: |
| 32 | 8.4890 ± 0.6587 | 8.9190 ± 0.2038 | 8.2944 ± 0.2693 | 0.952× |
| 256 | 8.5914 ± 1.3443 | 8.5299 ± 0.1358 | 8.3562 ± 0.4708 | 1.007× |
| 4,096 | 8.7245 ± 0.3597 | 8.6118 ± 0.1495 | 8.4688 ± 0.3906 | 1.013× |
| 65,536 | 8.4179 ± 0.1247 | 8.8064 ± 0.1936 | 8.7859 ± 0.2658 | 0.956× |
| 1,048,576 | 8.3866 ± 0.4512 | 8.3866 ± 0.2489 | 8.5101 ± 0.2402 | 1.000× |
| 16,777,216 | 41.5539 ± 0.0347 | 41.5027 ± 0.0390 | 41.5130 ± 0.2054 | 1.001× |
| 134,217,728 | 309.8624 ± 0.1172 | 309.4928 ± 0.0892 | 309.5757 ± 0.0943 | 1.001× |

Geometric mean across all seven shapes: **0.990×**; range 0.952–1.013×.

The 1.5× target was missed. Graph timings show essentially equal performance
for original, edited PTX and matching CUDA. Small ordinary event measurements
include Python enqueue gaps and show additional noise. At large sizes output
memory traffic dominates; fewer PTX instructions did not yield a meaningful
machine-code throughput improvement. This is a successful translation-validation
example with a negative optimization result, not a PTX performance win.

## Validation and reproduction

[Correctness evidence](results/correctness.json) records 2,616 kernel cases:
random, all-zero/all-one, high-bit and every one-hot word, boundary lengths,
three block sizes, extra inactive threads, untouched input and output canaries.
The reference uses NumPy unpackbits, independently of either PTX expression.
[Negative controls](results/negative-controls.json) mutate the multiplier,
input index and tail guard; manifests are deliberately rebound so those
failures exercise the semantic proof rather than hash checks. A stale
candidate also fails binding. No failed mutation may return `proved`.
The results are `unknown`, not formally refuted: the arithmetic mutation's
attempted proof reaches a recursion limit, while indexing/guard mutations
leave invalid safety obligations. [GPU witnesses](results/negative-gpu-witnesses.json)
independently demonstrate output/canary differences for each semantic mutant,
using extra physical buffers to avoid invalid device addresses. These are
executable defect witnesses, not universal counterexample proofs.

The protocol hash in the measurement metadata matches the retained
[pre-measurement snapshot](results/protocol-at-measurement.md). PROTOCOL.md
subsequently narrows the bfi frontend scope after GPU boundary checks; this
clarification does not change the measured kernels, shapes or timing method.

From repository root, with nvcc/CUDA 13.2, Python 3.12, Rust and Lean installed:

```bash
bash demos/ptx-equivalence/run.sh setup
python3 demos/ptx-equivalence/verify-freeze.py
bash demos/ptx-equivalence/run.sh proof
bash demos/ptx-equivalence/run.sh test
bash demos/ptx-equivalence/run.sh negative
bash demos/ptx-equivalence/run.sh benchmark
bash demos/ptx-equivalence/run.sh report
```

`setup` uses the shared setup script with this demo's requirements.txt,
pinning CuPy/NumPy and the CUDA12.8 runtime/NVRTC wheels used for measurement.
Large state lives under `/mnt/scratch/e5r-ptx-demo`; override E5R_DEMO_SCRATCH
if needed. Torch is not required. Host nvcc remains 13.2. The proof is
independent of these Python/GPU dependencies. Run proof
commands sequentially to avoid duplicate concurrent Lake rebuilds. GPU
scripts take the common lock themselves; never bypass it to run timings.

The primary preserved spec-correctness experiment is [verified packing](../verified-packing/README.md).
Its accepted unpack proof is separate evidence, not a premise of this direct
relational theorem. Pack/fusion drafts and the optional TorchAO exploration
are clearly labeled there; their status does not enlarge this theorem.

Recorded strict replay: 65 declarations, axioms `propext, Quot.sound, Classical.choice`.
