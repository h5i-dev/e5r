"""Regenerate the numerical report from retained raw measurements."""
from pathlib import Path
import hashlib,json,math
D=Path(__file__).resolve().parent

def main():
    data=json.loads((D/'results/performance.json').read_text());rows=data['rows']
    proof=json.loads((D/'results/proof.json').read_text())
    text='''# Frozen CUDA PTX → directly edited PTX → direct Lean equivalence

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

'''
    text+=f"GPU/environment: `{data['metadata']['gpu']}`. CuPy {data['metadata']['cupy']}, NumPy {data['metadata']['numpy']}, CUDA runtime {data['metadata']['runtime']}. nvcc 13.2.51, `-O3 -arch=sm_86`. Seven repeats; preallocated buffers; 20 warmups; 100 ordinary launches/repeat or 1000 graph launches/repeat. The shared host flock was held and foreign compute PIDs were checked throughout.\n\n"
    text+='Times below are device microseconds, median ± sample standard deviation. Speedup = original/candidate. Every predeclared shape is included. [Raw JSON](results/performance.json) retains all seven samples, min/max, synchronized host latency, throughput, launch dimensions, versions and artifact hashes.\n\n'
    for graph in [True,False]:
        text+=('### CUDA graph replay\n\n' if graph else '### Ordinary launches (includes host enqueue gaps)\n\n')
        text+='| Output bytes | Original PTX µs | Edited PTX µs | Matching CUDA µs | Speedup |\n| ---: | ---: | ---: | ---: | ---: |\n'
        rs=[r for r in rows if r['graph']==graph];ratios=[]
        for n in sorted({r['output_bytes'] for r in rs}):
            a={r['implementation']:r for r in rs if r['output_bytes']==n};ratio=a['original']['median_us']/a['optimized']['median_us'];ratios.append(ratio)
            cells=[f"{a[k]['median_us']:.4f} ± {a[k]['stdev_us']:.4f}" for k in ['original','optimized','matching_cuda']]
            text+=f"| {n:,} | "+' | '.join(cells)+f" | {ratio:.3f}× |\n"
        gm=math.exp(sum(map(math.log,ratios))/len(ratios));text+=f'\nGeometric mean across all seven shapes: **{gm:.3f}×**; range {min(ratios):.3f}–{max(ratios):.3f}×.\n\n'
    text+='''The 1.5× target was missed. Graph timings show essentially equal performance
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
'''
    assert proof['verdict']=='proved'
    text+=f"\nRecorded strict replay: {proof['proof']['check']['declarations']} declarations, axioms `{', '.join(proof['theorem']['axioms'])}`.\n"
    (D/'README.md').write_text(text)
if __name__=='__main__':main()
