"""Reproduce packing tables without rerunning GPU measurements."""
from pathlib import Path
import json,math
D=Path(__file__).resolve().parent

def main():
 data=json.loads((D/'results/performance.json').read_text());rows=data['rows']
 text='''# Directly authored packing PTX: preserved specification experiment

The primary complete result here is **unpack**: directly authored PTX,
an independent byte/bit specification, an accepted universal Lean proof of
functional correctness, memory safety, race freedom and termination, and
GPU correspondence/performance measurements. This is complementary to the
[direct CUDA-PTX equivalence demonstration](../ptx-equivalence/README.md),
whose main theorem uses a direct relation between concrete programs.

[Scope and frozen measurement plan](SPEC.md) · [unpack proof](unpack.lean) ·
[accepted replay](results/unpack-proof.json) · [raw measurements](results/performance.json).

## Proof and implementation scope

Little bit order, contiguous uint8, aligned/disjoint nonwrapping allocations.
Unpack requires input length divisible by 4. One thread writes four 0/1 output
bytes; eight threads may read the same input word. n is output words,
n divisible by 8, n <= G*B <= 2^31. The theorem quantifies over all byte values,
initial memory/registers/predicates and valid launches, every interleaving,
with no faults, progress, finite bounded steps, race freedom, existence of a
completed run and preservation of bytes outside output. Empty arrays are
included; the host wrapper skips their launch. This is a subset of CuPy's
API, not support for arbitrary tails, axes, strides, bit orders or dtypes.
The wrapper explicitly rejects unsupported layouts/tails.

`Packing.Spec.bit` states each output bit from the original input memory;
it does not transcribe the candidate arithmetic. `Spec.correct_of` lifts
candidate-specific symbolic execution to the complete grid. Strict replay
accepts only propext, Quot.sound and Classical.choice. Parser/export and
NVIDIA ptxas/JIT/hardware correspondence remain outside the theorem.

**Pack and threshold-fusion are experimental, not verified.** Their GPU tests
and timing rows are retained, including initial tuning results. `pack.lean`
and `threshold.lean` are unfinished development scripts with outstanding
goals. A long-running pack proof was stopped during recovery; no accepted
candidate proof or safety claim is made for either kernel. The generic
packing contract compiling does not constitute a proof of these candidates.

The optional TorchAO split-half INT4 candidate has an accepted map32 **word
expression** proof in results/torchao-proof.json. Its independent byte-layout
corollary and real TorchAO differential/performance tests were not completed.
It is not advertised as a finished TorchAO-compatible demonstration. The
frozen actual operator/layout and exact remaining obligations are in SPEC.md.
Optional Torch 2.9.1+cu128 was installed only in scratch; it is not needed for
the complete unpack or relational demonstration.

## Measurements

CuPy 13.6.0 is the actual pinned OSS baseline. Sources/commits/license and the
independent operator definition are in SPEC.md. All selected shapes are
reported below. Device graph timing is primary, since plain Python enqueue
loops expose launch gaps. Seven repeats, preallocated outputs, matching
streams, CUDA-event synchronization; all samples, variance, min/max,
synchronized host times and public-API allocation-inclusive times are in raw
JSON. The GPU benchmark held the common exclusive flock and sampled foreign
compute PIDs throughout. CuPy pack includes its required output zero fill;
threshold CuPy includes a separate predicate pass. Fusion gains therefore
are reported separately from standalone unpack/pack.

'''
 for op in ['unpack','pack','threshold']:
  text+=f"### {op} ({'proved' if op=='unpack' else 'experimental, unproved'})\n\n"
  implementations=['ptx','cupy_preallocated','cuda_grid_stride','cuda_grouped']+(['cuda_word'] if op=='unpack' else [])
  text+='| Unpacked bytes | '+' | '.join(implementations)+' | CuPy/PTX |\n'
  text+='| ---: | '+' | '.join('---:' for _ in implementations)+' | ---: |\n'
  selected=[r for r in rows if r['operation']==op and r['graph']]
  ns=sorted({r['unpacked_bytes'] for r in selected});ratios={k:[] for k in implementations[1:]}
  for n in ns:
   a={r['implementation']:r['median_us'] for r in selected if r['unpacked_bytes']==n}
   text+=f'| {n:,} | '+' | '.join(f'{a[k]:.4f}' for k in implementations)+f" | {a['cupy_preallocated']/a['ptx']:.2f}× |\n"
   if n>=65536:
    for k in ratios:ratios[k].append(a[k]/a['ptx'])
  text+='\nDevice microseconds, medians. Predeclared summary over the four sizes >=65,536 bytes: '
  text+='; '.join(f"{k}/PTX **{math.exp(sum(map(math.log,v))/len(v)):.2f}×** (range {min(v):.2f}–{max(v):.2f}×)" for k,v in ratios.items())+'.\n\n'
 text+='''Optimized matching CUDA removes much of the apparent advantage. The main
unpack benefit against CuPy is output-word ownership instead of a byte per
thread; it is an algorithm/thread-layout gain, not evidence of an inherently
PTX-only speedup. Pack misses the 1.5× target across the larger sizes.
Threshold fusion benefits against two-pass CuPy are substantial but remain
experimental until a candidate proof is accepted.

## Reproduction

```bash
bash demos/verified-packing/setup.sh
source demos/verified-packing/env.sh
"$E5R_VERIFY" ptx check demos/verified-packing/unpack.ptx \\
  --spec demos/verified-packing/unpack.json \\
  --proof demos/verified-packing/unpack.lean \\
  --keep "$E5R_DEMO_SCRATCH/accepted/unpack" \\
  --timeout 600 --memory-mb 4096 \\
  --out demos/verified-packing/results/unpack-proof.json
"$E5R_DEMO_SCRATCH/venv/bin/python" demos/verified-packing/test_gpu.py
"$E5R_DEMO_SCRATCH/venv/bin/python" demos/verified-packing/benchmark.py
python3 demos/verified-packing/report.py
```

The benchmark includes experimental pack/fusion rows explicitly labeled
above. `runtime.Packing.run` validates the selected subset, while raw
prevalidated launches are timed for equal Python overhead. The independent
604-case CPU/CuPy comparison includes every byte value, one-hot patterns,
threshold extrema, random data, zero lengths and block boundaries.
GPU tests complement the unpack theorem; they do not prove pack/fusion.

All large state lives under /mnt/scratch/e5r-ptx-demo. Dependencies are pinned
in requirements.txt. Upstream CuPy is MIT; TorchAO is BSD-3-Clause, used only
as a pinned operator reference in this unfinished follow-up. No third-party
implementation is vendored. All candidate PTX is directly authored by author.py;
CUDA baseline.cu is independently written. Initial kernels/results are
retained and have no accepted proof binding.
'''
 (D/'README.md').write_text(text)
if __name__=='__main__':main()
