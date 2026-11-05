# PTX authored from an independent endian conversion specification

This experiment implements `cupy.bitwise_xor(x.byteswap(), uint32(mask))` for disjoint, contiguous, one-dimensional native `uint32` arrays. The PTX was authored directly after freezing a byte-layout specification, before writing or compiling CUDA baselines. It is useful as a small fused endian conversion with an optional word mask. It makes no INT4 claim. The existing 32-bit map semantics can express this workload without extending the verifier.

The candidate exchanges adjacent bytes, exchanges the two halfwords, then applies XOR. Its JSON contract uses a separate four-byte expression; a Lean bit-layout theorem connects both computations to the independent source-bit permutation. This is a proof against a specification, with no reference PTX in the theorem.

See [SPEC.md](SPEC.md) for the frozen domain and sweep, [API-PIN.md](API-PIN.md) for an explicit dependency version correction, [PROVENANCE.txt](PROVENANCE.txt) for authorship/hashes, [DEPENDENCIES.md](DEPENDENCIES.md) for pins/licenses, and [REPORT.md](REPORT.md) for results and limitations.

Reproduce from the repository root on an NVIDIA sm_86 GPU, with Python 3.12, Rust, Lean v4.35.0 via elan, and CUDA 13.2 installed:

```sh
# Release builds, one Lean thread, Rust jobs=2, artifacts/dependencies on scratch.
demos/ptx-from-spec-endian/setup.sh
# CPU-only proof setup can instead use: setup.sh --proof-only

demos/ptx-from-spec-endian/verify.sh
# Proof JSON, exact dependency/axiom audit, independent leanchecker replay,
# and negative controls: /mnt/scratch/e5r-ptx-from-spec/evidence/

demos/ptx-from-spec-endian/run-gpu.sh --out /mnt/scratch/e5r-ptx-from-spec/new-gpu.json
demos/ptx-from-spec-endian/run-gpu.sh --wrapper-tests --out /mnt/scratch/e5r-ptx-from-spec/new-wrapper.json
python3 demos/ptx-from-spec-endian/report.py /mnt/scratch/e5r-ptx-from-spec/new-gpu.json
```

`SCRATCH` overrides the dedicated scratch directory. GPU commands acquire exclusive `/mnt/scratch/e5r-gpu-benchmark.lock`, check foreign compute PIDs before context creation, at every batch and after work, and abort if contention appears. A busy device is waited for in 15-second increments. Unrelated workloads need not honor the advisory lock; the PID checks are separate. No system GPU clock/power setting is modified.

The usable wrapper is [endian.py](endian.py). On the current CuPy stream:

```python
# Add demos/ptx-from-spec-endian to sys.path.
import cupy as cp
from endian import endian_xor
x = cp.arange(1025, dtype=cp.uint32)
y = endian_xor(x, 0x01020304)
# Or pass a preallocated, disjoint out= buffer of identical dtype/shape.
```

The host wrapper rejects inplace/overlapping outputs, unsupported layouts/dtypes and masks outside uint32. Caller-owned buffers must remain live, and concurrent writers must be excluded. The wrapper is tested empirically; the formal theorem is about the exact PTX under its launch/allocation preconditions. Startup, RawModule loading and allocations should occur before a caller's measured region.

Files in `results/` are committed evidence, not a substitute for rerunning the checker. `verify.sh` regenerates the statement directly from candidate PTX and contract, validates both SHA256 hashes against the supplied proof manifest, kernel-replays the proof declarations, audits exact transitive dependencies, independently replays the compiled module with `leanchecker`, and refuses realistic layout/index/tail mutants. Only an accepted `proved` result establishes the E5R claim.

Tests of ptxas output and driver JIT execution establish empirical correspondence on this A10G. Lean does not verify ptxas, driver JIT, SASS, CUDA, CuPy, host Python, the hardware or its runtime.
