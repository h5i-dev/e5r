# CuPy packing: direct PTX exploration

Two distinct practical kernels, packbits and unpackbits, from CuPy13.6.0 commit
25e552d5d679dcdc6f7cc3d81310a9b265463137, MIT. Default big-bitorder uint8 API
is captured through its normal ElementwiseKernel NVRTC dispatch. `packing.py`
is byte-identical to that upstream tag. `freeze.json` records generated source,
normal native cubin, optimized retained PTX and compiler options before editing.
PTX retention changes sm86 to compute86; normal native cubin is kept as the
ordinary and strongest applicable upstream baseline. No upstream body changes.

`author-edit.py` edits the exact frozen PTX. Packbits eliminates per-bit bounds
branches on the explicit full-byte domain and intermediate output stores.
Those stores do not reduce compulsory unique DRAM bytes; measured benefits
reflect branch/instruction work. Unpackbits expands one input byte per thread
to an aligned64bit output store, removing repeated byte loads and indexing.
It uses fewer threads; identical block128 with grid ceil(input bytes/128).
Both retain the ABI. Packbits covers input length multiple8 below2^31, contiguous
nonaliasing buffers, stride1 output. Unpackbits covers contiguous nonaliasing
uint8 arrays with output8-aligned, output length8*input length below2^31.
Zero-length launches return. Packbits other tails use ordinary upstream fallback,
not this specialized candidate; they are not timed as optimization results.

GPU tests compare original PTX, normal native cubin, edit and matching tuned
CUDA to independent NumPy pack/unpack with random/zero/all-byte patterns,
canaries and input preservation. Shared exclusive GPU lock and foreign process
checks are mandatory. Seven randomized-order repeats use32-node CUDA graphs,
20 warmups, preallocation, CUDA events and raw per-shape samples. `results.json`
is the initial hot run; `results-hot.json` and `results-rotating.json` are current
runs with exact artifact hashes. Rotating buffers target128MiB with at most16
buffers; actual ring bytes are reported. Small shapes retain one buffer.
Only kernel latency is measured. Compilation, allocation, transfer and zeroing
are consistently excluded. Output reuse is valid here because ORing identical
pack results is idempotent; the actual API initially zeros its output.

Initial hot run: unpackbits2.35x at65536 input bytes,2.37x at4194304 and2.38x
at16777216 vs normal native CuPy. Matching tuned CUDA matches or beats PTX.
Packbits1.15x at65536,1.40x at4194304,1.00x at16777216. No API/application
speedup or advantage over matching tuned CUDA claimed.

**No accepted universal equivalence proof yet.** `frontend.txt` retains the
actual original parser error at module-global initialization. Aggregate CArray
parameter layout and offset loads also need faithful semantics. Unpackbits
needs a direct relation across thread grouping/launches; no common operator
spec can replace that. Safety, race freedom, termination, frame, strict replay,
axiom audit and rebound semantic proof negatives remain open. GPU tests are
not a proof. NVIDIA compilation, JIT, hardware and Rust exporter remain outside
the Lean trust boundary.

Run from repository root:

```sh
source demos/oss-ptx-simple-multicopy/env.sh
# Freeze only with a fresh CUPY_CACHE_DIR so the API compiler is observed.
CUPY_CACHE_DIR="$E5R_OSS_SCRATCH/packing-cache-new" "$E5R_OSS_SCRATCH/venv/bin/python" demos/oss-ptx-cupy-packing/freeze.py
python3 demos/oss-ptx-cupy-packing/author-edit.py
"$E5R_OSS_SCRATCH/venv/bin/python" demos/oss-ptx-cupy-packing/gpu.py
OSS_PACKING_REGIME=rotating "$E5R_OSS_SCRATCH/venv/bin/python" demos/oss-ptx-cupy-packing/gpu.py
```
