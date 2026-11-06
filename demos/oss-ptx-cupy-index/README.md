# Five practical CuPy indexing kernels

These are **measured direct PTX optimization attempts, not accepted proofs**.
Initial frozen-original frontend failures on initialized globals are retained
in `frontend.json`. The later aggregate ABI extension addresses those syntax
frontiers; matching aggregate proof domains and remaining executable types/ops
still need validation.
No original program was simplified to evade unsupported syntax.

Actual CuPy13.6.0 public APIs were invoked to capture optimized native NVRTC
cubin and generated CUDA source. Identical generated source/options compiled
for virtual compute86 supplies retained PTX. Native default output is a timing
baseline alongside original PTX and a separately authored matching tuned CUDA
comparator. Frozen source identity, license and options appear per kernel.
`PROTOCOL.md` specifies specialization domains, default128-thread launch and
shape/timing protocol. Upstream Python sources are byte-identical to the pinned
v13.6.0 commit. This batch does not support arbitrary widths/repetition lengths.

| Kernel | Source / definition line | Specialized parameter | Native/edit65536 | Native/edit1048576 |
|---|---|---|---:|---:|
| tri | cupy/_creation/matrix.py:66 `_tri_kernel` | M256 |1.115x|1.027x|
| resize | cupy/_manipulation/add_remove.py:90 `_resize_kernel` | source size256 |1.042x|1.023x|
| putmask | cupy/_indexing/insert.py:70 `_putmask_kernel` | values size256 |1.062x|1.050x|
| flat slice assignment | cupy/_indexing/iterate.py:146 `_flatiter_setitem_slice` | values size256 |1.066x|1.025x|
| flat slice read | cupy/_indexing/iterate.py:152 `_flatiter_getitem_slice` | step1 |0.995x|1.006x|

Only tri meets the predeclared1.10x threshold at65536; every kernel misses at1M.
This is a hot-buffer kernel experiment, not an application speedup. Large cases
approach bandwidth limits. All raw samples, variant order, exact hashes and
native/original/edited/tuned absolute latencies are in `results.json`.
310 CPU/API/native/PTX/edit/tuned differential and canary/input-preservation
checks plus2430 adversarial value/mask/launch/frame checks passed. Five concrete semantic mutations have GPU output witnesses in
`negatives.json`; **strict hash-rebound proof negatives are still pending**.

The first edit only replaced a parameter load with an immediate; its mostly
neutral data remain in `load-specialization-results.json`. The stronger edit
also directly replaces division/remainder CFGs with shift/mask instructions,
and removes step multiplies for slice reads. `author-edit.py` edits original
PTX directly; tuned CUDA never supplies candidate instructions.

Reproduce using `bash run.sh freeze`, `bash run.sh edit`, `bash run.sh tuned`,
`bash run.sh test`, `bash run.sh negative` from this directory after the common
sample environment is installed. Exact CuPy v13.6.0 source tag must be available
in the scratch checkout. GPU scripts use exclusive shared flock and refuse
foreign compute PIDs. Zero-size calls exercise upstream host dispatch and do
not launch invalid zero-thread grids. Additional `edges.py` checks cover zeros, allbits, signed extremes and alternating
values; allfalse/alltrue/alternating masks;32/128/256-thread blocks, grid1
stride loops and covering+tail launches. Tests use nonzero input/output offsets.

Remaining: full direct universal original/edited observable equivalence,
both-side safety/race freedom/termination/frame and strict independent replay,
axiom audit, and hash-rebound semantic negatives. Initialized global metadata
and aggregate parameter ABI require faithful frontend/exporter support. None
of these obligations is established by the measured tests.
