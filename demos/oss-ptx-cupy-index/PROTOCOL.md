The five kernels are distinct actual CuPy APIs from v13.6.0, MIT, commit
25e552d5d679dcdc6f7cc3d81310a9b265463137. Frozen upstream Python files were
byte checked against the installed13.6.0 package. `freeze.py` invokes the actual
public APIs with default dispatch and captures native optimized NVRTC output;
PTX retention recompiles the identical source and options with virtual
compute86 replacing sm86. No upstream kernel body changes. Normal native cubin
and the retained original PTX are both timing comparators. Direct PTX edits
replace a single runtime parameter load with a constant. This makes specialization
explicit: tri has256 columns; resize and putmask use256 input/values; flat slice
assignment uses256 values; flat slice reads use step1. These are practical regular
matrix and repeating-pattern workloads. General parameters are outside the domain.

Before measurement: success target is1.10x median kernel latency at65536 and1048576
outputs. Sweep zero/tails and1,31,255,256,257,4096,65536,1048576,4194304 elements;
tri sweeps row counts1,31,256,4096,16384. Contiguous int32 buffers, disjoint data
and valid nonoverflowing pointers, output count<2^29. Graph64 launches,20 warmups,
7 randomized-order repeats with CUDA events and preallocated buffers. Hot-buffer
kernel timing only. Independent NumPy and actual upstream public API comparisons,
nonzero offsets and canary/input-preservation checks precede timing. Shared flock
and foreign PID check apply throughout. Matching tuned CUDA separately authored
and compiled nvcc -O3 -arch=sm_86; never used to generate the candidate. Wins over
generic OSS may be specialization wins; matching tuned CUDA can erase them.

Universal direct equivalence, safety, race freedom, termination and frame proofs
remain obligations. GPU tests do not establish proof. NVRTC/nvcc/ptxas/driver/
GPU and exporter correspondence lie outside the Lean trust boundary.
