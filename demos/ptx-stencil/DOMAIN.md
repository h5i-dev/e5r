# Concrete stencil PTX edit, frozen scope

Original CUDA and emitted PTX are frozen in freeze.json before candidate
editing. nvcc 13.2.51, -O3 -arch=sm_86 --ptx. The target is an ordinary 17-tap
one-dimensional uint32 box stencil. Addition is modulo 2^32, exactly.

Known edit: process four adjacent outputs per thread and reuse the running
window sum by subtracting the departing value and adding the arriving value.
This initial edit uses established rolling sums. Novel concrete instruction/layout/
work-assignment improvements are also authorized; a general optimizer or
scheduling-language research project is not the deliverable.
Candidate PTX is edited directly, never compiled from candidate CUDA.
A competent CUDA comparator implements the same known reuse technique.

Domain: arbitrary uint32 n, n <= G*B <= 2^31. Input has n+16 aligned u32
words; output n aligned u32 words. Allocations are disjoint, end addresses
do not wrap, and base alignment is only four bytes. Arbitrary input/global
memory and arbitrary initial register/predicate/shared-memory values. No
restriction that n is divisible by four; every final group is guarded.
A scalar global-only PTX edit avoids new shared/async/warp/vector semantics.

The original and edited launch shapes may differ explicitly: original
requires n <= G0*B0; candidate requires ceil(n/4) <= G1*B1. Both products
are <= 2^31. Comparison is over the same inputs and parameter valuation.
Prove direct equality of final observable output uint32 words for every pair
of completed schedules, plus preservation of all bytes outside the output.
Both programs must separately prove no faults, progress, bounded steps,
race freedom and existence of a completed execution. No common mathematical
output specification may mediate the main equivalence proof. Concrete solo
trace normalization, arithmetic relations and direct grid lifting are allowed.

Measure the same output-byte sweep 32,256,4096,65536,1048576,16777216,134217728,
plus boundary correctness tests including n=0..20, all tail remainders and
block boundaries. Shared GPU flock and foreign-PID checks always. Original,
direct PTX and tuned matching CUDA, preallocated buffers and graph/event
measurements. Report every shape and geometric means, misses and regressions.
No performance/proof acceptance claims before execution and strict replay.
Compiler/JIT/hardware correspondence remains empirical.

## Accepted two-output follow-up

`scalar2.ptx` and `paired2.ptx` assign outputs2*g and2*g+1 to edited threadg.
Their supplied-proof contract is `equivalence-stencil17-pair2` and the direct
statement is `StencilPair.Spec.Equivalent`. The original remains byte-for-byte
frozen. Replace edited coverage ceil(n/4)<=G1*B1 above with ceil(n/2)<=G1*B1;
all other allocation, n<=2^31, initial-memory, alignment and launch assumptions
remain. An odd final output uses a scalar store. The paired path additionally
checks actual output-address alignment modulo8 before each u64 store; failure
uses scalar stores. No stronger base alignment or divisibility assumption.
The current proofs and all-shape results are linked from README.md.
