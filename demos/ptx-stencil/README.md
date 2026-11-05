# Direct concrete PTX stencil edit

This experiment freezes ordinary CUDA -> nvcc PTX, directly edits that PTX
to reuse a 17-word sliding window across four outputs, and compares concrete
program executions. The benchmark missed the performance target. The scalar
and paired-u64 variants regress over the seven-size sweep; all results are
retained in [RESULTS.md](RESULTS.md) and machine-readable JSON.

The scalar [edited.ptx](edited.ptx) has an accepted direct relational proof:
192 declarations replayed, transitive axioms exactly `propext`, `Quot.sound`,
`Classical.choice`. [results/proof.json](results/proof.json) binds both concrete
PTX artifacts and the complete domain. The paired-u64 experiment has GPU
tests, without a candidate proof.

The original is [original.cu](original.cu), compiled once using the exact
command/version in [freeze.json](freeze.json). [original.ptx](original.ptx)
is immutable. [edited.ptx](edited.ptx) and [edited64.ptx](edited64.ptx) were
edited directly; [matching.cu](matching.cu) supplies competent scalar and
paired-store CUDA comparators. No CUDA candidate source generated either
edited PTX. These files are project-authored, with no copied third-party
implementation. Python dependencies and their pins are shared with
[the unpack demo](../ptx-equivalence/requirements.txt).

[DOMAIN.md](DOMAIN.md) declares validity, alignment, nonaliasing, uint32
modular arithmetic, launch coverage and observations. Original and edited
launches may have different thread counts. The accepted scalar theorem universally
quantifies over valid parameters, arbitrary initial global/shared memory,
registers and predicates, and every pair of completed schedules. It compares
observable output words directly and preserves all external bytes. Each side
must have fault freedom, progress, bounded termination, race freedom and an
actual completed execution. It does not relate the programs through a shared
mathematical output specification. A continuation-parametric symbolic execution
summary of the concrete original is used to avoid repeatedly expanding its
full instruction trace.

Use the repository's Lean 4.35.0 and release Rust build. Heavy state goes into
`/mnt/scratch/e5r-ptx-demo`. From the repository root:

```sh
bash demos/ptx-stencil/run.sh setup
source demos/verified-packing/env.sh
cargo build --release -p e5r-cli
bash demos/ptx-stencil/run.sh proof
bash demos/ptx-stencil/run.sh test
bash demos/ptx-stencil/run.sh negative
bash demos/ptx-stencil/run.sh benchmark
bash demos/ptx-stencil/run.sh profile
bash demos/ptx-stencil/run.sh report
```

GPU commands acquire `/mnt/scratch/e5r-gpu-benchmark.lock` and refuse foreign
compute processes. Tests cover all n=0..20, block/tail boundaries, random and
adversarial uint32 inputs, and input/output offsets 0/4/8/12 bytes
as recorded in the test script. NumPy convolution is the independent oracle;
canaries check out-of-output writes and input preservation. Raw JSON records
hashes, launch geometry, seven timing repeats, variance and host/event times.
The retained earlier scalar and initial paired-store runs are separate files;
`performance.json` uses the final `__restrict__` CUDA comparators.

The formal model interprets parsed concrete PTX, including memory access and
launch semantics. The Rust parser/exporter, NVIDIA ptxas/driver JIT and hardware
are outside Lean's proof; executable agreement is empirical. Supplied-proof
acceptance must bind exact hashes, independently replay kernel declarations
and audit transitive axioms against `propext`, `Quot.sound`, `Classical.choice`.

## Coalesced follow-up experiments

[COALESCED.md](COALESCED.md) reports every shape and block size for the direct
striped, output-staged, input-tiled and two-output rolling edits, with matching
CUDA comparators and exact hardware transaction counts. The original scalar
and paired-store rolling edits process four outputs per thread; their proof
and timings remain separate. The additional candidates do not inherit that
proof. Input/output staging uses existing shared-memory/barrier semantics;
no shuffle or unsupported vector operation is silently trusted.

At 128 threads/block the two-output paired-store experiment measures 1.019x
all-shape geometric mean versus the original, driven by 1 MiB output
(3.641us original, 2.829us PTX, 3.042us matching CUDA). It still regresses at
16/128 MiB and misses the 1.5x target. Universal two-output proof acceptance
is pending; no verified improvement is claimed for these changed artifacts.

```sh
bash demos/ptx-stencil/run.sh coalesced test
bash demos/ptx-stencil/run.sh coalesced benchmark
bash demos/ptx-stencil/run.sh coalesced profile
bash demos/ptx-stencil/run.sh tiled test
bash demos/ptx-stencil/run.sh tiled benchmark
bash demos/ptx-stencil/run.sh tiled profile
bash demos/ptx-stencil/run.sh paired2 test
bash demos/ptx-stencil/run.sh paired2 benchmark
bash demos/ptx-stencil/run.sh paired2 profile
bash demos/ptx-stencil/run.sh coalesced report
```
