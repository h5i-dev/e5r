from pathlib import Path
import json
D=Path(__file__).resolve().parent
r=json.loads((D/'results/performance.json').read_text())
lines=['# Measurements','', 'CUDA event times per kernel in microseconds, median ± sample standard deviation over seven randomized-order repeats. Each repeat replays 256 preallocated graph nodes. All predeclared positive shapes are shown; n=0 is tested without timing. Original uses the exact unchanged normal CMake sm_86 cubin; edit and tuned use the same nvcc13.2 ptxas. Driver JIT variants are also retained in the raw dataset. Block512, ceiling-grid for tails. Actual default n=4194304 uses the original normal grid.','', '| n words | cache regime | original µs | direct edit µs | restrict CUDA µs | original/edit | edit vs tuned |','| ---: | :--- | ---: | ---: | ---: | ---: | ---: |']
for n,regime in dict.fromkeys((x['n'],x['regime']) for x in r['rows']):
 rows={x['implementation']:x for x in r['rows'] if (x['n'],x['regime'])==(n,regime)}
 def fmt(name):
  x=rows[name];return f"{x['median_us']:.3f} ± {x['stdev_us']:.3f}"
 a,b,c=[rows[k]['median_us'] for k in ('original_aot','edited_aot','tuned_aot')]
 lines.append(f'| {n:,} | {regime} | {fmt("original_aot")} | {fmt("edited_aot")} | {fmt("tuned_aot")} | {a/b:.3f}× | {c/b:.3f}× |')
lines+=['','**The predeclared default-shape 1.10× success target failed.** Small cache-hot inputs improve, but the default shape and larger streaming inputs regress. The edited PTX closely matches a compiler-produced restrict CUDA implementation. No win over this tuned comparator or sample end-to-end speedup is established.','', 'Hot means repeatedly reused buffers, not guaranteed full L2 residency. Rotating uses the actual ring size and total buffer bytes in performance.json; it exceeds L2 but is a bounded ring rather than an unbounded stream. Graph replay rotates within 64 nodes and repeats that graph. No GPU clocks or power settings were changed.','', '[Raw measurements](results/performance.json) include every sample, order, launch, ring size, compiler/driver/runtime and PTX hashes. The GPU compute-process list was checked before each sample while holding the common exclusive lock.','']
(D/'MEASUREMENTS.md').write_text('\n'.join(lines))
