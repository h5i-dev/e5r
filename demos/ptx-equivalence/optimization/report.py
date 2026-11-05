from pathlib import Path
import csv,io,json,math,re
D=Path(__file__).resolve().parent

def main():
 data=json.loads((D/'results/diagnosis.json').read_text());rows=data['rows'];profiles=[]
 keys=['gpu__time_duration.sum','dram__bytes_read.sum','dram__bytes_write.sum','dram__throughput.avg.pct_of_peak_sustained_elapsed','sm__warps_active.avg.pct_of_peak_sustained_active','lts__t_sector_hit_rate.pct','launch__registers_per_thread','launch__occupancy_limit_registers','launch__occupancy_limit_warps','launch__occupancy_limit_blocks']
 for p in sorted((D/'results').glob('profile-*.csv')):
  records=list(csv.DictReader(io.StringIO(p.read_text())))
  r=next(r for r in records if r['ID']);units=records[0]
  def base(k):
   factor={'Kbyte':1e3,'Mbyte':1e6,'Gbyte':1e9,'us':1e3,'ms':1e6,'s':1e9}.get(units.get(k),1)
   return str(float(r[k])*factor)
  profiles.append(dict(run=p.stem,source_units={k:units[k] for k in keys},metrics={k:base(k) for k in keys}))
 def norm(p):
  return [re.sub(r'(\bBRA .*?)\s+0x[0-9a-f]+$',r'\1 ADDRESS',re.sub(r'\s+0\s*$','',re.sub(r'^0x[0-9a-f]+\s+','',s))).strip() for s in p.read_text().splitlines() if re.match(r'^0x[0-9a-f]+\s',s)]
 identical=norm(D/'results/jit-optimized.sass')==norm(D/'results/jit-matching.sass')
 (D/'results/summary.json').write_text(json.dumps(dict(loaded_edited_matches_tuned_cuda_instructions=identical,profiles=profiles),indent=2)+'\n')
 text='''# Unpack headroom diagnosis after the proved milestone

**Memory-bound at large sizes; edited PTX and matching CUDA have identical
loaded machine instructions**, after removing only absolute branch addresses.
No new faster PTX replacement is claimed. Original ccfec80 proof/timings are
retained unchanged. The subsequent user scope correction selected one concrete
integer-stencil edit rather than a broad variant/optimizer project.

All seven original shapes, blocks 64/128/256/512/1024 for original/edited/tuned
CUDA, and traffic baselines were measured using graph replay, seven repeats,
the shared flock and foreign-compute-PID checks. All measurements and variance
are in [diagnosis.json](results/diagnosis.json); all configurations, including
regressions, are retained. Output buffers are preallocated and functionality
is checked before timing. SASS/resource diagnosis is separate from timing.

## Fixed 256-thread comparison

| Output bytes | Original µs | Edited PTX µs | Matching CUDA µs | Broadcast R/W µs | Copy R/W µs | Write µs | Edited logical GB/s |
| ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
'''
 for n in sorted({r['output_bytes'] for r in rows}):
  a={r['name']:r for r in rows if r['output_bytes']==n and r['block']==256}
  text+=f'| {n:,} | '+' | '.join(f"{a[k]['median_us']:.4f}" for k in ['original','optimized','matching','broadcast_rw','copy_rw','write_only'])+f" | {a['optimized']['logical_GBps']:.1f} |\n"
 text+='''
Broadcast R/W has the exact traffic pattern x[i/8] -> y[i] with the arithmetic
removed. Logical unpack/broadcast bytes count output plus unique input once
(1.125× output size). Copy reads and writes the full output size (2×);
write-only counts output once. At 128MiB all deliver about 490–497 GB/s on
these definitions: removing unpack arithmetic offers essentially no gain.
At 1MiB, copy logical throughput exceeds DRAM bandwidth because the working
set fits L2; it must not be interpreted as off-chip bandwidth.

## Launch and cache regimes

| Output bytes | Best original block / µs | Best edited block / µs | Best CUDA block / µs | Edited 1024-thread / µs |
| ---: | ---: | ---: | ---: | ---: |
'''
 for n in sorted({r['output_bytes'] for r in rows}):
  cells=[]
  for name in ['original','optimized','matching']:
   a=min((r for r in rows if r['output_bytes']==n and r['name']==name),key=lambda r:r['median_us']);cells.append(f"{a['block']} / {a['median_us']:.4f}")
  q=next(r for r in rows if r['output_bytes']==n and r['name']=='optimized' and r['block']==1024)
  text+=f'| {n:,} | '+' | '.join(cells)+f" | {q['median_us']:.4f} |\n"
 text+='''
Best-per-shape entries describe the measured sweep, not a held-out optimized
policy. Fair CUDA receives the same sweep and gains the same benefits.
1024-thread launches visibly regress large cases; no result is discarded.
The 1MiB regime fits L2, while 16/128MiB outputs exceed it. Profiling separately
uses explicit cache-control all (cold replay) and none (uncontrolled/warm
replay), unmodified GPU clocks, after ten warmups. Profiler times are diagnostic,
not substitutes for the ordinary seven-repeat benchmark.

| Kernel / output / cache control | DRAM read MB | DRAM write MB | DRAM sustained % | Achieved occupancy % | L2 hit % |
| --- | ---: | ---: | ---: | ---: | ---: |
'''
 for p in profiles:
  v=p['metrics'];text+=f"| {p['run'].removeprefix('profile-')} | {float(v['dram__bytes_read.sum'])/1e6:.3f} | {float(v['dram__bytes_write.sum'])/1e6:.3f} | {float(v['dram__throughput.avg.pct_of_peak_sustained_elapsed']):.2f} | {float(v['sm__warps_active.avg.pct_of_peak_sustained_active']):.2f} | {float(v['lts__t_sector_hit_rate.pct']):.2f} |\n"
 text+='''
DRAM metrics include transaction/ECC effects and differ from logical payload.
NVIDIA's [profiling guide](https://docs.nvidia.com/nsight-compute/ProfilingGuide/)
defines these counters. Large-case DRAM utilization around 90% leaves little
credible room for a 1.5× improvement solely by removing arithmetic.

## Actual machine code and occupancy

[Loaded original](results/jit-original.sass), [edited](results/jit-optimized.sass),
[matching CUDA](results/jit-matching.sass) come from Nsight Compute reports for
the actual driver-JIT-loaded kernels. The edited/tuned CUDA instruction lists
are identical after absolute code addresses are normalized. The original's
spread uses four arithmetic instructions after nibble masking; the edit uses
IMAD plus LOP3, two instructions. Removing two instructions did not change the
large-case bottleneck. This is direct evidence against a PTX-specific win here.

CUDA function attributes and offline ptxas report 10 registers, no local/shared
memory or spills. Nsight launch allocation reports 16 registers/thread, with
register allocation allowing 16 blocks but warp capacity limiting a 256-thread
launch to six blocks/SM (48 warps, 1536 threads on sm_86). The difference is
consistent with register-allocation granularity, not evidence of different
loaded instructions. Achieved occupancy is reported above; it is not inferred
from register count. Raw resource/device attributes are in diagnosis.json.

Reproduce from repository root after the existing setup:

```bash
source demos/verified-packing/env.sh
"$E5R_DEMO_SCRATCH/venv/bin/python" demos/ptx-equivalence/diagnose.py
flock /mnt/scratch/e5r-gpu-benchmark.lock bash demos/ptx-equivalence/profile-diagnostics.sh
python3 demos/ptx-equivalence/optimization/report.py
```

NCU 2026.1.0 is required for counters/SASS extraction; unavailable privileges
must be reported as an unavailable check. No privileged driver setting was
changed. NVIDIA disassembly tool downloads are pinned with hashes in
../results/tool-downloads.json, used from scratch and not vendored.

The authorized stronger concrete demo is [stencil17](../../ptx-stencil/DOMAIN.md):
a frozen CUDA-generated program, directly edited using the established rolling
sum reuse technique, with explicit tails and a direct execution relation.
No optimizer, scheduling language or new optimization algorithm is introduced.
'''
 (D/'README.md').write_text(text)
if __name__=='__main__':main()
