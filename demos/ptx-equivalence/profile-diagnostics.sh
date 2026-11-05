#!/usr/bin/env bash
# Invoke with flock /mnt/scratch/e5r-gpu-benchmark.lock bash this-file.
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
cd "$here/../.."
source demos/verified-packing/env.sh
out="$here/optimization/results"
scratch="$E5R_DEMO_SCRATCH/profile"
mkdir -p "$scratch"
metrics=gpu__time_duration.sum,dram__bytes_read.sum,dram__bytes_write.sum,dram__throughput.avg.pct_of_peak_sustained_elapsed,sm__warps_active.avg.pct_of_peak_sustained_active,lts__t_sector_hit_rate.pct,launch__registers_per_thread,launch__occupancy_limit_registers,launch__occupancy_limit_warps,launch__occupancy_limit_blocks
for name in original optimized matching; do
  for size in 1048576 134217728; do
    for cache in all none; do
      tag="$name-$size-$cache"
      ncu --target-processes application-only --kernel-name regex:unpack4\|matching \
        --launch-skip 10 --launch-count 1 --clock-control none --cache-control "$cache" \
        --metrics "$metrics" --csv --force-overwrite --export "$scratch/$tag" \
        --log-file "$out/profile-$tag.csv" \
        "$E5R_DEMO_SCRATCH/venv/bin/python" "$here/profile.py" "$name" "$size"
      if [[ "$size" == 134217728 && "$cache" == none ]]; then
        ncu --import "$scratch/$tag.ncu-rep" --page source --print-source sass \
          > "$out/jit-$name.sass"
      fi
    done
  done
done
