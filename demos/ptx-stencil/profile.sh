#!/usr/bin/env bash
# Run under the shared host flock.
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
cd "$here/../.."
source demos/verified-packing/env.sh
scratch="$E5R_DEMO_SCRATCH/stencil-profile"
mkdir -p "$scratch"
metrics=gpu__time_duration.sum,dram__bytes_read.sum,dram__bytes_write.sum,dram__throughput.avg.pct_of_peak_sustained_elapsed,sm__warps_active.avg.pct_of_peak_sustained_active,l1tex__t_sectors_pipe_lsu_mem_global_op_st.sum,l1tex__t_sectors_pipe_lsu_mem_global_op_ld.sum,smsp__inst_executed.sum,launch__registers_per_thread
names=(original edited edited64 matching17 matching64)
prefix=
if [[ "${1:-}" == coalesced ]]; then
 names=(original striped staged striped17 staged17 matching64)
 prefix=coalesced-
 metrics+=,l1tex__data_bank_conflicts_pipe_lsu_mem_shared_op_st.sum,l1tex__data_bank_conflicts_pipe_lsu_mem_shared_op_ld.sum
fi
if [[ "${1:-}" == tiled ]]; then
 names=(original tiled tiled4 tiled17 tiled417)
 prefix=tiled-
 metrics+=,l1tex__data_bank_conflicts_pipe_lsu_mem_shared_op_st.sum,l1tex__data_bank_conflicts_pipe_lsu_mem_shared_op_ld.sum
fi
if [[ "${1:-}" == paired2 ]]; then
 names=(original paired2 scalar2 paired2_cuda scalar2_cuda)
 prefix=paired2-
fi
for name in "${names[@]}"; do
 ncu --target-processes application-only --kernel-name regex:stencil17\|matching\|striped17\|staged17\|tiled\|paired2_cuda\|scalar2_cuda \
  --launch-skip 10 --launch-count 1 --cache-control none --clock-control none \
  --metrics "$metrics" --force-overwrite --export "$scratch/$prefix$name" \
  --log-file "$scratch/$prefix$name.log" "$E5R_DEMO_SCRATCH/venv/bin/python" "$here/profile.py" "$name"
 ncu --import "$scratch/$prefix$name.ncu-rep" --page raw --csv --print-units base > "$here/results/profile-$prefix$name.csv"
done
