#!/usr/bin/env bash
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
source "$here/../oss-ptx-simple-multicopy/env.sh"
case ${1:-test} in
 freeze) exec "$E5R_OSS_SCRATCH/venv/bin/python" "$here/freeze.py" ;;
 edit) exec python3 "$here/author-edit.py" ;;
 tuned) exec nvcc -O3 -arch=sm_86 --cubin "$here/tuned.cu" -o "$E5R_OSS_SCRATCH/cupy-index/tuned.cubin" ;;
 test|benchmark) exec "$E5R_OSS_SCRATCH/venv/bin/python" "$here/gpu.py" ;;
 edges) exec "$E5R_OSS_SCRATCH/venv/bin/python" "$here/edges.py" ;;
 negative) exec "$E5R_OSS_SCRATCH/venv/bin/python" "$here/negative.py" ;;
 *) exit 64 ;;
esac
