#!/usr/bin/env bash
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
cd "$here/../.."
source "$here/env.sh"
mkdir -p "$E5R_DEMO_SCRATCH"/{cargo,lean,cache,downloads}
python3.12 -m venv "$E5R_DEMO_SCRATCH/venv"
"$E5R_DEMO_SCRATCH/venv/bin/pip" install -r "${E5R_DEMO_REQUIREMENTS:-$here/requirements.txt}"
cargo build --release -p e5r-verify
mkdir -p verification/ptx/.lake
if [[ ! -e verification/ptx/.lake/build ]]; then
  ln -s "$E5R_DEMO_SCRATCH/lean" verification/ptx/.lake/build
fi
cd verification/ptx
lake build Ptx proofcheck
