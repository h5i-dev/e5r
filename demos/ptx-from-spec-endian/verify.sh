#!/usr/bin/env bash
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
export SCRATCH=${SCRATCH:-/mnt/scratch/e5r-ptx-from-spec}
project="$SCRATCH/lean-project"
proofdir="$SCRATCH/proof"
e5r="$SCRATCH/cargo-target/release/e5r"
export LEAN_NUM_THREADS=1
mkdir -p "$proofdir" "$SCRATCH/evidence"
"$e5r" ptx check "$here/endian_xor.ptx" --spec "$here/contract.json" \
  --proof "$here/E5rProof.lean" --project "$project" --keep "$proofdir" \
  --out "$SCRATCH/evidence/proof.json" --timeout 600 --memory-mb 2500
cp "$here/Audit.lean" "$proofdir/Audit.lean"
cd "$project"
export E5R_ENDIAN_PROOF_DIR="$proofdir"
lake env sh -c 'cd "$E5R_ENDIAN_PROOF_DIR" && LEAN_PATH="$LEAN_PATH:$E5R_ENDIAN_PROOF_DIR" lean Audit.lean' > "$SCRATCH/evidence/axiom-audit.json"
lake env sh -c 'cd "$E5R_ENDIAN_PROOF_DIR" && LEAN_PATH="$LEAN_PATH:$E5R_ENDIAN_PROOF_DIR" leanchecker E5rProof' > "$SCRATCH/evidence/leanchecker.log" 2>&1
lake env python3 "$here/record-replay.py" "$proofdir" "$SCRATCH/evidence/replay.json"
cp "$proofdir/E5rSpec.lean" "$SCRATCH/evidence/E5rSpec.lean"
python3 "$here/negative.py" --scratch "$SCRATCH"
echo "Proof, exact dependency audit, independent replay and negative controls passed. Evidence: $SCRATCH/evidence"
