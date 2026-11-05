#!/usr/bin/env python3
"""Called by verify.sh only after successful independent leanchecker replay."""
import hashlib
import json
from pathlib import Path
import shutil
import sys
import time

proofdir, output = map(Path, sys.argv[1:])
checker = Path(shutil.which('leanchecker')).resolve()
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
data = {
    'schema': 'e5r.endian.replay.v1',
    'date_utc': time.strftime('%Y-%m-%dT%H:%M:%SZ', time.gmtime()),
    'command': 'lake env sh -c \'cd "$E5R_ENDIAN_PROOF_DIR" && LEAN_PATH="$LEAN_PATH:$E5R_ENDIAN_PROOF_DIR" leanchecker E5rProof\'',
    'exit_code': 0,
    'checker_binary': str(checker),
    'checker_binary_sha256': sha(checker),
    'toolchain': Path('lean-toolchain').read_text().strip(),
    'modules': {name:sha(proofdir/name) for name in ['E5rSpec.lean','E5rSpec.olean','E5rProof.lean','E5rProof.olean']},
}
output.write_text(json.dumps(data,indent=2)+'\n')
