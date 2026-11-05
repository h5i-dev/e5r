"""Verify immutable source/PTX provenance without recompiling either artifact."""
from pathlib import Path
import hashlib,json
D=Path(__file__).resolve().parent
manifest=json.loads((D/'freeze.json').read_text())
for name,expected in manifest['sha256'].items():
    assert hashlib.sha256((D/name).read_bytes()).hexdigest()==expected,name
print('Frozen CUDA source and emitted original PTX hashes match.')
