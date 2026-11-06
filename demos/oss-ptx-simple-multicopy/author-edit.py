"""Author the candidate directly from frozen PTX; no candidate CUDA compilation."""
from pathlib import Path
import hashlib,json
D=Path(__file__).resolve().parent
original=(D/'original.ptx').read_bytes()
assert hashlib.sha256(original).hexdigest()==json.loads((D/'freeze.json').read_text())['hashes']['original.ptx']
s=original.decode();start=s.index('\tand.b32');end=s.index('$L__BB0_6:')
s=s[:start]+'''// Direct PTX edit: under the declared nonalias, repeats=5 domain,
// five identical stores collapse to this one concrete load/add/store.
\tld.global.u32 %r22, [%rd1];
\tadd.s32 %r23, %r22, 1;
\tst.global.u32 [%rd2], %r23;
\n'''+s[end:]
(D/'edited.ptx').write_text(s)
