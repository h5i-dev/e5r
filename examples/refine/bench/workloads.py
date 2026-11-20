#!/usr/bin/env python3
"""Deterministic inputs for the refinement benchmark's functions
(examples/refine/bench/README.md): what each task's A and B are run on in
the simulated performance oracle (`nocompiler sim`), to measure the
speed-up and to compare A's and B's outputs (a difference refutes B).

    python3 -I examples/refine/bench/workloads.py FUNCTION OUTDIR

Writes OUTDIR/<k>.bin for a few sizes, each the stdin of the function's
driver (examples/refine/targets/src/lib.rs, module `bench`): for the
counting functions the first byte is the needle; for memset the first
byte is the value; strlen's driver puts the terminator at the end.
"""
import os, random, sys

f, out = sys.argv[1], sys.argv[2]
os.makedirs(out, exist_ok=True)
rng = random.Random(20261120)
sizes = [0, 1, 7, 8, 15, 64, 1000, 4096, 60000]


def text(n):
    # Mixed ASCII and multi-byte UTF-8, for the character counter.
    s = "".join(rng.choice(["a", "b", " ", "\n", "é", "ü", "日", "本", "🙂"]) for _ in range(n))
    return s.encode()[:n]


for k, n in enumerate(sizes):
    if f in ("naive_count", "naive_count_32"):
        needle = rng.choice([0, 10, 32, 97])
        body = bytes(rng.choice([needle, rng.randrange(256)]) for _ in range(n))
        data = bytes([needle]) + body
    elif f == "naive_num_chars":
        data = text(n)
    elif f == "strlen":
        data = bytes(rng.randrange(1, 256) for _ in range(n))
    else:
        data = bytes(rng.randrange(256) for _ in range(n))
    open(os.path.join(out, f"{k:02d}-{n}.bin"), "wb").write(data)
