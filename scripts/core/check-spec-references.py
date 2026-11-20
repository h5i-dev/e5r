#!/usr/bin/env python3
"""Executable specifications against independent reference implementations.

A proof shows that the binary meets its specification; nothing but reading
shows that the specification means what was intended. Where a specification
is computable, this script evaluates it (the `spec-eval` executable, which
runs the specification's own Lean definitions) and compares the result with
a reference written independently here, in Python, from the description of
the function rather than from the Lean text:

  sum, sum2    Python's sum mod 2^64 (Examples.Sum.sumW, Demo.Sum.sumW;
               sum2's postcondition is sumW xs + sumW ys)
  cobs_decode  the reference decoder of examples/demo/test/cobs_test.py (the one the
               binaries are tested against under qemu) vs Demo.Cobs.report
  write_all    the bytes of a trace of writes to one fd vs NoCompiler.writtenTo
  hello        the message in examples/hello.c vs Examples.Hello.message, and
               its length vs the constant the specification uses

    python3 -I scripts/core/check-spec-references.py [N]     (needs lake; builds spec-eval)
"""
import importlib.util, os, random, re, subprocess, sys

ROOT = os.path.abspath(os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", ".."))
LEAN = os.path.join(ROOT, "lean")
M64 = 1 << 64


def load_cobs_reference():
    spec = importlib.util.spec_from_file_location("cobs_test", os.path.join(ROOT, "examples/demo/test/cobs_test.py"))
    mod = importlib.util.module_from_spec(spec)
    src = open(spec.origin).read()
    # Only the definitions: the module runs its test when executed as a script.
    exec(compile(src.split("\ndef main")[0], spec.origin, "exec"), mod.__dict__)
    return mod


def written_ref(fd, events):
    out = bytearray()
    for kind, f, data in events:
        if kind != "w" or f != fd:
            return None
        out += data
    return bytes(out)


def hello_message():
    src = open(os.path.join(ROOT, "examples/hello.c")).read()
    m = re.search(r'static const char msg\[\] = "((?:[^"\\]|\\.)*)";', src)
    return m.group(1).encode().decode("unicode_escape").encode("latin-1")


def main():
    n = int(sys.argv[1]) if len(sys.argv) > 1 else 3000
    rng = random.Random(20261120)
    cobs = load_cobs_reference()
    queries, expect, what = [], [], []

    def ask(q, e, w):
        queries.append(q); expect.append(e); what.append(w)

    # sum: edge values (0, 2^64 - 1, wrap-around) and random lists.
    words = [0, 1, M64 - 1, M64 - 2, 1 << 63, (1 << 63) - 1]
    for _ in range(n):
        k = rng.choice([0, 1, 2, rng.randrange(50)])
        xs = [rng.choice(words + [rng.randrange(M64)]) for _ in range(k)]
        s = sum(xs) % M64
        ask("sum " + " ".join(map(str, xs)), f"{s} {s}", f"sum {xs[:6]}")
    # cobs_decode: the same case generator as the qemu test.
    gen = cobs.cases(rng, n)
    for _ in range(n):
        buf = next(gen)
        (t, a, b), out = cobs.reference(buf)
        ask(f"cobs {buf.hex()}", f"{t} {a} {'-' if b is None else b} {out.hex()}", f"cobs {buf[:16].hex()}")
    # writtenTo: traces of writes, with a stray read, exit or other fd.
    for _ in range(n):
        fd = rng.choice([1, 2])
        evs = []
        for _ in range(rng.randrange(5)):
            r = rng.random()
            data = bytes(rng.randrange(256) for _ in range(rng.randrange(6)))
            if r < 0.85:
                evs.append(("w", fd, data))
            elif r < 0.9:
                evs.append(("w", 3 - fd, data))
            elif r < 0.95:
                evs.append(("r", fd, data))
            else:
                evs.append(("x", rng.randrange(3), b""))
        enc = " ".join(f"x:{f}" if k == "x" else f"{k}:{f}:{d.hex()}" for k, f, d in evs)
        ref = written_ref(fd, evs)
        ask(f"written {fd} {enc}".rstrip(), "none" if ref is None else ref.hex(), f"written {fd} {enc[:60]}")
    msg = hello_message()
    ask("message", msg.hex(), "hello message vs examples/hello.c")

    env = dict(os.environ)
    b = subprocess.run(["lake", "build", "spec-eval"], cwd=LEAN, capture_output=True, text=True)
    if b.returncode != 0:
        print(b.stdout[-3000:], b.stderr[-2000:]); print("FAIL spec-eval does not build"); return 1
    r = subprocess.run(["lake", "exe", "spec-eval"], cwd=LEAN, input="\n".join(queries) + "\n",
                       capture_output=True, text=True, env=env)
    got = r.stdout.split("\n")
    fail = 0
    counts = {}
    for i, (e, w) in enumerate(zip(expect, what)):
        g = got[i] if i < len(got) else "<missing>"
        key = w.split(" ")[0]
        counts.setdefault(key, [0, 0])[0] += 1
        if g != e:
            counts[key][1] += 1
            if counts[key][1] <= 3:
                print(f"FAIL {w}: spec gives {g[:120]!r}, reference {e[:120]!r}")
            fail = 1
    # The constant the specification uses for the message length.
    hello = open(os.path.join(LEAN, "Examples/Hello.lean")).read()
    lens = sorted(set(int(x) for x in re.findall(r"k = (\d+) ∧ c = 0", hello)))
    if lens != [len(msg)]:
        print(f"FAIL hello: the specification's full length is {lens}, the message in hello.c has {len(msg)} bytes"); fail = 1
    for k, (tot, bad) in counts.items():
        print(f"{'ok  ' if not bad else 'FAIL'} {k}: {tot - bad}/{tot} agree with the reference")
    return fail


sys.exit(main())
