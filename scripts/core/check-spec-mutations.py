#!/usr/bin/env python3
"""Spec mutation tests: a specification that a proof still satisfies after
it has been altered was not saying what we thought.

For each mutation below, change one piece of one specification in a copy of
lean/ (a constant in the postcondition, a result register, a region, a
conjunct of the precondition) and require every proof of that specification
to FAIL against the altered one. Then require the unaltered copy to pass.

The code-side counterpart is scripts/core/check-proof-controls.sh (mutate the
binary, keep the spec). The two answer different questions: there, "does the
proof depend on the code?"; here, "does the proof establish the spec, and
does the spec pin down the behaviour?".

What a surviving mutation means, by kind:
  post  the postcondition does not determine that part of the result: too weak.
  pre   the precondition has a conjunct the proof never needs: not wrong, but
        the theorem could be stronger (drop the conjunct and re-prove).
  frame a region could be smaller: the permission is wider than the code needs.
A surviving mutation is reported as FAIL either way; decide which it is and
fix the spec or the list, never hide it.

A conjunct of a precondition is dropped by replacing it with `True` in
place, so that the proof's shape (its `rintro` pattern) is unchanged and a
failure means the proof used the fact.

A mutation is only evidence if the altered spec is itself well formed: if
Lean reports an error inside a `def` or `structure` (the spec, not the
proof), the mutation is reported as INVALID.

    python3 -I scripts/core/check-spec-mutations.py [--only SUBSTR] [--skip SUBSTR] [--list]

Needs lake (elan) on PATH. Wrap it as the other Lean scripts are (bounded
memory) on a shared machine.
"""
import os, re, shutil, subprocess, sys, tempfile, time

ROOT = os.path.abspath(os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", ".."))

# (file under lean/, modules whose proofs must fail, kind, name, old, new)
# `old` must occur exactly once in the file.
MUTATIONS = [
    # u64 sum(const u64 *a, u64 n), lean/Examples/Sum.lean
    ("Examples/Sum.lean", ["Examples.Sum"], "post", "sum-post-plus-one",
     "post := fun ⟨_, xs⟩ _ s' => s'.reg Reg.a0 = sumW xs",
     "post := fun ⟨_, xs⟩ _ s' => s'.reg Reg.a0 = sumW xs + 1"),
    ("Examples/Sum.lean", ["Examples.Sum"], "post", "sum-result-in-a1",
     "post := fun ⟨_, xs⟩ _ s' => s'.reg Reg.a0 = sumW xs",
     "post := fun ⟨_, xs⟩ _ s' => s'.reg Reg.a1 = sumW xs"),
    ("Examples/Sum.lean", ["Examples.Sum"], "post", "sum-fold-starts-at-1",
     "def sumW (xs : List Word) : Word := xs.foldl (· + ·) 0",
     "def sumW (xs : List Word) : Word := xs.foldl (· + ·) 1"),
    ("Examples/Sum.lean", ["Examples.Sum"], "post", "sum-fold-is-xor",
     "def sumW (xs : List Word) : Word := xs.foldl (· + ·) 0",
     "def sumW (xs : List Word) : Word := xs.foldl (· ^^^ ·) 0"),
    ("Examples/Sum.lean", ["Examples.Sum"], "frame", "sum-reads-nothing",
     "reads := fun ⟨a, xs⟩ _ => [arrRegion a xs]",
     "reads := fun ⟨a, xs⟩ _ => []"),
    ("Examples/Sum.lean", ["Examples.Sum"], "frame", "sum-reads-one-word-short",
     "reads := fun ⟨a, xs⟩ _ => [arrRegion a xs]",
     "reads := fun ⟨a, xs⟩ _ => [⟨a, 8 * xs.length - 8⟩]"),
    ("Examples/Sum.lean", ["Examples.Sum"], "pre", "sum-drops-alignment",
     "aligned a 8 ∧ arr64 s.mem a xs", "True ∧ arr64 s.mem a xs"),
    ("Examples/Sum.lean", ["Examples.Sum"], "pre", "sum-drops-contents",
     "aligned a 8 ∧ arr64 s.mem a xs", "aligned a 8 ∧ True"),
    ("Examples/Sum.lean", ["Examples.Sum"], "pre", "sum-drops-length-bound",
     "8 * xs.length < 2^64 ∧ aligned a 8", "True ∧ aligned a 8"),
    ("Examples/Sum.lean", ["Examples.Sum"], "pre", "sum-length-off-by-one",
     "s.reg Reg.a1 = BitVec.ofNat 64 xs.length ∧\n    8 * xs.length",
     "s.reg Reg.a1 = BitVec.ofNat 64 (xs.length + 1) ∧\n    8 * xs.length"),
    # sum2 = sum(a, n) + sum(b, m), lean/Examples/Sum2.lean
    ("Examples/Sum2.lean", ["Examples.Sum2"], "post", "sum2-adds-xs-twice",
     "s'.reg Reg.a0 = sumW xs + sumW ys", "s'.reg Reg.a0 = sumW xs + sumW xs"),
    ("Examples/Sum2.lean", ["Examples.Sum2"], "frame", "sum2-stack-16",
     "stack := 32", "stack := 16"),
    ("Examples/Sum2.lean", ["Examples.Sum2"], "frame", "sum2-reads-only-a",
     "reads := fun ⟨a, xs, b, ys⟩ _ => [arrRegion a xs, arrRegion b ys]",
     "reads := fun ⟨a, xs, b, ys⟩ _ => [arrRegion a xs]"),
    ("Examples/Sum2.lean", ["Examples.Sum2"], "pre", "sum2-b-may-overlap-the-frame",
     "(∀ x, (arrRegion b ys).mem x → ¬ (Spec.stackRegion s 32).mem x)", "True"),
    # write_all and hello, lean/Examples/Hello.lean
    ("Examples/Hello.lean", ["Examples.Hello"], "post", "write_all-success-returns-1",
     "(k = n ∧ r = 0)", "(k = n ∧ r = 1)"),
    ("Examples/Hello.lean", ["Examples.Hello"], "post", "write_all-error-range-4094",
     "1 ≤ e ∧ e ≤ 4095 ∧ r = -(BitVec.ofNat 64 e)", "1 ≤ e ∧ e ≤ 4094 ∧ r = -(BitVec.ofNat 64 e)"),
    ("Examples/Hello.lean", ["Examples.Hello"], "post", "write_all-writes-one-more",
     "writtenTo fd evs = some (readBytes s.mem buf k) ∧ Outcome",
     "writtenTo fd evs = some (readBytes s.mem buf (k + 1)) ∧ Outcome"),
    ("Examples/Hello.lean", ["Examples.Hello"], "post", "hello-success-status-1",
     "some (message.take k) ∧ ((k = 11 ∧ c = 0)", "some (message.take k) ∧ ((k = 11 ∧ c = 1)"),
    ("Examples/Hello.lean", ["Examples.Hello"], "post", "hello-writes-to-fd-2",
     "writtenTo 1 evs = some (message.take k)", "writtenTo 2 evs = some (message.take k)"),
    ("Examples/Hello.lean", ["Examples.Hello"], "frame", "hello-stack-8",
     "stack := 16", "stack := 8"),
    # The demo: one spec, two binaries (examples/demo/README.md)
    ("Demo/SumSpec.lean", ["Demo.SumB", "Demo.SumA"], "post", "demo-sum-post-plus-one",
     "post := fun ⟨_, xs⟩ _ s' => s'.reg Reg.a0 = sumW xs",
     "post := fun ⟨_, xs⟩ _ s' => s'.reg Reg.a0 = sumW xs + 1"),
    ("Demo/SumSpec.lean", ["Demo.SumB", "Demo.SumA"], "frame", "demo-sum-reads-nothing",
     "reads := fun ⟨a, xs⟩ _ => [arrRegion a xs]", "reads := fun ⟨a, xs⟩ _ => []"),
    ("Demo/SumSpec.lean", ["Demo.SumB", "Demo.SumA"], "pre", "demo-sum-drops-alignment",
     "aligned a 8 ∧ arr64 s.mem a xs", "True ∧ arr64 s.mem a xs"),
    ("Demo/CobsSpec.lean", ["Demo.CobsB", "Demo.CobsA"], "post", "demo-cobs-tag-swapped",
     "(if d.1 then 0 else 1, if d.1 then n else 1,", "(if d.1 then 1 else 0, if d.1 then n else 1,"),
    ("Demo/CobsSpec.lean", ["Demo.CobsB", "Demo.CobsA"], "post", "demo-cobs-error-a-is-0",
     "(if d.1 then 0 else 1, if d.1 then n else 1,", "(if d.1 then 0 else 1, if d.1 then n else 0,"),
    ("Demo/CobsSpec.lean", ["Demo.CobsB", "Demo.CobsA"], "post", "demo-cobs-decoded-count-plus-one",
     "some d.2.length)", "some (d.2.length + 1))"),
    ("Demo/CobsSpec.lean", ["Demo.CobsB", "Demo.CobsA"], "post", "demo-cobs-no-zero-after-254",
     "if c ≠ 255 ∧ e < n then [0] else []", "if c ≠ 254 ∧ e < n then [0] else []"),
    ("Demo/CobsSpec.lean", ["Demo.CobsB", "Demo.CobsA"], "post", "demo-cobs-empty-a-is-1",
     "if buf = [] then ((1, 0, none), buf)", "if buf = [] then ((1, 1, none), buf)"),
    ("Demo/CobsSpec.lean", ["Demo.CobsB", "Demo.CobsA"], "post", "demo-cobs-unwritten-b-is-zero",
     "| none => read64 s'.mem (r + 16) = read64 s.mem (r + 16)",
     "| none => read64 s'.mem (r + 16) = 0"),
    ("Demo/CobsSpec.lean", ["Demo.CobsB", "Demo.CobsA"], "frame", "demo-cobs-writes-16-of-24",
     "[⟨buf, orig.length⟩, ⟨r, 24⟩]", "[⟨buf, orig.length⟩, ⟨r, 16⟩]"),
    ("Demo/CobsSpec.lean", ["Demo.CobsB", "Demo.CobsA"], "pre", "demo-cobs-drops-slot-alignment",
     "aligned r 8 ∧\n", "True ∧\n"),
    ("Demo/CobsSpec.lean", ["Demo.CobsB", "Demo.CobsA"], "pre", "demo-cobs-drops-disjointness",
     "aligned r 8 ∧\n    Region.Disjoint ⟨r, 24⟩ ⟨buf, orig.length⟩", "aligned r 8 ∧\n    True"),
    ("Demo/CobsSpec.lean", ["Demo.CobsB", "Demo.CobsA"], "pre", "demo-cobs-drops-length-bound",
     "orig.length < 2 ^ 63 ∧ readBytes", "True ∧ readBytes"),
]

DECL = re.compile(r"^(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+|noncomputable\s+)*"
                  r"(def|abbrev|structure|inductive|instance|theorem|lemma|example)\b")
ERR = re.compile(r"error: ([\w/.]+\.lean):(\d+):\d+")


def decl_at(lines, n):
    """The kind and line of the top-level declaration containing line n (1-based)."""
    for i in range(n - 1, -1, -1):
        m = DECL.match(lines[i])
        if m:
            return m.group(1), i + 1
    return None, 0


def lake_build(work, mod, log):
    r = subprocess.run(["lake", "build", mod], cwd=os.path.join(work, "lean"),
                       stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True,
                       timeout=int(os.environ.get("SPEC_MUTATION_TIMEOUT", "900")))
    with open(log, "w") as f:
        f.write(r.stdout)
    return r.returncode == 0, r.stdout


def main():
    only = None
    if "--only" in sys.argv:
        only = sys.argv[sys.argv.index("--only") + 1]
    skip = sys.argv[sys.argv.index("--skip") + 1] if "--skip" in sys.argv else None
    muts = [m for m in MUTATIONS if (only is None or only in m[3] or only in m[0])
            and (skip is None or not (skip in m[3] or skip in m[0]))]
    if "--list" in sys.argv:
        for f, mods, kind, name, _, _ in muts:
            print(f"{kind:5} {name:40} {f} -> {' '.join(mods)}")
        return 0
    work = tempfile.mkdtemp(prefix="spec-mut-")
    fail = 0
    try:
        shutil.copytree(os.path.join(ROOT, "lean"), os.path.join(work, "lean"), symlinks=True)
        log = os.path.join(work, "log")
        # Build the unaltered copy first: every later build is then incremental.
        mods_all = sorted({m for x in muts for m in x[1]})
        for mod in mods_all:
            ok, out = lake_build(work, mod, log)
            if not ok:
                print(f"FAIL unaltered: {mod} does not build"); print(out[-3000:]); return 1
        print(f"ok   unaltered: {' '.join(mods_all)} check")
        for f, mods, kind, name, old, new in muts:
            path = os.path.join(work, "lean", f)
            orig = open(path).read()
            if orig.count(old) != 1:
                print(f"FAIL {name}: the text to mutate occurs {orig.count(old)} times in {f}"); fail = 1
                continue
            mutated = orig.replace(old, new)
            open(path, "w").write(mutated)
            t0 = time.time()
            survived, invalid, where = [], [], []
            for mod in mods:
                ok, out = lake_build(work, mod, log)
                if ok:
                    survived.append(mod); continue
                errs = [(e, int(n)) for e, n in ERR.findall(out)]
                for e, n in errs:
                    src = os.path.join(work, "lean", e)
                    kind_at, line = decl_at(open(src).read().split("\n"), n)
                    decl = open(src).read().split("\n")[line - 1].split(":")[0].strip() if line else "?"
                    if kind_at in ("def", "abbrev", "structure", "inductive", "instance"):
                        invalid.append(f"{e}:{n} in {decl}")
                    else:
                        where.append(f"{e}:{n} ({decl[:60]})")
                if not errs:
                    invalid.append(f"{mod}: failed without a located error")
            open(path, "w").write(orig)
            dt = time.time() - t0
            if survived:
                print(f"FAIL {name} [{kind}]: {' '.join(survived)} still checks against the altered spec"); fail = 1
            elif invalid:
                print(f"INVALID {name}: the altered spec itself does not elaborate: {invalid[0]}"); fail = 1
            else:
                first = sorted(set(where))[0] if where else "?"
                print(f"ok   {name} [{kind}]: {' '.join(mods)} fail ({dt:.0f}s; first error {first})")
        # The unaltered copy again, so a failure above is the mutation's.
        for mod in mods_all:
            ok, out = lake_build(work, mod, log)
            if not ok:
                print(f"FAIL unaltered (after): {mod}"); fail = 1
        if not fail:
            print(f"all {len(muts)} spec mutations break their proofs")
    finally:
        shutil.rmtree(work, ignore_errors=True)
    return fail


sys.exit(main())
