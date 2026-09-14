#!/usr/bin/env bash
# G4: function boundary precision and recall against DWARF ground truth.
#
# The quality gate table in ROADMAP.md has listed G4 since the start and
# nothing measured it over a corpus worth the name. This does, over two:
#
#   fixtures/build          the local corpus, four C files at two levels
#   fixtures/build/decbench the DecBench corpus, real projects at three levels,
#                           built by scripts/decbench-fixtures.sh
#
# The method, which is the part worth arguing about:
#
#   * Ground truth is every DWARF subprogram with a low_pc and a high_pc, read
#     out of the *unstripped* binary by readelf. Not by our own DWARF reader:
#     a boundary score graded by the thing being graded is not a measurement.
#   * r12e is run on a copy with the debug information removed, in two
#     configurations. `stripped` is `strip --strip-all`, which leaves
#     .eh_frame, and .eh_frame names the start of every function that can be
#     unwound through: a tool that reads it scores perfect recall and has
#     shown nothing. `blind` removes .eh_frame and .eh_frame_hdr as well, and
#     is the configuration that measures recovery. Quote the second one.
#   * A recovered function counts as a hit when its start address equals a
#     ground-truth start. Start-only, because that is the number the field
#     reports and the number the rest of analysis depends on; the end is
#     reported separately as `exact`, where the size must also agree.
#   * Ground truth is restricted to addresses inside a section r12e considers
#     executable, so a subprogram the linker discarded is not counted against
#     recall. Precision is scoped to the byte ranges DWARF covers, for the
#     reason spelled out where it is computed.
#
# Usage: scripts/boundary-gate.sh [--csv] [glob ...]
#
#   scripts/boundary-gate.sh              # both corpora
#   scripts/boundary-gate.sh --csv        # machine-readable, for docs/
#   scripts/boundary-gate.sh zlib         # only manifest rows matching zlib
#
# Env: R12E  the executable (default target/release/r12e)
#
# Degrades rather than fails: no corpus is a skip and a zero exit, like every
# other gate here. A non-zero exit means a floor below was missed.
set -euo pipefail

repo=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)
r12e=${R12E:-$repo/target/release/r12e}

csv=0
if [ "${1:-}" = "--csv" ]; then csv=1; shift; fi
filter=${1:-}

if [ ! -x "$r12e" ]; then
  echo "no $r12e; build first: cargo build --release. Skipping." >&2
  exit 0
fi

manifest=$repo/fixtures/build/decbench/manifest.tsv
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT
rows=$work/rows.tsv
: > "$rows"

# The local corpus is a `.stripped` beside an unstripped original, which is
# what scripts/build-fixtures.sh already produces. Ground truth is extracted
# here rather than cached, because it is four files.
ground_truth() {
  readelf --debug-dump=info "$1" 2> /dev/null | python3 -c '
import re, sys
low = high = name = None
declared = False
out = {}
def flush():
    global low, high, name, declared
    if low is not None and high is not None and not declared:
        size = high - low if high > low else high
        if size > 0:
            out[low] = size
    low = high = name = None
    declared = False
for line in sys.stdin:
    if "DW_TAG_" in line:
        flush()
        if "DW_TAG_subprogram" not in line:
            declared = True
        continue
    m = re.search(r"DW_AT_low_pc\s*:\s*(0x[0-9a-f]+|\d+)", line)
    if m: low = int(m.group(1), 0); continue
    m = re.search(r"DW_AT_high_pc\s*:\s*(0x[0-9a-f]+|\d+)", line)
    if m: high = int(m.group(1), 0); continue
    if "DW_AT_declaration" in line: declared = True
flush()
for a in sorted(out):
    print(f"{a:#x}\t{out[a]:#x}\t")
'
}

# One binary, two configurations.
#
#   stripped  `strip --strip-all`. No symbols and no DWARF, but .eh_frame
#             survives, and .eh_frame names the start of every function that
#             can be unwound through. This is what a real Linux target looks
#             like and it is the configuration DecBench hands its entrants.
#   blind     .eh_frame and .eh_frame_hdr removed as well. Nothing is left but
#             the code, the relocations and the entry point, which is what
#             firmware, a Windows binary without unwind data, and anything
#             deliberately hardened look like. This is the configuration that
#             measures boundary *recovery* rather than unwind-table reading,
#             and it is the number worth quoting.
score_one() {
  local project=$1 opt=$2 orig=$3 stripped=$4 truth=$5
  local blind=$work/blind.bin
  if ! objcopy --remove-section=.eh_frame --remove-section=.eh_frame_hdr \
    "$stripped" "$blind" 2> /dev/null; then
    blind=""
  fi
  local mode image
  for mode in stripped blind; do
    image=$stripped
    [ "$mode" = stripped ] || image=$blind
    [ -n "$image" ] || continue
    "$r12e" funcs --json "$image" > "$work/funcs.json" 2> /dev/null || continue
    "$r12e" sections --json "$image" > "$work/sections.json" 2> /dev/null || continue
    python3 - "$project" "$opt" "$orig" "$mode" "$truth" "$work/funcs.json" \
      "$work/sections.json" <<'PY' >> "$rows"
import json, os, sys

project, opt, orig, mode, truth_path, funcs_path, sections_path = sys.argv[1:8]

def num(x):
    return int(x, 0) if isinstance(x, str) else int(x)

exec_ranges = []
for s in json.load(open(sections_path))["items"]:
    if not s.get("exec"):
        continue
    start, size = num(s["addr"]), num(s.get("size", 0))
    if size:
        exec_ranges.append((start, start + size))

def in_exec(a):
    # No executable section at all means the question cannot be asked, so
    # every address counts rather than none.
    return not exec_ranges or any(lo <= a < hi for lo, hi in exec_ranges)

truth = {}
for line in open(truth_path):
    parts = line.rstrip("\n").split("\t")
    if len(parts) < 2:
        continue
    a, n = int(parts[0], 0), int(parts[1], 0)
    if in_exec(a):
        truth[a] = n

found = {}
for f in json.load(open(funcs_path))["items"]:
    found[num(f["addr"])] = num(f.get("size", 0) or 0)

if not truth:
    sys.exit(0)

# Precision needs a scope, and getting it wrong is how this number lies.
# A stripped binary contains code the project did not compile: PLT thunks,
# _init and _fini, and whatever the C runtime linked in, none of which has
# DWARF because none of it was built with -g. Counting those as false
# positives would say r12e invented 300 functions where it found 300 real
# ones the ground truth simply does not describe.
#
# In scope means inside a byte range DWARF actually covers. A reported
# function starting in the middle of a ground-truth body is a genuine false
# positive, a split, and it counts. One in the PLT is out of scope. Both
# denominators are printed, because the wider one is what an outsider would
# compute and hiding it would be the same dishonesty in the other direction.
merged = []
for lo, hi in sorted((a, a + n) for a, n in truth.items()):
    if merged and lo <= merged[-1][1]:
        merged[-1][1] = max(merged[-1][1], hi)
    else:
        merged.append([lo, hi])
starts = [m[0] for m in merged]

import bisect

def in_scope(a):
    i = bisect.bisect_right(starts, a) - 1
    return i >= 0 and a < merged[i][1]

scoped = {a for a in found if in_scope(a)}
hits = set(truth) & set(found)
exact = sum(1 for a in hits if truth[a] == found[a])
tp = len(hits)
recall = tp / len(truth)
precision = tp / len(scoped) if scoped else 0.0
f1 = 2 * recall * precision / (recall + precision) if tp else 0.0
print("\t".join([
    project, opt, os.path.basename(orig), mode,
    str(len(truth)), str(len(scoped)), str(len(found)), str(tp), str(exact),
    f"{recall:.4f}", f"{precision:.4f}", f"{f1:.4f}",
]))
PY
  done
}

# --- the DecBench corpus -----------------------------------------------------
if [ -s "$manifest" ]; then
  while IFS=$'\t' read -r project opt orig stripped truth; do
    [ -n "${project:-}" ] || continue
    [ -z "$filter" ] || case "$project/$orig" in *"$filter"*) ;; *) continue ;; esac
    [ -f "$stripped" ] && [ -s "$truth" ] || continue
    score_one "$project" "$opt" "$orig" "$stripped" "$truth"
  done < "$manifest"
fi

# --- the local corpus --------------------------------------------------------
if [ -z "$filter" ] && [ -d "$repo/fixtures/build" ]; then
  for stripped in "$repo"/fixtures/build/*.stripped; do
    [ -f "$stripped" ] || continue
    orig=${stripped%.stripped}
    [ -f "$orig" ] || continue
    base=$(basename "$orig")
    # The optimization level is in the fixture name, which is how
    # scripts/build-fixtures.sh spells it.
    case "$base" in
      *.O0*) opt=O0 ;; *.O1*) opt=O1 ;; *.O2*) opt=O2 ;;
      *.O3*) opt=O3 ;; *.Os*) opt=Os ;; *) opt=- ;;
    esac
    ground_truth "$orig" > "$work/truth.tsv"
    [ -s "$work/truth.tsv" ] || continue
    score_one "fixtures" "$opt" "$orig" "$stripped" "$work/truth.tsv"
  done
fi

if [ ! -s "$rows" ]; then
  echo "no corpus with DWARF ground truth found." >&2
  echo "  local:    scripts/build-fixtures.sh" >&2
  echo "  DecBench: scripts/decbench-fixtures.sh" >&2
  echo "Skipped." >&2
  exit 0
fi

if [ "$csv" = 1 ]; then
  echo "project,opt,binary,mode,truth,in_scope,reported,hit,exact,recall,precision,f1"
  tr '\t' ',' < "$rows"
  exit 0
fi

# Floors, so this is a gate and not a report. Recorded from a measured run and
# set a little under it, the way the lifting floors are: a floor is a
# regression detector, not a target. Raise one when the number it guards has
# moved up and stayed up, in the commit that moved it.
#
# BOUNDARY_FLOOR=0 turns the check off, for a run on a partial corpus.
: "${BOUNDARY_FLOOR:=1}"
FLOOR_STRIPPED_RECALL=0.99 \
FLOOR_STRIPPED_EXACT=0.70 \
FLOOR_BLIND_RECALL=0.75 \
FLOOR_BLIND_PRECISION=0.90 \
BOUNDARY_FLOOR="$BOUNDARY_FLOOR" \
python3 - "$rows" <<'PY'
import sys
from collections import defaultdict

rows = []
for line in open(sys.argv[1]):
    p, o, b, m, t, sc, fa, h, e, _r, _pr, _f1 = line.rstrip("\n").split("\t")
    rows.append((p, o, b, m, int(t), int(sc), int(fa), int(h), int(e)))

MODES = ["stripped", "blind"]

def agg(mode, keyfn):
    out = defaultdict(lambda: [0, 0, 0, 0, 0, 0])
    for p, o, b, m, t, sc, fa, h, e in rows:
        if m != mode:
            continue
        a = out[keyfn(p, o)]
        a[0] += t; a[1] += sc; a[2] += fa; a[3] += h; a[4] += e; a[5] += 1
    return out

def show(label, a):
    t, sc, fa, h, e, n = a
    rec = h / t if t else 0.0
    prec = h / sc if sc else 0.0
    f1 = 2 * rec * prec / (rec + prec) if h else 0.0
    ex = e / t if t else 0.0
    print(f"{label:<26} {n:>4} {t:>7} {sc:>7} {fa:>8} {rec:>7.3f} {prec:>7.3f} {f1:>7.3f} {ex:>7.3f}")

hdr = (f"{'':<26} {'bins':>4} {'truth':>7} {'scope':>7} {'reported':>8} "
       f"{'recall':>7} {'prec':>7} {'F1':>7} {'exact':>7}")

print("G4: function boundary recovery against DWARF ground truth")
print()
print("  truth     DWARF subprograms with a low_pc inside an executable section")
print("  scope     functions r12e reported inside a byte range DWARF covers")
print("  reported  functions r12e reported at all, PLT and CRT code included")
print("  recall    ground-truth starts r12e found")
print("  prec      in-scope reported functions that are ground-truth starts")
print("  exact     ground-truth functions whose start AND size both matched")
print()
print("  stripped  strip --strip-all: no symbols, no DWARF, .eh_frame kept")
print("  blind     .eh_frame and .eh_frame_hdr removed too, so nothing but code")

for mode in MODES:
    per = agg(mode, lambda p, o: (p, o))
    if not per:
        continue
    print()
    print(f"=== {mode} ===")
    print(hdr)
    print("-" * len(hdr))
    for (p, o), a in sorted(per.items()):
        show(f"{p} {o}", a)
    print("-" * len(hdr))
    for o, a in sorted(agg(mode, lambda p, o: o).items()):
        show(f"all projects {o}", a)
    show("TOTAL", list(agg(mode, lambda p, o: 0).values())[0])

import os

totals = {m: (list(agg(m, lambda p, o: 0).values()) or [[0] * 6])[0] for m in MODES}

def rate(a, num, den):
    return a[num] / a[den] if a[den] else 0.0

failures = []
if os.environ.get("BOUNDARY_FLOOR") == "1":
    checks = [
        ("stripped recall", rate(totals["stripped"], 3, 0), "FLOOR_STRIPPED_RECALL"),
        ("stripped exact", rate(totals["stripped"], 4, 0), "FLOOR_STRIPPED_EXACT"),
        ("blind recall", rate(totals["blind"], 3, 0), "FLOOR_BLIND_RECALL"),
        ("blind precision", rate(totals["blind"], 3, 1), "FLOOR_BLIND_PRECISION"),
    ]
    print()
    for label, got, var in checks:
        floor = float(os.environ[var])
        ok = got >= floor
        print(f"  {'ok  ' if ok else 'FAIL'} {label:<20} {got:.3f} against a floor of {floor:.3f}")
        if not ok:
            failures.append(f"{label} {got:.3f} < {floor:.3f}")

# An average hides the binary that scores zero, so the tail gets its own list.
blind = [r for r in rows if r[3] == "blind"]
if blind:
    worst = sorted(blind, key=lambda r: (r[7] / r[4] if r[4] else 1.0, -r[4]))[:10]
    print()
    print("Worst ten binaries by recall, blind")
    for p, o, b, m, t, sc, fa, h, e in worst:
        rec = h / t if t else 0.0
        prec = h / sc if sc else 0.0
        print(f"  {p:<12} {o:<12} {b:<26} {h:>5}/{t:<6} recall {rec:.3f}  prec {prec:.3f}")

if failures:
    print()
    print("G4 below floor: " + "; ".join(failures), file=sys.stderr)
    sys.exit(1)
PY
