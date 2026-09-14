#!/usr/bin/env bash
# A CPU profile of one r12e run, as a flamegraph and as a table.
#
# Not a test: it needs a profiler, it takes as long as the run it measures,
# and what it produces is a picture and a list a person reads and records. Run
# it by hand when a change is supposed to have made something faster, or when
# something is slow and nobody knows which part.
#
# Usage: scripts/flamegraph.sh <r12e arguments...>
#        scripts/flamegraph.sh funcs /usr/lib/aarch64-linux-gnu/libcrypto.so.3
#        OUT=/tmp/x.svg TOP=30 scripts/flamegraph.sh stats /bin/bash
#
# Environment:
#   OUT    where the SVG goes (default target/profile/<command>-<binary>.svg)
#   TOP    how many rows of the table to print (default 20)
#   FREQ   sampling frequency in Hz (default 997, a prime so it does not beat
#          against anything periodic in the program)
#   PERF   a perf binary to use instead of the one this script finds
set -euo pipefail
cd "$(dirname "$0")/.."

r12e=${R12E:-target/release/r12e}
top=${TOP:-20}
freq=${FREQ:-997}

[ $# -gt 0 ] || {
  sed -n '2,17p' "$0" | sed 's/^# \{0,1\}//' >&2
  exit 2
}
[ -x "$r12e" ] || {
  echo "no $r12e; build it first: cargo build --release" >&2
  exit 2
}

# Ubuntu and WSL ship /usr/bin/perf as a wrapper that looks for a perf built
# for the running kernel and refuses when that package is missing, which is
# the normal state of a WSL box. The versioned binary next door works anyway,
# because nothing here needs a kernel-matched build: the samples come from the
# process, not from the kernel's own symbols. So find one that actually runs
# rather than one that merely exists.
find_perf() {
  local candidate
  for candidate in ${PERF:-} perf /usr/lib/linux-tools-*/perf /usr/lib/linux-tools/*/perf; do
    [ -n "$candidate" ] || continue
    command -v "$candidate" > /dev/null 2>&1 || [ -x "$candidate" ] || continue
    if "$candidate" --version > /dev/null 2>&1; then
      echo "$candidate"
      return 0
    fi
  done
  return 1
}

if ! perfbin=$(find_perf); then
  echo "no working profiler found." >&2
  echo >&2
  echo "  perf            the one this script uses; apt install linux-tools-generic" >&2
  echo "                  (on WSL the kernel-specific package does not exist, and" >&2
  echo "                   the versioned binary from linux-tools-generic is fine)" >&2
  echo "  samply          cargo install samply, for an interactive profile instead" >&2
  echo "  cargo-flamegraph  cargo install flamegraph, which drives perf as well" >&2
  echo >&2
  if command -v samply > /dev/null 2>&1; then
    echo "samply is installed. It renders its own view rather than an SVG, so" >&2
    echo "this script does not drive it; run it directly:" >&2
    echo "  samply record $r12e $*" >&2
  fi
  exit 2
fi

# perf_event_paranoid above 2 refuses a profile of your own process, and the
# error it gives says "permission denied" without saying why.
paranoid=$(cat /proc/sys/kernel/perf_event_paranoid 2> /dev/null || echo 2)
if [ "$paranoid" -gt 2 ]; then
  echo "perf_event_paranoid is $paranoid, which forbids profiling even your own" >&2
  echo "processes. Lower it for this boot:" >&2
  echo "  sudo sysctl kernel.perf_event_paranoid=2" >&2
  exit 2
fi

name=$(printf '%s-%s' "$1" "$(basename "${2:-run}")" | tr -c 'A-Za-z0-9._-' '-')
outdir=target/profile
mkdir -p "$outdir"
svg=${OUT:-$outdir/$name.svg}
data=$outdir/$name.perf
folded=$outdir/$name.folded

echo "profiling: $r12e $*" >&2
# --call-graph dwarf, because a release build has no frame pointers and the
# default unwinder then reports one frame per sample. Output is thrown away:
# the profile is of the analysis, not of the terminal.
"$perfbin" record -F "$freq" --call-graph dwarf,8192 -o "$data" -- "$r12e" "$@" \
  > /dev/null 2>&1 || {
  echo "perf record failed; rerun without the redirect to see why:" >&2
  echo "  $perfbin record -F $freq --call-graph dwarf,8192 -o $data -- $r12e $*" >&2
  exit 1
}

# perf prints Rust's v0 names raw, so the profile of r12e is unreadable until
# something demangles it. The workspace has the demangler the tool itself uses;
# when it is built, use it, and when it is not, say so rather than silently
# printing mangled names.
demangler=target/release/examples/demangle
if [ -x "$demangler" ]; then
  filter=$demangler
else
  filter=cat
  echo "note: names stay mangled; build the demangler for readable ones:" >&2
  echo "  cargo build --release -p r12e-analysis --example demangle" >&2
fi

"$perfbin" script -i "$data" 2> /dev/null | "$filter" | python3 -c '
import sys, collections

# Fold perf script output into "frame;frame;frame count" lines. A sample is a
# blank-line-separated block whose first line is the header and whose rest is
# the stack, innermost first.
stacks = collections.Counter()
frames = []

def flush():
    if frames:
        # Reversed, because a flamegraph reads outwards from the root.
        stacks[";".join(reversed(frames))] += 1
    frames.clear()

for line in sys.stdin:
    if not line.strip():
        flush()
        continue
    if not line[0].isspace():
        flush()
        continue
    # "  address symbol+0xoff (/path/to/object)" - keep the symbol.
    body = line.strip()
    parts = body.split(" ", 1)
    sym = parts[1] if len(parts) > 1 else body
    if sym.endswith(")"):
        sym = sym.rsplit(" (", 1)[0]
    sym = sym.rsplit("+0x", 1)[0].strip()
    if not sym or sym == "[unknown]":
        sym = "[unknown]"
    frames.append(sym.replace(";", ":"))
flush()

for stack, n in sorted(stacks.items()):
    print(stack, n)
' > "$folded"

samples=$(awk '{n += $NF} END {print n + 0}' "$folded")
if [ "$samples" -lt 1 ]; then
  echo "no samples; the run was too short to profile at ${freq}Hz" >&2
  exit 1
fi

python3 - "$folded" "$svg" "$*" <<'PY'
import sys, collections, html

folded, out, title = sys.argv[1], sys.argv[2], sys.argv[3]

# Build the call tree from the folded stacks. Children are kept in name order
# so the same profile always draws the same picture; a flamegraph that moves
# between runs cannot be compared against a screenshot from last week.
class Node:
    __slots__ = ("total", "kids")
    def __init__(self):
        self.total = 0
        self.kids = collections.defaultdict(Node)

root = Node()
for line in open(folded):
    stack, _, n = line.rpartition(" ")
    if not stack:
        continue
    n = int(n)
    root.total += n
    at = root
    for frame in stack.split(";"):
        at = at.kids[frame]
        at.total += n

W, H, PAD = 1200, 16, 3
depth = [0]
def measure(node, d):
    depth[0] = max(depth[0], d)
    for kid in node.kids.values():
        measure(kid, d + 1)
measure(root, 0)
height = (depth[0] + 2) * H + 40

def color(name):
    # Warm palette, hashed from the name so a function keeps its colour.
    h = 0
    for ch in name:
        h = (h * 31 + ord(ch)) & 0xFFFFFFFF
    return "rgb(%d,%d,%d)" % (205 + h % 50, 60 + (h >> 8) % 130, 40 + (h >> 16) % 55)

rects = []
def draw(node, d, x):
    for name, kid in sorted(node.kids.items()):
        w = W * kid.total / root.total
        if w > 0.12:
            y = height - (d + 1) * H - 20
            pct = 100.0 * kid.total / root.total
            label = name if w > len(name) * 6.2 else ""
            if label == "" and w > 30:
                label = name[: int(w / 6.2) - 2] + ".."
            rects.append(
                '<g><title>%s (%d samples, %.2f%%)</title>'
                '<rect x="%.2f" y="%d" width="%.2f" height="%d" fill="%s"/>'
                '<text x="%.2f" y="%d">%s</text></g>'
                % (html.escape(name), kid.total, pct, x, y, max(w - 0.6, 0.3),
                   H - 1, color(name), x + 2, y + H - 5, html.escape(label))
            )
        draw(kid, d + 1, x)
        x += w

draw(root, 0, 0)

open(out, "w").write(
    '<svg xmlns="http://www.w3.org/2000/svg" width="%d" height="%d" '
    'font-family="monospace" font-size="11">\n'
    '<rect width="100%%" height="100%%" fill="#f8f8f4"/>\n'
    '<text x="8" y="18" font-size="14">%s &#8212; %d samples</text>\n'
    '%s\n</svg>\n'
    % (W, height, html.escape("r12e " + title), root.total, "\n".join(rects))
)
PY

echo
echo "flamegraph: $svg"
echo "folded:     $folded  ($samples samples)"
echo
echo "where the time goes, by the function the sample was in (self time):"
awk '{
  n = $NF
  sub(/ [0-9]+$/, "")
  split($0, f, ";")
  self[f[length(f)]] += n
  total += n
}
END {
  for (k in self) printf "%8.2f%%  %8d  %s\n", 100 * self[k] / total, self[k], k
}' "$folded" | sort -rn | head -"$top"
