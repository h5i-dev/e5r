#!/usr/bin/env bash
# Make the DecBench corpus available as fixtures, without copying it into this
# repository.
#
# DecBench is not a set of binaries: it is 39 recipes that fetch upstream
# sources and build them at several optimization levels with DWARF retained.
# That is the reason it is worth having here. Every function's true start and
# end is in the debug information, so it is ground truth for the G4 function
# boundary gate that does not come from our own symbol reader, and it is real
# code rather than the handful of C files in fixtures/src.
#
# What this script does NOT do: copy anything large into the checkout. The
# sources, the object trees and the binaries live in a cache directory outside
# it; the only thing that lands under fixtures/ is a manifest, which is a text
# file, and which is under fixtures/build/ and therefore gitignored.
#
# It also does not use DecBench's Python package, a virtualenv, angr or Joern.
# scripts/decbench.sh needs all of those because it runs the benchmark's own
# metrics. This one only needs the recipe, which is the TOML, so it reads the
# TOML and drives gcc itself. The DecBench checkout is read-only throughout:
# nothing is written inside it, not even a __pycache__.
#
# Usage: scripts/decbench-fixtures.sh [project ...]
#
#   scripts/decbench-fixtures.sh                 # the default short list
#   scripts/decbench-fixtures.sh zlib bzip2      # named projects
#   scripts/decbench-fixtures.sh --list          # what the checkout offers
#   DECBENCH_OPTS=O0,O2 scripts/decbench-fixtures.sh zlib
#
# Env: DECBENCH_REPO      the DecBench checkout (default ~/Ref/decbench)
#      DECBENCH_FIXTURES  where to build (default $XDG_CACHE_HOME/e5r/decbench,
#                         falling back to ~/.cache/e5r/decbench)
#      DECBENCH_OPTS      comma-separated optimization levels; default is what
#                         each project's TOML asks for
#      DECBENCH_JOBS      make -j level (default 1: four agents share this box)
#
# Exit status is 0 when there is nothing to do, because this is a fixture
# builder and an absent corpus is a skip, not a failure. It is non-zero only
# when a project it was explicitly asked for could not be built.
set -euo pipefail

repo=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)
decbench=${DECBENCH_REPO:-$HOME/Ref/decbench}
cache=${DECBENCH_FIXTURES:-${XDG_CACHE_HOME:-$HOME/.cache}/e5r/decbench}
jobs=${DECBENCH_JOBS:-1}
manifest_dir="$repo/fixtures/build/decbench"

# Projects that build here with no cross toolchain, no autotools bootstrap and
# no network beyond the source fetch. The full 39 include several that need a
# sysroot or a configure run this machine cannot satisfy; asking for one by
# name still tries it.
default_projects="zlib bzip2 gzip diffutils"

if [ "${1:-}" = "--list" ]; then
  if [ ! -d "$decbench/projects" ]; then
    echo "no DecBench checkout at $decbench; set DECBENCH_REPO" >&2
    exit 0
  fi
  find "$decbench/projects" -name '*.toml' -not -path '*/disabled/*' \
    -printf '%f\n' | sed 's/\.toml$//' | sort
  exit 0
fi

if [ ! -d "$decbench/projects" ]; then
  echo "no DecBench checkout at $decbench; set DECBENCH_REPO. Skipping." >&2
  exit 0
fi
command -v gcc > /dev/null || { echo "no gcc; skipping DecBench fixtures" >&2; exit 0; }
command -v git > /dev/null || { echo "no git; skipping DecBench fixtures" >&2; exit 0; }

projects=("$@")
if [ "${projects[0]:-}" = "--all" ]; then
  # Every recipe the checkout offers. Most of the 39 need a dependency this
  # machine does not have; each one that fails is reported and skipped, so the
  # corpus ends up being whatever actually builds here.
  read -r -a projects <<< "$(find "$decbench/projects" -name '*.toml' \
    -not -path '*/disabled/*' -printf '%f\n' | sed 's/\.toml$//' | sort | tr '\n' ' ')"
fi
[ ${#projects[@]} -gt 0 ] || read -r -a projects <<< "$default_projects"

mkdir -p "$cache/src" "$cache/bin" "$manifest_dir"
manifest="$manifest_dir/manifest.tsv"

# The TOML is the recipe and nothing else in this script knows its shape.
# tomllib is stdlib from 3.11; a `--list` of the fields is printed as shell
# assignments so bash does not have to parse TOML.
read_recipe() {
  python3 - "$1" <<'PY'
import shlex, sys, tomllib
with open(sys.argv[1], 'rb') as f:
    t = tomllib.load(f)
c = t.get('compilation', {})
# O2-noinline is O2 with -fno-inline, which is the level DecBench added because
# inlining is what destroys function boundaries. It is the interesting one for
# a boundary gate, so the mapping is kept exactly as DecBench defines it.
flags = {
    'O0': '-O0', 'O1': '-O1', 'O2': '-O2', 'O3': '-O3',
    'Os': '-Os', 'Oz': '-Oz', 'O2-noinline': '-O2 -fno-inline',
}
out = {
    'name': t.get('name', ''),
    'version': t.get('version', ''),
    'remote': t.get('source_remote', ''),
    'remote_type': t.get('remote_type', 'git'),
    'package_dir': t.get('package_dir', ''),
    'source_dir': t.get('source_dir', '.'),
    'pre_make': ' && '.join(c.get('pre_make_cmds', t.get('pre_make_cmds', []))) ,
    'post_download': ' && '.join(t.get('post_download_cmds', [])),
    'make_cmd': t.get('make_cmd', 'make'),
    'base_flags': ' '.join(c.get('base_flags', ['-g'])),
    'levels': ','.join(str(x) for x in c.get('optimization_levels', ['O2'])),
    'opt_flags': ';'.join(f'{k}={v}' for k, v in flags.items()),
}
for k, v in out.items():
    print(f'r_{k}={shlex.quote(str(v))}')
PY
}

opt_flags_for() {
  case "$1" in
    O0) echo "-O0" ;; O1) echo "-O1" ;; O2) echo "-O2" ;; O3) echo "-O3" ;;
    Os) echo "-Os" ;; Oz) echo "-Oz" ;; O2-noinline) echo "-O2 -fno-inline" ;;
    *) echo "-$1" ;;
  esac
}

# DWARF ground truth for one binary, as a TSV of low_pc, size and name.
#
# readelf rather than our own reader on purpose: a boundary gate graded by the
# thing being graded measures nothing. readelf is binutils' DWARF reader and is
# the oracle here, the way objdump is the oracle for the decoder gates.
ground_truth() {
  readelf --debug-dump=info "$1" 2> /dev/null | python3 -c '
import re, sys
low = high = name = None
declared = False
out = {}
def flush():
    global low, high, name, declared
    if low is not None and high is not None and not declared:
        # DW_AT_high_pc is either an address or, in DWARF 4 and later with a
        # constant form, a length. readelf prints both as a bare hex number,
        # so the smaller-than-low_pc case is the length form.
        size = high - low if high > low else high
        if size > 0:
            out[low] = (size, name or "")
    low = high = name = None
    declared = False
for line in sys.stdin:
    if "DW_TAG_" in line:
        flush()
        if "DW_TAG_subprogram" not in line:
            low = high = None
            name = None
            declared = True
        continue
    m = re.search(r"DW_AT_low_pc\s*:\s*(0x[0-9a-f]+|\d+)", line)
    if m:
        low = int(m.group(1), 0)
        continue
    m = re.search(r"DW_AT_high_pc\s*:\s*(0x[0-9a-f]+|\d+)", line)
    if m:
        high = int(m.group(1), 0)
        continue
    if "DW_AT_declaration" in line:
        declared = True
        continue
    m = re.search(r"DW_AT_name\s*:.*?:\s*(\S+)\s*$", line)
    if m:
        name = m.group(1)
flush()
for low in sorted(out):
    size, name = out[low]
    print(f"{low:#x}\t{size:#x}\t{name}")
'
}

failed=0
for project in "${projects[@]}"; do
  toml=$(find "$decbench/projects" -name "$project.toml" -not -path '*/disabled/*' | head -1)
  if [ -z "$toml" ]; then
    echo "== $project: no recipe in $decbench/projects; skipped" >&2
    failed=1
    continue
  fi
  eval "$(read_recipe "$toml")"

  # Fetch once, into the cache. Shallow, and at the version the recipe names,
  # so the corpus is the same corpus DecBench scores.
  src="$cache/src/$project"
  if [ ! -d "$src/.git" ] && [ ! -d "$src" ]; then
    echo "== $project: fetching $r_remote ($r_version)"
    case "$r_remote_type" in
      git)
        git clone --quiet --depth 1 ${r_version:+--branch "$r_version"} \
          "$r_remote" "$src" 2> /dev/null \
          || git clone --quiet --depth 1 "$r_remote" "$src" \
          || { echo "== $project: clone failed; skipped" >&2; failed=1; continue; }
        ;;
      tar)
        mkdir -p "$src"
        # To a file rather than through a pipe: the recipes name .tar.gz,
        # .tar.xz and .tar.bz2, and tar picks the decompressor from the
        # suffix, which it cannot see on stdin.
        tarball="$cache/src/.$project.tar"
        if ! curl -fsSL -o "$tarball" "$r_remote" \
          || ! tar -xf "$tarball" -C "$src" --strip-components=1; then
          echo "== $project: download failed; skipped" >&2
          rm -rf "$src" "$tarball"
          failed=1
          continue
        fi
        rm -f "$tarball"
        ;;
      *)
        echo "== $project: remote type $r_remote_type not handled here; skipped" >&2
        failed=1
        continue
        ;;
    esac
  fi

  levels=${DECBENCH_OPTS:-$r_levels}
  for opt in ${levels//,/ }; do
    bindir="$cache/bin/$opt/$project"
    if [ -n "$(ls "$bindir" 2> /dev/null | grep -v '\.\(stripped\|dwarf\)$' || true)" ]; then
      echo "== $project $opt: already built"
    else
      build="$cache/build/$opt/$project"
      rm -rf "$build"
      mkdir -p "$(dirname "$build")"
      # A copy per level rather than a `make clean`: the recipes are upstream
      # build systems and not all of them have a clean that works.
      cp -a "$src" "$build"
      # DecBench runs configure and make at the package root and collects the
      # binaries from `source_dir` under it, which is a subdirectory like
      # `src` or `find`, not the place the build runs. Getting these two the
      # same way round is the difference between building grep and not.
      root="$build"
      collect="$build/${r_source_dir:-.}"
      export CC=gcc
      export CFLAGS="$r_base_flags $(opt_flags_for "$opt")"
      echo "== $project $opt: building with CFLAGS=$CFLAGS"
      mkdir -p "$cache/log"
      log="$cache/log/$project.$opt.log"
      (
        cd "$root"
        # autogen and configure are allowed to fail: several recipes run one
        # that is optional, and the make that follows is the real test.
        [ -z "$r_post_download" ] || eval "$r_post_download" || true
        [ -z "$r_pre_make" ] || eval "$r_pre_make" || true
        eval "${r_make_cmd:-make} -j$jobs"
      ) > "$log" 2>&1 \
        || { echo "== $project $opt: build failed, see $log; skipped" >&2; failed=1; continue; }

      mkdir -p "$bindir"
      # Collect linked ELF images only: the objects are not what a boundary
      # gate measures, and DecBench collects the same set.
      while IFS= read -r f; do
        case "$(file -b "$f" 2> /dev/null)" in
          *ELF*executable* | *ELF*shared\ object*) cp -f "$f" "$bindir/$(basename "$f")" ;;
        esac
      done < <(find "$collect" -type f -perm -u+x ! -name '*.o' ! -name '*.sh' ! -name '*.py' 2> /dev/null)
      # The build tree is the big thing; the binaries are not. Drop it.
      rm -rf "$build"
    fi

    for bin in "$bindir"/*; do
      [ -f "$bin" ] || continue
      case "$bin" in *.stripped | *.dwarf) continue ;; esac
      # The DWARF copy is the ground truth; the stripped copy is what the gate
      # hands to e5r, so that nothing it measures came from a symbol table.
      [ -f "$bin.dwarf" ] || ground_truth "$bin" > "$bin.dwarf"
      if [ ! -s "$bin.dwarf" ]; then
        rm -f "$bin.dwarf"
        continue
      fi
      if [ ! -f "$bin.stripped" ]; then
        cp -f "$bin" "$bin.stripped"
        strip --strip-all "$bin.stripped" 2> /dev/null || true
      fi
    done
  done
done

# The manifest is rebuilt from what is in the cache, not from what this run
# built, so asking for one more project adds to the corpus instead of replacing
# it, and a deleted cache directory disappears from the manifest by itself.
: > "$manifest.tmp"
for bin in "$cache"/bin/*/*/*; do
  [ -f "$bin" ] || continue
  case "$bin" in *.stripped | *.dwarf | *.log) continue ;; esac
  [ -s "$bin.dwarf" ] && [ -f "$bin.stripped" ] || continue
  o=$(basename "$(dirname "$(dirname "$bin")")")
  pr=$(basename "$(dirname "$bin")")
  printf '%s\t%s\t%s\t%s\t%s\n' "$pr" "$o" "$bin" "$bin.stripped" "$bin.dwarf" \
    >> "$manifest.tmp"
done

if [ -s "$manifest.tmp" ]; then
  sort -o "$manifest" "$manifest.tmp"
  rm -f "$manifest.tmp"
  echo
  echo "manifest: $manifest ($(wc -l < "$manifest") binaries, \
$(cut -f1 "$manifest" | sort -u | wc -l) projects, \
$(cut -f2 "$manifest" | sort -u | tr '\n' ' '))"
  echo "corpus:   $cache ($(du -sh "$cache" 2> /dev/null | cut -f1) outside the checkout)"
  echo "gate:     scripts/boundary-gate.sh"
else
  rm -f "$manifest.tmp"
  echo "nothing built; the manifest is unchanged" >&2
fi
exit $failed
