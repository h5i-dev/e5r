#!/usr/bin/env bash
# Build an e5r signature library out of real distribution packages.
#
# A statically linked binary is the case signature matching exists for: the
# library code is inside the image, the symbol table that named it has been
# stripped, and what is left is several thousand functions with no names. The
# names are not lost, though. They are sitting in the distribution's own
# development packages, in the static libraries the linker copied that code out
# of, and those are downloadable, versioned and already on most machines.
#
# So this takes packages or static libraries, splits each archive into the
# objects it holds, fingerprints every named function in them with `e5r sig
# <object> create`, and merges the result into one sorted library. The output is the
# ordinary text format: one signature per line, sorted, so a library reviews in
# a diff and merges the way the annotation log does.
#
# Usage:
#   scripts/build-siglib.sh -o glibc.sig /path/to/libc6-dev_*.deb
#   scripts/build-siglib.sh -o glibc.sig libc6-dev            # installed package
#   scripts/build-siglib.sh -o ssl.sig /usr/lib/*/libcrypto.a
#   scripts/build-siglib.sh -o all.sig /usr/lib/aarch64-linux-gnu
#
# Inputs may be, in any mixture:
#   *.deb                  a Debian package
#   *.rpm                  an RPM package
#   *.tar.zst|xz|gz|bz2    an Arch or source tarball
#   *.a                    a static library
#   a directory            searched for static libraries
#   a name                 an installed dpkg or rpm package, looked up
#
# What this does not do is read anybody else's signature format. The FLIRT
# `.sig` container is not published by its vendor; the byte layouts that
# circulate are third-party reverse engineering, and CONTRIBUTING.md's
# clean-room rule rules them out. The archives below are a better source
# anyway: they carry the exact code the linker copied, with the real names, and
# they need no reverse engineering of anyone's format.
set -euo pipefail

e5r=${E5R:-./target/release/e5r}
out=
inputs=()

while [ $# -gt 0 ]; do
  case "$1" in
    -o|--out) out=$2; shift 2 ;;
    -h|--help) sed -n '2,40p' "$0"; exit 0 ;;
    -*) echo "unknown option $1" >&2; exit 2 ;;
    *) inputs+=("$1"); shift ;;
  esac
done

if [ ${#inputs[@]} -eq 0 ] || [ -z "$out" ]; then
  echo "usage: $0 -o LIBRARY INPUT..." >&2
  exit 2
fi

if [ ! -x "$e5r" ]; then
  echo "$e5r not found; build it with: cargo build --release -p e5r-cli" >&2
  exit 2
fi

work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT
mkdir -p "$work/parts"

# Every static library found, one per line, with the input it came from.
archives=$work/archives

note() { printf '%s\n' "$*" >&2; }

# Unpack one package into a directory and list the static libraries in it.
unpack() {
  local pkg=$1 into=$2
  mkdir -p "$into"
  case "$pkg" in
    *.deb)
      if command -v dpkg-deb > /dev/null; then
        dpkg-deb -x "$pkg" "$into"
      else
        # A .deb is an ar archive holding data.tar.*; both tools are here
        # because the project already needs them.
        (cd "$into" && ar x "$(readlink -f "$pkg")" && tar xf data.tar.*)
      fi
      ;;
    *.rpm)
      command -v rpm2cpio > /dev/null || { note "skip $pkg: no rpm2cpio"; return 1; }
      (cd "$into" && rpm2cpio "$(readlink -f "$pkg")" | cpio -id --quiet)
      ;;
    *.tar.zst|*.tar.xz|*.tar.gz|*.tar.bz2|*.tgz)
      tar xf "$pkg" -C "$into"
      ;;
    *) return 1 ;;
  esac
}

for input in "${inputs[@]}"; do
  case "$input" in
    *.a)
      [ -e "$input" ] || { note "skip $input: no such file"; continue; }
      printf '%s\t%s\n' "$input" "$(basename "$input")" >> "$archives"
      ;;
    *.deb|*.rpm|*.tar.*|*.tgz)
      [ -e "$input" ] || { note "skip $input: no such file"; continue; }
      d=$work/pkg/$(basename "$input")
      if unpack "$input" "$d"; then
        # The package name is what a reader wants in the source column, not
        # the temporary path the file was unpacked into.
        while IFS= read -r a; do
          printf '%s\t%s\n' "$a" "$(basename "$input")/$(basename "$a")" >> "$archives"
        done < <(find "$d" -name '*.a' -type f | sort)
      fi
      ;;
    *)
      if [ -d "$input" ]; then
        while IFS= read -r a; do
          printf '%s\t%s\n' "$a" "$(basename "$a")" >> "$archives"
        done < <(find "$input" -name '*.a' -type f | sort)
      elif command -v dpkg > /dev/null && dpkg -L "$input" > /dev/null 2>&1; then
        while IFS= read -r a; do
          [ -f "$a" ] || continue
          printf '%s\t%s\n' "$a" "$input/$(basename "$a")" >> "$archives"
        done < <(dpkg -L "$input" | grep '\.a$' | sort)
      elif command -v rpm > /dev/null && rpm -ql "$input" > /dev/null 2>&1; then
        while IFS= read -r a; do
          [ -f "$a" ] || continue
          printf '%s\t%s\n' "$a" "$input/$(basename "$a")" >> "$archives"
        done < <(rpm -ql "$input" | grep '\.a$' | sort)
      else
        note "skip $input: not a package, an archive or a directory"
      fi
      ;;
  esac
done

if [ ! -s "$archives" ]; then
  note "no static libraries found in: ${inputs[*]}"
  exit 1
fi

members=0
failed=0
n=0
while IFS=$'\t' read -r archive label; do
  n=$((n + 1))
  d=$work/x/$n
  mkdir -p "$d"
  # `ar x` rather than reading the archive in the tool: a member is an ordinary
  # object file once it is on disk, and this keeps the script working against
  # any e5r that can open an object at all.
  (cd "$d" && ar x "$(readlink -f "$archive")" 2>/dev/null) || {
    note "skip $archive: not an archive this ar understands"
    continue
  }
  # Every member, not every `*.o`: glibc names its members `.oS`, and an
  # archive is free to call them anything at all.
  for o in "$d"/*; do
    [ -f "$o" ] || continue
    members=$((members + 1))
    if ! "$e5r" sig "$o" create > "$work/one.sig" 2>/dev/null; then
      failed=$((failed + 1))
      continue
    fi
    # Rewrite the provenance column so every name says which archive member it
    # came out of. A signature nobody can trace back is a name with no evidence
    # behind it, which is the thing this whole feature must not produce.
    awk -v src="$label($(basename "$o"))" \
      '!/^#/ && NF >= 5 { printf "%s %s %s %s %s\n", $1, $2, $3, $4, src }' \
      "$work/one.sig" >> "$work/parts/all"
  done
  rm -rf "$d"
  so_far=0
  if [ -s "$work/parts/all" ]; then
    so_far=$(wc -l < "$work/parts/all")
  fi
  note "$label: $so_far signatures so far"
done < "$archives"

if [ ! -s "$work/parts/all" ]; then
  note "no signatures were produced"
  exit 1
fi

# Sorted and deduplicated here as well as in the reader, so the file on disk is
# the same file on every machine and a rebuild shows up as a real diff.
{
  echo "# e5r signatures v1"
  echo "# built by scripts/build-siglib.sh from: ${inputs[*]}"
  LC_ALL=C sort -u < "$work/parts/all"
} > "$out"

note "$(grep -vc '^#' "$out") signatures from $members objects in $(wc -l < "$archives") archives, $failed unreadable"
note "wrote $out"
