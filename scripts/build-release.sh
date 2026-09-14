#!/usr/bin/env bash
# Build release binaries into dist/, one archive and one checksum per target.
#
# The release workflow runs this same script for the Linux targets, so what CI
# does is what a maintainer can run by hand and inspect. That matters more here
# than usual: a packaging job nobody has ever run is a gate that always passes.
#
# Linking, and why the recipe looks like this:
#   * The musl targets are linked with rust-lld, which ships with the toolchain
#     in every rustup install. No musl-gcc, no cross, no container, and the same
#     command works whichever architecture the builder is. rustc supplies the
#     self-contained crt objects and libc.a for the target, so the only thing
#     missing from a plain `cargo build` is a linker that knows the other
#     architecture, and rust-lld is one.
#   * crt-static is already the musl default, so the result is a single static
#     ELF with no interpreter and no glibc version to match.
#   * Symbols are stripped through rustc rather than with a strip(1) that would
#     have to be the right architecture's.
set -euo pipefail
cd "$(dirname "$0")/.."

version=$(sed -n '/^\[workspace\.package\]/,/^\[/p' Cargo.toml |
  sed -n 's/^version = "\(.*\)"/\1/p' | head -1)
[ -n "$version" ] || { echo "cannot read the version out of Cargo.toml" >&2; exit 2; }

targets=("$@")
if [ ${#targets[@]} -eq 0 ]; then
  targets=(x86_64-unknown-linux-musl aarch64-unknown-linux-musl)
fi

host=$(rustc -vV | sed -n 's/^host: //p')
lld=$(rustc --print sysroot)/lib/rustlib/$host/bin/rust-lld
out=dist
mkdir -p "$out"

# A tarball whose bytes depend on the clock is a checksum nobody can reproduce.
# GNU tar can be told to sort and to zero the metadata; bsdtar on macOS cannot,
# and there the archive is ordinary.
tarflags=()
if tar --version 2>/dev/null | grep -q GNU; then
  tarflags=(--sort=name --owner=0 --group=0 --numeric-owner --mtime=@0)
fi

built=()
skipped=()
for target in "${targets[@]}"; do
  if ! rustc --print target-libdir --target "$target" >/dev/null 2>&1; then
    echo "skip $target: no std installed (rustup target add $target)" >&2
    skipped+=("$target")
    continue
  fi

  flags="-C strip=symbols"
  case "$target" in
    *-linux-musl) flags="$flags -C linker=$lld -C linker-flavor=ld.lld" ;;
  esac

  echo "==> $target"
  # Only the binary and what it needs: a release job has no use for the test
  # binaries of fourteen crates, and on a small machine that is the difference
  # between a build that fits and one that swaps.
  if ! RUSTFLAGS="$flags" cargo build --release --target "$target" -p r12e-cli --bin r12e; then
    echo "FAIL $target: did not build here" >&2
    skipped+=("$target")
    continue
  fi

  bin=target/$target/release/r12e
  [ -x "$bin" ] || { echo "FAIL $target: no binary at $bin" >&2; skipped+=("$target"); continue; }

  # A gate rather than a print. A musl archive that picked up a dynamic
  # dependency is not the thing the release promises, and the failure is
  # silent everywhere except on the machine that lacks that library.
  case "$target" in
    *-linux-musl)
      if command -v readelf > /dev/null; then
        if readelf -dlW "$bin" | grep -qE 'NEEDED|INTERP'; then
          echo "FAIL $target: not static" >&2
          readelf -dlW "$bin" | grep -E 'NEEDED|INTERP' >&2
          skipped+=("$target")
          continue
        fi
      else
        echo "warn: no readelf, so nothing checked that $target is static" >&2
      fi
      ;;
  esac

  name=r12e-$version-$target
  stage=$out/$name
  rm -rf "$stage"
  mkdir -p "$stage"
  cp "$bin" "$stage/r12e"
  cp README.md LICENSE MANUAL.md "$stage/"
  tar -C "$out" "${tarflags[@]}" -czf "$out/$name.tar.gz" "$name"
  rm -rf "$stage"
  built+=("$name.tar.gz")
  printf '%-34s %8s bytes  %s\n' "$target" "$(wc -c < "$bin")" "$(file -b "$bin" | cut -c1-72)"
done

[ ${#built[@]} -gt 0 ] || { echo "nothing built" >&2; exit 1; }

# One checksum file over everything, because that is the file a signature
# covers and the file a package manager reads. macOS has shasum rather than
# sha256sum, and both write the same two columns.
#
# Every archive of this version in dist/, not only the ones this run built, so
# that building one target at a time still leaves a checksum file describing
# the whole release. An archive of some other version is not listed, because a
# checksum file that mixes versions is worse than none.
if command -v sha256sum > /dev/null; then sha=(sha256sum); else sha=(shasum -a 256); fi
(cd "$out" && "${sha[@]}" r12e-"$version"-* > SHA256SUMS)
cat "$out/SHA256SUMS"

# A target that was asked for and did not appear is a failure, not a note. The
# release workflow runs one job per platform for the same reason: a missing
# archive should turn something red rather than quietly shorten the release.
if [ ${#skipped[@]} -gt 0 ]; then
  echo "not built: ${skipped[*]}" >&2
  exit 1
fi
