#!/usr/bin/env bash
# The installer against a real archive, end to end.
#
# `install.sh` reaches into the archive by name -- it expects
# `e5r-<version>-<target>/e5r` inside `e5r-<version>-<target>.tar.gz`, and it
# expects a `SHA256SUMS` beside it that names that archive. Every one of those
# is decided by `scripts/build-release.sh`, in a different file, and nothing
# links the two. A change to either that forgot the other is a download that
# unpacks into a path nobody looks at, and the first person to find out is
# whoever piped the script into a shell.
#
# So this builds the archive the release builds, serves it the way GitHub
# serves it, and runs the installer against it. Then it does the same with a
# corrupted checksum, because an installer that verifies nothing also passes
# the first half.
set -euo pipefail
cd "$(dirname "$0")/.."

host=$(rustc -vV | sed -n 's/^host: //p')
version=$(sed -n '/^\[workspace\.package\]/,/^\[/p' Cargo.toml |
  sed -n 's/^version = "\(.*\)"/\1/p' | head -1)
[ -n "$version" ] || { echo "cannot read the version out of Cargo.toml" >&2; exit 2; }

# The host triple, not a musl one: this is about the layout, and cross-linking
# a second architecture here would only slow the gate down. `install.sh` maps a
# Linux host to musl, so the archive is renamed to what it will ask for.
echo "==> building the release archive for $host"
./scripts/build-release.sh "$host" > /dev/null

work=$(mktemp -d)
trap 'rm -rf "$work"; [ -n "${server:-}" ] && kill "$server" 2> /dev/null || true' EXIT

case "$(uname -s)-$(uname -m)" in
  Linux-x86_64) want=x86_64-unknown-linux-musl ;;
  Linux-aarch64 | Linux-arm64) want=aarch64-unknown-linux-musl ;;
  Darwin-arm64) want=aarch64-apple-darwin ;;
  Darwin-x86_64) want=x86_64-apple-darwin ;;
  *) echo "no installer mapping for this host; nothing to check" >&2; exit 0 ;;
esac

src="dist/e5r-$version-$host.tar.gz"
[ -f "$src" ] || { echo "build-release.sh produced no $src" >&2; exit 1; }

# Restage under the name the installer will ask for. The directory inside has
# to be renamed too, which is the half that would otherwise go unchecked.
tar -xzf "$src" -C "$work"
mv "$work/e5r-$version-$host" "$work/e5r-$version-$want"
tar -C "$work" -czf "$work/e5r-$version-$want.tar.gz" "e5r-$version-$want"
rm -rf "$work/e5r-$version-$want"
(cd "$work" && sha256sum "e5r-$version-$want.tar.gz" > SHA256SUMS)

# A high port chosen per run, so two checkouts checking at once do not collide.
port=$((20000 + RANDOM % 20000))
(cd "$work" && python3 -m http.server "$port" > /dev/null 2>&1) &
server=$!
for _ in $(seq 40); do
  curl -fsS "http://127.0.0.1:$port/SHA256SUMS" > /dev/null 2>&1 && break
  sleep 0.25
done

run() {
  E5R_BASE_URL="http://127.0.0.1:$port" E5R_VERSION="v$version" \
    E5R_INSTALL_DIR="$1" sh install.sh
}

echo "==> a good archive installs"
mkdir -p "$work/good"
run "$work/good"
[ -x "$work/good/e5r" ] || { echo "FAIL: the installer left no binary" >&2; exit 1; }
"$work/good/e5r" --version | grep -q "$version" ||
  { echo "FAIL: the installed binary does not report $version" >&2; exit 1; }

echo "==> a tampered checksum is refused"
cp "$work/SHA256SUMS" "$work/SHA256SUMS.good"
# The whole digest, not its first character: `s/^./0/` leaves the file
# untouched one time in sixteen, whenever the digest already starts with a
# zero, and then this step asks the installer to reject a checksum that is
# correct. It passed here and accused the installer on CI.
sed 's/^[0-9a-f]\{64\}/0000000000000000000000000000000000000000000000000000000000000000/' \
  "$work/SHA256SUMS.good" > "$work/SHA256SUMS"
cmp -s "$work/SHA256SUMS" "$work/SHA256SUMS.good" &&
  { echo "FAIL: the tampering step changed nothing, so it tests nothing" >&2; exit 1; }
mkdir -p "$work/bad"
if run "$work/bad" > /dev/null 2>&1; then
  echo "FAIL: the installer accepted a mismatched checksum" >&2
  exit 1
fi
[ -e "$work/bad/e5r" ] && { echo "FAIL: it installed anyway" >&2; exit 1; }
cp "$work/SHA256SUMS.good" "$work/SHA256SUMS"

echo "==> a missing SHA256SUMS is refused"
mv "$work/SHA256SUMS" "$work/SHA256SUMS.hidden"
mkdir -p "$work/nosum"
if run "$work/nosum" > /dev/null 2>&1; then
  echo "FAIL: the installer installed without a checksum to check" >&2
  exit 1
fi
mv "$work/SHA256SUMS.hidden" "$work/SHA256SUMS"

echo "ok: install.sh agrees with the release layout, and refuses what it should"
