#!/usr/bin/env python3
"""Fill the Homebrew formula in from a release's SHA256SUMS.

    scripts/update-homebrew.py 0.2.0 dist/SHA256SUMS

The formula carries one url per platform and a sha256 under each. Editing four
hashes by hand once per release is how the wrong hash gets shipped, so this
reads them out of the checksum file the release job publishes and rewrites the
version at the same time.

A target with no line in SHA256SUMS keeps its placeholder and is reported, so a
release that built three platforms out of four is visible rather than silently
carrying last release's hash.
"""
import re
import sys
from pathlib import Path

FORMULA = Path(__file__).resolve().parent.parent / "packaging" / "homebrew" / "r12e.rb"
# url line, then the sha256 line under it. Non-greedy so one pair matches at a
# time, and the target comes out of the url so the two cannot drift apart.
PAIR = re.compile(
    r'(url "[^"]*r12e-)(?P<ver>[^-]+)(-(?P<target>[A-Za-z0-9_.-]+)\.tar\.gz"\s*\n\s*sha256 ")'
    r'(?P<sha>[^"]*)"'
)


def main():
    if len(sys.argv) != 3:
        sys.exit(__doc__)
    version, sums_path = sys.argv[1], Path(sys.argv[2])

    sums = {}
    for line in sums_path.read_text().splitlines():
        parts = line.split()
        if len(parts) == 2:
            sums[parts[1].lstrip("*")] = parts[0]

    text = FORMULA.read_text()
    text, n = re.subn(r'^  version "[^"]*"$', f'  version "{version}"',
                      text, count=1, flags=re.M)
    if n != 1:
        sys.exit("no version line in the formula")

    missing = []

    def fill(m):
        name = f"r12e-{version}-{m.group('target')}.tar.gz"
        sha = sums.get(name)
        if sha is None:
            missing.append(name)
            return m.group(0)
        return m.group(1) + m.group("ver") + m.group(3) + sha + '"'

    text = PAIR.sub(fill, text)
    FORMULA.write_text(text)

    print(f"{FORMULA}: version {version}")
    for name in missing:
        print(f"  no checksum for {name}, placeholder kept", file=sys.stderr)
    return 1 if missing else 0


if __name__ == "__main__":
    sys.exit(main())
