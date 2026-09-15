#!/usr/bin/env sh
set -e

# Everything lives in main() and main is called on the last line, so a
# truncated `curl … | sh` cannot execute a half-downloaded prefix.
main() {
  REPO="h5i-dev/r12e"
  INSTALL_DIR="${R12E_INSTALL_DIR:-/usr/local/bin}"

  for arg in "$@"; do
    case "$arg" in
      -h | --help)
        echo "Usage: install.sh"
        echo
        echo "  Installs r12e, which is one binary with no runtime dependency."
        echo
        echo "Piped into a shell, options go after \`sh -s --\`:"
        echo "  curl -fsSL https://raw.githubusercontent.com/${REPO}/main/install.sh | sh -s -- --help"
        echo
        echo "Environment:"
        echo "  R12E_INSTALL_DIR   where the binary goes (default /usr/local/bin)"
        echo "  R12E_VERSION       a tag to install instead of the latest"
        echo "  R12E_SKIP_CHECKSUM set to 1 to install without verifying"
        echo "  R12E_BASE_URL      where the archives are, for a mirror"
        exit 0
        ;;
      *)
        echo "Unknown option: $arg" >&2
        echo "Try: install.sh --help" >&2
        exit 1
        ;;
    esac
  done

  # ── the platform ───────────────────────────────────────────────────────────
  OS="$(uname -s)"
  case "$OS" in
    Linux) os="linux" ;;
    Darwin) os="macos" ;;
    *)
      echo "Unsupported OS: $OS" >&2
      echo "Windows: download the .zip from the releases page and put r12e.exe on your PATH." >&2
      exit 1
      ;;
  esac

  ARCH="$(uname -m)"
  case "$ARCH" in
    x86_64 | amd64) arch="x86_64" ;;
    arm64 | aarch64) arch="aarch64" ;;
    *)
      echo "Unsupported architecture: $ARCH" >&2
      exit 1
      ;;
  esac

  case "${os}-${arch}" in
    linux-x86_64) target="x86_64-unknown-linux-musl" ;;
    linux-aarch64) target="aarch64-unknown-linux-musl" ;;
    macos-x86_64) target="x86_64-apple-darwin" ;;
    macos-aarch64) target="aarch64-apple-darwin" ;;
    *)
      echo "Unsupported platform: ${os}-${arch}" >&2
      exit 1
      ;;
  esac

  # ── which release ──────────────────────────────────────────────────────────
  VERSION="${R12E_VERSION:-}"
  if [ -z "$VERSION" ] && [ -z "${R12E_BASE_URL:-}" ]; then
    VERSION="$(curl -fsSL "https://api.github.com/repos/${REPO}/releases/latest" \
      | grep '"tag_name"' | sed 's/.*"tag_name": *"\([^"]*\)".*/\1/')"
  fi
  if [ -z "$VERSION" ]; then
    echo "Could not determine the latest version." >&2
    echo "With R12E_BASE_URL set, R12E_VERSION has to be set too: a mirror has" >&2
    echo "no releases API to ask." >&2
    echo "Set R12E_VERSION=vX.Y.Z, or check that a release exists:" >&2
    echo "  https://github.com/${REPO}/releases" >&2
    exit 1
  fi

  TMP="$(mktemp -d)"
  trap 'rm -rf "$TMP"' EXIT

  # The version inside an archive's name has no leading `v`; the tag has one.
  BARE="${VERSION#v}"
  ARCHIVE="r12e-${BARE}-${target}.tar.gz"
  # Overridable for a mirror, and for testing this script against a release
  # that has not been published yet -- which is the difference between an
  # installer that has been run and one that has only been written.
  BASE="${R12E_BASE_URL:-https://github.com/${REPO}/releases/download/${VERSION}}"

  echo "Installing r12e ${VERSION} (${target}) → ${INSTALL_DIR}/r12e"

  if ! curl -fsSL "${BASE}/${ARCHIVE}" -o "${TMP}/${ARCHIVE}"; then
    echo "Could not download ${ARCHIVE}." >&2
    echo "  ${BASE}/${ARCHIVE}" >&2
    echo "Not every release carries every platform; the asset list is on the" >&2
    echo "releases page, and R12E_VERSION picks a different one." >&2
    exit 1
  fi

  # ── verify ─────────────────────────────────────────────────────────────────
  # Not a substitute for a signature -- the checksums come from the same origin
  # as the archive -- but it catches a truncated or corrupted download, and it
  # makes tampering with one asset alone insufficient. The release also
  # publishes SHA256SUMS.sig and SHA256SUMS.pem, which `cosign verify-blob`
  # checks and which this script deliberately does not require: cosign is not
  # on most machines, and an installer that fails without it would be one
  # people work around rather than run.
  if [ "${R12E_SKIP_CHECKSUM:-0}" = "1" ]; then
    echo "!  checksum verification skipped (R12E_SKIP_CHECKSUM=1)" >&2
  else
    if command -v sha256sum > /dev/null 2>&1; then
      actual="$(sha256sum "${TMP}/${ARCHIVE}" | cut -d' ' -f1)"
    elif command -v shasum > /dev/null 2>&1; then
      actual="$(shasum -a 256 "${TMP}/${ARCHIVE}" | cut -d' ' -f1)"
    else
      echo "Neither sha256sum nor shasum found; cannot verify the download." >&2
      echo "Install one, or re-run with R12E_SKIP_CHECKSUM=1 to accept the risk." >&2
      exit 1
    fi

    if ! curl -fsSL "${BASE}/SHA256SUMS" -o "${TMP}/SHA256SUMS"; then
      echo "Could not fetch SHA256SUMS — refusing to install unverified." >&2
      echo "Re-run with R12E_SKIP_CHECKSUM=1 to accept the risk." >&2
      exit 1
    fi

    # One file covers every archive, so the line for this one has to be found
    # rather than read off the top. Matching on the whole name and requiring
    # exactly one line is what stops a prefix collision between, say, the two
    # `aarch64` targets from verifying against the wrong digest.
    line="$(grep -F " ${ARCHIVE}" "${TMP}/SHA256SUMS" | grep -E "[ *]${ARCHIVE}\$" || true)"
    count="$(printf '%s' "$line" | grep -c . || true)"
    if [ "$count" != "1" ]; then
      echo "SHA256SUMS does not name ${ARCHIVE} exactly once (found ${count})." >&2
      exit 1
    fi
    expected="$(printf '%s' "$line" | cut -d' ' -f1)"
    if [ -z "$expected" ] || [ "$expected" != "$actual" ]; then
      echo "Checksum mismatch for ${ARCHIVE}" >&2
      echo "  expected: ${expected:-<empty>}" >&2
      echo "  actual:   ${actual}" >&2
      exit 1
    fi
  fi

  # ── install ────────────────────────────────────────────────────────────────
  # `--no-same-owner`: only `$TMP/.../r12e` is installed, with an explicit mode,
  # so this changes nothing today. It is here so an archive with more members
  # cannot carry ownership in from a tarball the operator did not build.
  tar -xzf "${TMP}/${ARCHIVE}" -C "$TMP" --no-same-owner

  # The archive holds a directory, not a bare binary, so that the README, the
  # licence and the manual travel with it.
  BIN="${TMP}/r12e-${BARE}-${target}/r12e"
  if [ ! -x "$BIN" ]; then
    echo "The archive did not contain r12e where expected:" >&2
    echo "  ${BIN}" >&2
    exit 1
  fi

  # `install` rather than `mv`: `mv` preserves the invoking user's ownership,
  # which under sudo leaves a user-writable binary in a root-owned PATH
  # directory.
  if [ -w "$INSTALL_DIR" ]; then
    install -m 755 "$BIN" "${INSTALL_DIR}/r12e"
  elif [ -d "$INSTALL_DIR" ] || [ -w "$(dirname "$INSTALL_DIR")" ]; then
    sudo install -d -m 755 "$INSTALL_DIR"
    sudo install -o root -g 0 -m 755 "$BIN" "${INSTALL_DIR}/r12e"
  else
    echo "${INSTALL_DIR} does not exist and its parent is not writable." >&2
    echo "Pick somewhere else: R12E_INSTALL_DIR=\$HOME/.local/bin sh install.sh" >&2
    exit 1
  fi

  echo "✔  r12e ${VERSION} installed: run r12e --help"

  # Said once, at the end, rather than buried in the transcript above. A PATH
  # directory the invoking user can write is not a defect this script can fix
  # -- where someone keeps their binaries is theirs to decide -- so it says so
  # rather than leaving it to be discovered.
  case ":${PATH}:" in
    *":${INSTALL_DIR}:"*) ;;
    *)
      echo "!  ${INSTALL_DIR} is not on your PATH." >&2
      echo "   Add it, or run ${INSTALL_DIR}/r12e directly." >&2
      ;;
  esac
}

main "$@"
