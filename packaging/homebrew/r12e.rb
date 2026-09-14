# A DRAFT. This formula has never been run: there is no brew on the machine it
# was written on, so `brew install --build-from-source`, `brew audit --strict`
# and `brew test` are all unexercised. Treat it as the shape of the formula
# rather than as a tested one, and run those three before pointing a tap at it.
#
# It installs the release archive rather than building from source, because the
# Linux archives are the static musl binaries and a source build would want a
# Rust toolchain for a tool that ships as one file with no runtime dependency.
#
# The sha256 lines are filled in from a release's SHA256SUMS by
# scripts/update-homebrew.py; the placeholders below are not hashes of
# anything.
class R12e < Formula
  desc "Reverse engineering toolkit: disassembler, decompiler and binary diff"
  homepage "https://github.com/h5i-dev/r12e"
  version "0.1.0"
  license "Apache-2.0"

  on_macos do
    on_arm do
      url "https://github.com/h5i-dev/r12e/releases/download/v#{version}/r12e-#{version}-aarch64-apple-darwin.tar.gz"
      sha256 "not-filled-in"
    end
    on_intel do
      url "https://github.com/h5i-dev/r12e/releases/download/v#{version}/r12e-#{version}-x86_64-apple-darwin.tar.gz"
      sha256 "not-filled-in"
    end
  end

  on_linux do
    on_arm do
      url "https://github.com/h5i-dev/r12e/releases/download/v#{version}/r12e-#{version}-aarch64-unknown-linux-musl.tar.gz"
      sha256 "not-filled-in"
    end
    on_intel do
      url "https://github.com/h5i-dev/r12e/releases/download/v#{version}/r12e-#{version}-x86_64-unknown-linux-musl.tar.gz"
      sha256 "not-filled-in"
    end
  end

  def install
    bin.install "r12e"
    # Both are generated from the command tree, so neither can describe a
    # command that does not exist. Generating them here rather than shipping
    # them in the archive keeps them matched to the binary being installed.
    (man1/"r12e.1").write Utils.safe_popen_read(bin/"r12e", "manpage")
    generate_completions_from_executable(bin/"r12e", "completions")
  end

  test do
    assert_match version.to_s, shell_output("#{bin}/r12e --version")
    # The binary is a file the tool can read on every platform this formula
    # installs on, so the test analyzes it rather than shipping a fixture.
    assert_match "entry", shell_output("#{bin}/r12e info #{bin}/r12e")
  end
end
