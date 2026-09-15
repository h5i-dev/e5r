# e5r

Reverse engineering from the command line. Load a binary, recover its
functions, disassemble them, decompile them, and ask questions about what is
there.

Every command takes `--json` and prints the same information in a form a
script can read. Exit codes are `0` for success, `1` for nothing found, `2` for
a bad command line, and `3` for input that could not be read.

```
cargo build --release
./target/release/e5r info /bin/ls
```

## Installing

### A release binary

Every release attaches one archive per platform, a `SHA256SUMS` file and a
signature over it. Unpack and put `e5r` on your path:

```
tar -xzf e5r-0.1.0-x86_64-unknown-linux-musl.tar.gz
install -m755 e5r-0.1.0-x86_64-unknown-linux-musl/e5r /usr/local/bin/
```

Check what you downloaded first. The checksums cover the archives, and the
signature covers the checksum file. Signing is Sigstore keyless, so the
identity is the release workflow itself and there is no key to distribute:

```
sha256sum -c SHA256SUMS
cosign verify-blob --signature SHA256SUMS.sig --certificate SHA256SUMS.pem \
  --certificate-identity-regexp '^https://github.com/h5i-dev/e5r/' \
  --certificate-oidc-issuer https://token.actions.githubusercontent.com \
  SHA256SUMS
```

| Platform | Archive |
| --- | --- |
| Linux x86-64 | `e5r-VERSION-x86_64-unknown-linux-musl.tar.gz` |
| Linux AArch64 | `e5r-VERSION-aarch64-unknown-linux-musl.tar.gz` |
| macOS Apple silicon | `e5r-VERSION-aarch64-apple-darwin.tar.gz` |
| macOS Intel | `e5r-VERSION-x86_64-apple-darwin.tar.gz` |
| Windows x86-64 | `e5r-VERSION-x86_64-pc-windows-msvc.zip` |

### What the Linux build guarantees

The Linux archives are static musl binaries. There is no dynamic loader, no
`libc.so` to find and no glibc version to match, so one file runs on any Linux
with the same architecture: a current distribution, an eight-year-old one,
Alpine, a distroless container, or a rescue initramfs. `ldd` on it says it is
not a dynamic executable, and that is the whole claim:

```
$ file e5r
e5r: ELF 64-bit LSB pie executable, x86-64, static-pie linked, stripped
```

Nothing outside the binary is needed at run time. The fixture corpus under
`fixtures/` is what the test suite measures against; an installed `e5r` never
reads it, and no data file, configuration or cache directory is required to
start.

### From source

```
cargo install --git https://github.com/h5i-dev/e5r e5r-cli
cargo install --path crates/e5r-cli          # from a checkout
```

The dependency list is deliberately short (`serde` and `serde_json`, `clap`,
`memmap2`, `rayon`, and nothing else), and no crate in the workspace has a
build script or links against a C library. That is what makes cross-compiling
a matter of naming a target rather than assembling a sysroot: the loaders and
decoders are written here rather than pulled in, so nothing in the graph needs
a platform toolchain.

To build the release archives yourself, for any target whose standard library
rustup has installed:

```
scripts/build-release.sh x86_64-unknown-linux-musl aarch64-unknown-linux-musl
```

It links the musl targets with the `rust-lld` that comes with the toolchain, so
cross-building the other architecture's static binary needs no musl gcc, no
`cross` and no container. The archives and the `SHA256SUMS` land in `dist/`.
The tarball adds no variation of its own: entries are sorted and ownership and
timestamps are zeroed, so the same binary always packs to the same checksum.

### install.sh

```
curl -fsSL https://raw.githubusercontent.com/h5i-dev/e5r/main/install.sh | sh
```

It works out the platform, asks the releases API for the latest tag, downloads
that archive, **verifies it against the release's `SHA256SUMS` and refuses to
install if it does not match**, and puts the binary in `/usr/local/bin` with
`install` rather than `mv`, so a `sudo` install does not leave a user-writable
binary in a root-owned directory.

Four environment variables, all of them for a case the default does not cover:

| | |
| --- | --- |
| `E5R_INSTALL_DIR` | somewhere other than `/usr/local/bin` |
| `E5R_VERSION` | a tag other than the latest |
| `E5R_BASE_URL` | a mirror, or a staged release that is not published yet |
| `E5R_SKIP_CHECKSUM` | install without verifying, said out loud on stderr |

There is no Homebrew formula. There was a draft one, and it was deleted rather
than published: it had never been run against `brew`, and a tap is a second
place a version number has to be right. A script that has been run against a
real archive, and refuses a tampered one, is the smaller promise and the kept
one.

## What it will and will not tell you

Every recovered fact carries the evidence for it, and the strength of that
evidence is printed next to it:

| Strength | Meaning |
| --- | --- |
| `asserted` | A person or an agent wrote it in the annotation log. |
| `proven` | The file says so: a symbol table, debug information, an entry point, an unwind record. |
| `inferred` | Something in the code implies it: a call target, a jump table, an import thunk. |
| `heuristic` | A pattern suggests it: a prologue, a linear sweep, a pointer in data. |

Where a thing cannot be worked out, it is reported as unknown rather than
guessed at. A function whose control flow could not be followed to the end is
marked incomplete; a jump table whose bound could not be established is left
unresolved; an instruction the lifter does not model appears as unmodelled in
the output rather than being approximated.

## Looking at a file

```
e5r info FILE           container, architecture, entry, what the loader noticed
e5r sections FILE       sections and where they are mapped
e5r symbols FILE        symbols the container names
e5r imports FILE        what it needs from elsewhere
e5r exports FILE        what it offers
e5r strings FILE        strings found in the image, by section
e5r stats FILE          counts: functions, blocks, instructions, references
```

`info` and the listings above need only the container, so they are instant
whatever the size of the file.

## Code

```
e5r funcs FILE                     every recovered function and its evidence
e5r disas FILE TARGET              disassemble a function, an address, or `all`
e5r xrefs FILE TARGET [--from]     references to an address, or from one
e5r decompile FILE TARGET          pseudo-C for a function, or for `all`
e5r emulate FILE TARGET [ARGS...]  run a function and report what it did
```

`TARGET` is an address (`0x401000`, `401000`), a symbol name, or `all`.

The decompiler's output says what the machine does in C's notation. It does
not claim to be the source. Where the control flow does not fit an `if` or a
`while`, a labelled `goto` appears rather than a shape that is not there, and
the number of them is printed above the function: that is the honest measure
of how well the structuring worked. Where the binary carries debug
information, parameters are named and typed as the compiler recorded them;
where it does not, they are recovered from what the code does with them.

`emulate` runs the function in the same interpreter the lifters are tested
against. Nothing escapes the process: memory is a copy of the image, a system
call stops the run, and a budget bounds it.

## Windows

A PE keeps its debug information in a separate `.pdb`, so it is looked for: at
the path the linker recorded, and beside the binary, which is where the file
usually actually is.

**A database from the wrong build is refused**, with a note saying so. Symbols
from a different build are worse than no symbols, because they are confidently
wrong, so the identity the image asks for is checked before anything in the
database is believed.

```
$ e5r funcs prog.exe
0x140001000  ...  proven  program database  compare_points
0x140001020  ...  proven  program database  walk
```

Without it, the same binary yields only its entry point.

`e5r info` reports `pe.pdb`, `pe.pdb.key` and `pe.pdb.age`, which together
are what a symbol server is indexed by.

## C++

```
e5r classes prog                # the hierarchy
e5r classes prog --members      # and every member function, with its `this`
```

Classes come from the type information where a binary has it, and from the
virtual tables alone where it does not. Both Itanium and Microsoft layouts are
read. Every claim says what it rests on: a name read out of RTTI or a mangled
symbol is proven, one inferred from what a function writes is not, and the two
are never printed as each other.

A binary built with `-fno-rtti` degrades and says which it is:

```
13 class(es) from 13 table(s); 9 named by symbol, 0 only by type information
  (unknown, absent (-fno-rtti): vtables only, no hierarchy)
```

`--members` lifts every member function to see what it touches through
`this`, which on a real C++ library takes tens of seconds, so it is off by
default.

## Structure and types

```
e5r shapes FILE TARGET     what the pointers a function takes point at
e5r vtables FILE           virtual tables and the classes they belong to
```

`shapes` reports the offsets a function touches through each pointer it is
given, and the element size when it walks an array of them. It reports what it
saw rather than a conclusion: it does not name fields and it does not average
two disagreeing strides into one.

## Asking questions

```
e5r query FILE 'functions where insns > 100 and name ~ "crypt"'
e5r query FILE 'strings where length >= 20 and text ~ "/etc/"'
e5r query FILE 'xrefs where kind = call and to = 0x401000 limit 20'
```

Entities: `functions`, `strings`, `symbols`, `imports`, `exports`, `sections`,
`xrefs`. Operators: `=` `!=` `<` `<=` `>` `>=`, `~` for contains and `!~` for
does not, combined with `and`, `or`, `not` and brackets. Numbers may be
decimal or hexadecimal. A field that does not exist is a mistake in the query
and is reported as one, with the fields there are.

## Comparing builds

```
e5r diff OLD NEW [--all]
```

Functions are matched across the two builds by a fingerprint of their
instruction shape rather than by address, so the match survives a relink.
Matched, changed, added and removed are reported with a similarity score.
Given a vulnerable build and a patched one, this points at the change.

## Naming a stripped binary

```
e5r sig FILE create -o LIBRARY      a signature for every named function
e5r sig FILE apply LIBRARY          name what the library recognizes
```

A signature identifies a function by its content rather than its address, so a
library built from a binary with symbols names the same code in one without
them. It refuses every coin flip: two signatures that disagree about a hash
name nothing, a short function is not identified by shape alone, and import
thunks are excluded because they differ only in an offset.

The file is sorted text, so a signature library reviews in a diff.

## An interactive session

```
$ e5r repl prog
38 function(s) in prog. `help` lists the commands, `quit` leaves.
0x400144> f
0x400144> seek parse_header
0x400180> dec
0x400180> q 'calls to "memcpy" where arg3 is not bounded'
0x400180> quit
```

The commands are the ones above, spelled the same way and without the file, so
nothing has to be learned twice. `seek` moves, and the commands that take an
address use where you are when given none. Short forms exist only for the ones
typed a hundred times an hour: `d` `dec` `f` `i` `s` `x` `q` `?`.

The point is not saved typing. Analyzing a large binary takes seconds, and a
session pays it once: five `funcs` on libcrypto is 1.26s as five invocations
and 0.63s in one session, and the gap widens with the binary.

A session runs the same code the command line does, so the two cannot disagree
about what a command means.

## Telling it what you know

An assertion is not a note on the side: it changes the analysis. Decompile,
see what the engine could not work out, say what it is, decompile again.

```
$ e5r decompile prog nestedoffset
uint64_t nestedoffset(uint64_t arg0, uint64_t arg1, uint64_t arg2)
{
    return (uint64_t)((uint64_t)(uint32_t)*(uint32_t *)(arg0 +
        ((int64_t)(int32_t)((uint32_t)arg1 + (uint32_t)arg2) << 2) + 12));
}

$ e5r annotate prog type nestedoffset \
    "int nestedoffset(struct outer { int header; int pad; int array[8]; } *ptr, int a, int b)"

$ e5r decompile prog nestedoffset
struct outer { int32_t header; int32_t pad; int32_t array[8]; };

int32_t nestedoffset(struct outer *ptr, int32_t a, int32_t b)
{
    return (int32_t)((uint64_t)(uint32_t)*(uint32_t *)((uint64_t)ptr +
        ((int64_t)(int32_t)((uint32_t)a + (uint32_t)b) << 2) + 12));
}
```

The binary above has no debug information at all. The declaration is refused
if it does not parse, so a typo is caught when it is typed.

An assertion outranks what the engine recovered, and where the two disagree
the disagreement is recorded rather than hidden: declare two parameters where
the code reads four argument registers and `--json` reports the other two as
conflicts. That is the point of the strength ladder, not a caveat on it.

`--json` also carries every variable with its name, type, size, role and
where the machine kept it, so a program driving this can see what there is to
assert:

```
$ e5r decompile prog nestedoffset --json
  ...
  "asserted": true,
  "variables": [
    { "name": "ptr", "type": "struct outer *", "role": "parameter", "storage": "register+56" },
    { "name": "a",   "type": "int32_t",        "role": "parameter", "storage": "register+48" },
    { "name": "b",   "type": "int32_t",        "role": "parameter", "storage": "register+16" }
  ]
```

## Annotations

```
e5r annotate FILE name TARGET NAME
e5r annotate FILE comment TARGET TEXT
e5r annotate FILE list
e5r annotate FILE undo
```

Annotations are written to a log beside the binary, keyed to a content anchor
rather than an address, so the work survives a rebuild. The log is text sorted
by that anchor, so two analysts on separate branches merge without conflict
markers. Add this to `.gitattributes`:

```
*.e5r merge=union
```

## Containers that are not one program

An `ar` archive holds objects rather than being one, so it is listed rather
than loaded: picking a member silently would make every later answer about
bytes you did not choose.

```
e5r archive libfoo.a              # members, sizes and offsets
e5r archive libfoo.a --symbols    # and what each one defines
```

GNU and BSD archives, long names, both symbol index forms, and thin archives.

```
e5r overlay firmware.exe
```

reports where the headers stop describing the file, what is appended past that
point, and the entropy of every section with a peak per 4 KB window, which is
how a packed region inside an ordinary-looking section shows up.

Findings carry a strength and never a verdict. A section that is writable and
executable is a fact; what put it there is not. A packer is named only where a
section carries that packer's own signature.

## Patching

An edit is anchored to the code around it and carries the bytes it expects to
find, so a patch written against one build still lands on the right
instruction in the next one, and says how it found it.

```
e5r patch prog record 0x401234 --asm "nop" --note "skip the check" -o fix.e5r-patch
e5r patch prog record 0x401234 --bytes 90909090 -o fix.e5r-patch
e5r patch prog record 0x401234 --asm "mov eax, 1" --pad-to 8 -o fix.e5r-patch
e5r patch prog preview fix.e5r-patch     # where it lands, what it overwrites
e5r patch prog apply   fix.e5r-patch -o prog.patched
e5r patch prog.patched revert fix.e5r-patch -o prog
e5r patch prog merge a.e5r-patch b.e5r-patch -o both.e5r-patch
```

`--asm` assembles at the target address, because a branch encodes a
displacement from where it sits. It accepts what `e5r disas` prints, so a
line can be copied out, changed, and assembled back. `--pad-to` fills the rest
with no-ops: an instruction that encodes shorter than the one it replaces
would otherwise leave the bytes after it meaning something they did not mean.

A set applies as a whole or not at all. Overlapping edits are a conflict
rather than an order-dependent result, and an edit is always the same length
as what it replaces, because a different length would move every byte after it
and invalidate the rest of the set.

`apply` refuses by default when an edit resolved on its address alone, since
that means the code it was written against is no longer there; `--allow-address-only`
overrides. `revert` does not refuse, because a patched binary no longer holds
the bytes the anchor fingerprinted, which is exactly what applying it did.

## Saving a session

```
e5r project new prog -o prog.e5r-proj --set scan_gaps=true
e5r project add prog.e5r-proj --signatures libc.e5r-sig --patch fix.e5r-patch
e5r project verify prog.e5r-proj
e5r project show prog.e5r-proj
```

A project names its binary by content as well as by path. Opening it against a
rebuilt binary says so rather than answering about bytes that are not there,
and a binary that only moved is still the right one.

## Driving it from a program

Every command takes `--json`. The schema is named in every document
(`"schema": "e5r/1"`) and addresses are hex strings so nothing is lost to a
float.

## Shell integration

```
e5r completions bash > /etc/bash_completion.d/e5r
e5r completions zsh  > ~/.zsh/completions/_e5r
e5r completions fish > ~/.config/fish/completions/e5r.fish
e5r manpage          > /usr/local/share/man/man1/e5r.1
```

Both are generated from the command tree, so they cannot describe a command
that does not exist.

## Common options

| Option | Effect |
| --- | --- |
| `--json` | Print the same information as JSON. |
| `--base ADDR` | Load a raw image, or rebase a relocatable one, at an address. |
| `--arch NAME` | The architecture of a raw image, which has no header to say. |
| `--threads N` | How much of the analysis to run in parallel. The output does not depend on this. |
| `--color WHEN` | `auto` (a terminal only), `always`, or `never`. `NO_COLOR` is honoured. |
| `--no-pager` | Do not page, even when a terminal is reading. `PAGER` and `E5R_PAGER` choose the pager. |
| `--budget SECONDS` | Stop after this long and report what was finished. |
| `--limit N` | Stop after this many items and report what was finished. |
| `--progress` | Show a counter on stderr. Silent when stderr is not a terminal. |

A job that runs out of budget prints why on stderr and how much is left, and
the output it already produced is still a valid document:

```
$ e5r decompile libstdc++.so.6 all --budget 3 > partial.c
e5r: out of time after 3.5s and 1024 of 5609 function(s); 4585 not done.
Raise --budget or --limit, or narrow the target.
```

Colour, paging and width-fitting happen only when a person is reading. Piped
output carries no escape sequences and is never truncated, so a listing taken
today diffs against the same listing taken a week ago.

## What is not built yet

SLEIGH languages, i386, Windows-specific entry points, an assembler, and an
interactive session. `ROADMAP.md` is the list, and it says what each milestone
is and what it is measured by.
