# Loading

`crates/e5r-format`

## What it is for

A file on disk becomes an address space with sections, symbols, imports,
exports, relocations and whatever the container said about itself. Everything
above this layer asks questions about addresses, so the loader's job is to be
the only place that knows what a file format is.

## The decision that shaped it

**Every count in a file is attacker-controlled.** A section header says there
are 4,000,000,000 relocations; a DWARF unit says its abbreviation table has
2^61 entries; an archive member says it is longer than the file. The loader is
the first code to touch bytes nobody chose, and it is the code most likely to
be pointed at something hostile on purpose.

So: no count read from a file is ever used to allocate or to bound a loop
before it has been checked against what fits in the file. Every walk checks
that its cursor advanced. `Caps` carries the per-kind ceilings, and exceeding
one is a warning on the object, not a panic and not a silent truncation.

This is not theoretical caution. Three loops written without it, in one
session, took the test suite from finishing in three seconds to not finishing
at all: a DWARF unit walk that could fail to advance, an unbounded abbreviation
table, and a relocation count of `sh.size / 24` where `sh.size` was 7x10^17.

## What it does

- ELF, PE and Mach-O, plus raw images when the caller says the architecture and
  the base address.
- Relocations applied to code in relocatable objects, which is what makes a
  `.o` file analyzable at all: an unrelocated `bl` encodes an offset of zero.
- DWARF 4 and 5, including the parts that only work in a `.o` once relocations
  are applied. `.debug_addr` and `.debug_str_offsets` need them, and without
  them every clang-produced DWARF 5 function resolves to address zero and every
  name to the producer string.
- `.eh_frame`, which survives stripping and carries function boundaries.
- Language runtime metadata: Go's `pclntab`, Rust's symbol conventions,
  Objective-C's class and method lists.
- `ar` archives, which are listed rather than loaded, for the reason below.
- Overlays and entropy, which are measured rather than judged.

## What it deliberately does not do

**It does not pick a member of an archive.** An archive has no architecture,
no entry point and no memory map, so it cannot be an `Object` without choosing
one member and making every later answer about bytes the caller did not
choose. `archive::open` is separate, and `load` refuses an archive with a
message saying what to do instead.

**It does not render a verdict about packing.** `overlay::analyze` reports
that a section is writable and executable, that its file bytes are far fewer
than the memory it claims, that a 4 KB window has entropy 7.9. Those are
facts. "This is packed" is not, and the only place a product is named is where
a section carries that product's own signature, at which point the finding says
so in those words.

**It does not run anything.** No emulated unpacking, no loader stubs.

## How it is measured

`objdump`, `readelf` and `llvm-readobj` for what the containers say. For
robustness, hundreds of truncations and thousands of targeted corruptions of
real files per format, each of which must return in bounded time with a
self-consistent object or a clean error, and never panic.

The false-positive gate on the overlay pass matters as much as the true
positives: fourteen ordinary binaries, seven linked and seven relocatable,
across Go, Rust, C and C++, must produce no overlay and no finding at
`Inferred` or above. Getting that clean is what forced `described_end` to
account for the program and section header tables, the COFF symbol and string
tables, PE's `SizeOfHeaders` and its certificate directory, which is a file
offset rather than an RVA, and the Mach-O linkedit commands.
