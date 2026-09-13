# Resource limits and the one unsafe block

`crates/r12e-core/src/error.rs`, and the exceptions listed at the end.

Two of M12's items are policies rather than code: what this tool does with a
count it read out of a file it does not trust, and where it uses `unsafe`.
Both are written down here so that an exception has to be argued rather than
merely added.

## The rule for a count read from a file

**No count taken from input is used to allocate, to size a loop, or to bound a
walk until it has been checked against what actually fits in the file.**

A section header claiming 4,000,000,000 relocations is not a large file, it is
a 64-byte file with a large number in it. Believing the number is how a
loader turns a 200-byte input into an out-of-memory kill. This is not
theoretical: three loops written without the rule, in one session, took this
repository's test suite from finishing in three seconds to not finishing at
all. A DWARF unit walk that could fail to advance, an unbounded abbreviation
table, and a relocation count of `sh.size / 24` where `sh.size` was 7x10^17.

In practice this means, in this order:

1. **Bound by the file.** Compute how many entries of this size fit in what
   remains of the section, and take the smaller of that and the declared
   count. A declared count above it is a warning on the object, not an error:
   the file said something impossible about itself and the user should know.
2. **Bound by the cap.** `Caps` carries a ceiling per kind, below. Exceeding
   one is also a warning, and the walk stops there rather than continuing.
3. **Check the cursor advanced.** Every loop over variable-length records
   asserts progress. A record that decodes to zero length is the difference
   between a parse error and a hang.
4. **Read through the reader.** `Reader` returns a typed error for a read past
   the end. Indexing a slice directly is how a five-byte file beginning with
   the ELF magic panicked, which the mutation fuzzer found on its first run.

Nothing allocates from a count before step 1. `Vec::with_capacity` on a number
from a file is the specific mistake this rule exists to prevent.

## The caps

Defaults in `Caps::default()`. They are deliberately generous: a cap is the
last line, not the first, and a legitimate binary should never meet one.

| cap | default | what it bounds |
| --- | --- | --- |
| `sections` | 65,536 | sections or segments in one container |
| `symbols` | 16,777,216 | symbols in one table |
| `relocations` | 16,777,216 | relocations in one table |
| `string_len` | 65,536 | bytes in one string before it is called unterminated |
| `function_insns` | 1,048,576 | instructions in one function before analysis gives up |
| `function_blocks` | 262,144 | basic blocks in one function |
| `jump_table_entries` | 65,536 | entries in one recovered jump table |

Every cap is a field a caller can lower. A tool embedding this crate to triage
untrusted samples should lower them; the defaults suit an analyst looking at a
binary they chose to open.

Two caps are not about hostile input at all. `function_insns` and
`function_blocks` bound analysis of a function that is real but pathological,
usually machine-generated dispatch, and hitting them marks the function
incomplete rather than dropping it.

## How the rule is checked

Not by review. Every loader has a mutation-fuzzing test in the ordinary test
suite, seeded from the real corpus and bounded by time: hundreds of
truncations and thousands of targeted corruptions per format, each of which
must return in bounded time with a self-consistent object or a clean error.
The corruptions are not uniformly random, because uniformly random bytes
rarely produce a large count: they are runs of `0xff` and runs of ASCII `9`,
which is how a size or an entry count becomes enormous in practice.

## `unsafe`

Every crate is `#![forbid(unsafe_code)]` except `r12e-cli`, which is
`#![deny(unsafe_code)]` so that one audited call can opt in with a written
reason. There is exactly one, and this is it:

```rust
#[allow(unsafe_code)]
fn map_file(file: &std::fs::File) -> std::io::Result<memmap2::Mmap> {
    unsafe { memmap2::Mmap::map(file) }
}
```

**Why it is needed.** `info` on a 500 MB binary should be instant, and reading
the file into a `Vec` costs 500 MB and the time to copy it. Mapping costs the
pages actually touched, which for a header parse is a handful.

**What makes it unsafe.** A memory mapping is a promise that the bytes will
not change underneath the reader, and the operating system does not make that
promise: another process can truncate the file while the mapping lives, and
touching a page past the new end raises SIGBUS.

**Why it is acceptable here.** Nothing in this program writes to the mapping,
and the mapping is dropped when the command ends, so the window is the
lifetime of one command. A truncation racing a read produces a corrupted read,
and every loader already treats its input as hostile, so a corrupted read is
an ordinary error rather than a new failure mode. The residual risk is the
SIGBUS, which is a crash and not a wrong answer: this tool would rather stop
than say something untrue.

**What would remove it.** Reading the file instead, at the cost above. That is
the right trade for a caller who must never crash, and the wrong one for the
common case, so the binary maps and a library consumer can pass its own bytes.
