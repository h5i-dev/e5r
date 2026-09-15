# The annotation store

`crates/e5r-db`

ROADMAP.md M7 says this subsystem gets designed before it gets coded, because
it is the feature that distinguishes e5r from the incumbents. This is that
design, kept up to date with what was built.

## The problem

Reverse engineering is weeks of work producing knowledge that lives nowhere
but in one person's project file. Two people cannot work on the same binary
and combine what they learned. Nobody can review the work. Rebuilding the
binary throws it away. A project file is a binary blob a version control
system cannot merge, diff or blame.

Every incumbent has this problem and it is not incidental to them: it follows
from identifying everything by address into a database keyed by that address.

## The decision that shaped it

**Identify by content, store as text, merge with git.**

### Content anchors

A function is identified by three things, checked in this order:

1. An exact hash of its bytes. Same binary, instant, certain.
2. A fingerprint of its instruction-shape stream with branch targets excluded.
   This survives a rebase and a relink, because moving code changes the
   displacements and not the shapes.
3. Its address, as a tiebreak and as the last resort.

Resolution reports **which of the three matched**, as a `Resolution`, and the
caller decides what that is worth. Something that matched on the address alone
after a rebuild is telling you the code it was written against is not there,
and an operation that would write to the binary refuses on that basis by
default.

Anchors exist for things that are not functions too: a data object, an address
inside a function, a structure field, a call site. All of them are an anchor
plus a byte offset.

### The log

One assertion per line. Append-only. Sorted by a sequence number with a
content hash as the deterministic tiebreak, so two people who made assertions
concurrently produce a file whose order does not depend on whose was written
first.

```
name 3f0a1c2b8e7d4a19 d41d8cd98f00b204 12 0 seq=7 who=ht value=parse_header
```

The current state is a fold over the log: the last assertion for a key wins,
and undo is a new assertion rather than an edit, so history is never rewritten.

### Merging

The file is line-oriented and append-only, which means `*.e5r merge=union` in
`.gitattributes` makes git merge two branches of annotations with no conflict
markers. Two analysts on separate branches merge like two people editing
different functions in source, because that is what they are doing.

**The oracle for this is `git merge` itself.** Not a model of merging: the real
program, run on real repositories, over every scenario in this document
including the ones designed to conflict.

The tool prints a note when it writes a log into a git repository that has no
union rule, rather than editing someone's `.gitattributes` unasked.

## Signatures

The same anchor machinery, used for a different question. A signature library
built from a binary with symbols names the same code in a binary without them.
A signature identifies a function by what it is rather than where it is, so a
statically linked library recovers its names.

The measure is recall **with zero wrong names**. A wrong name is worse than no
name, because the reader will believe it.

## Patch sets

Also the same machinery. An edit is anchored to the code around it and carries
the bytes it expects to find, so a patch written against one build lands on the
right instruction in the next one and says how it found it.

Three properties, each of which exists because the alternative is a corrupted
binary:

- An edit is always the same length as what it replaces. A different length
  would move every byte after it and invalidate the rest of the set.
- A set applies as a whole or not at all. A half-applied patch set is the worst
  possible outcome and it is unreachable by construction: the preview proves
  every edit before the first byte is written.
- Overlapping edits are a conflict, not an order-dependent result.

`apply` refuses by default when an edit resolved on its address alone.
`revert` does not, because a patched binary no longer holds the bytes the
anchor fingerprinted, which is exactly what applying it did, and the expected
bytes are the exact bytes the apply wrote.

## Project files

What it takes to reopen a session: the binary by path **and by content**, the
load configuration, the analysis options, and the files holding the
annotations, signatures and patches. Opening one against a rebuilt binary says
so rather than answering about bytes that are not there. A binary that only
moved is still the right one, and that is a distinct verdict from both of the
others.

## What it deliberately does not do

**It is not a database.** No index to keep consistent, no schema migration, no
lock file, no daemon. A text file and a fold over it.

**It does not store analysis results.** Only assertions a person made. The
analysis is cheap enough to redo and it is the thing most likely to be wrong;
caching it would be caching a guess and then defending the cache.

**It does not resolve an ambiguous anchor by picking one.** Two functions with
the same shape and the same byte hash resolve to `Resolution::Ambiguous`, and
the caller is told.
