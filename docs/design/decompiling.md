# Decompiling

`crates/e5r-decomp`, with `crates/e5r-api` driving it

## What it is for

SSA IR becomes C. Not the source, which is gone: a statement of what the
machine does, in C's notation, with everything it cannot express named rather
than hidden.

## The decision that shaped it

**The gate is running the output, not compiling it.**

Compiling was the first gate, and it is necessary: a structuring bug that
drops a brace or an expression rebuilder that emits an unbalanced cast fails
loudly under `clang -c`. But it proves the output is well formed and nothing
else. An inverted comparison compiles. A missing truncation compiles. A shift
by the wrong amount compiles.

So the second gate compiles the output **and runs it**. Every pure function in
the corpus, meaning one whose whole behaviour is its return value, is
decompiled, compiled, called on 36 argument vectors, and compared against the
IR interpreter, which is itself measured against a real processor. Nothing in
that loop is the decompiler checking itself.

The first time it ran, 130 of 225 functions returned a different answer from
the machine. Three classes accounted for most of it:

- Both extensions name the width they extend **from** as well as the width they
  extend to, and the emitter wrote only the second. Since every local is
  declared at its whole register's width, `(uint64_t)x` after a 32-bit add
  carried the bits above 32 along and the extension did nothing.
- Signed division, remainder and shift took their width from the size of the
  location holding an operand rather than from the operation, so a 32-bit
  `sdiv` came out as a 64-bit one.
- `x != y && y <= x` is `y < x`, and the rewrite that recognizes a signed
  comparison in the flag algebra emitted `x < y`. Every `<` and `<=` in a
  source program reached the output meaning its complement, on both
  architectures at every optimization level, for as long as the decompiler had
  existed.

None of the three was visible by reading the output, and the compile gate
passed throughout.

## Structuring

Regions, not gotos: `Seq`, `If`, `While`, `Infinite`, `Switch`, plus `Break`,
`Continue` and `Goto` for what is left. Post-dominators give the join points,
and tail duplication with a small budget removes the common cases that would
otherwise need a label.

**The goto count is published per corpus.** Structuring that gives up produces
a labelled goto, which is honest, and is also the thing to improve, so the
share of functions needing one is a ceiling that only comes down.

## Expressions

The rebuilder turns SSA into expression trees, recognizing what the machine
does with pointers: `base + index * stride + offset` becomes an element or a
field access when the shape analysis knows the pointer's layout, and stays
arithmetic when it does not. Flag algebra becomes comparisons. Reciprocal
multiplication should become division and does not yet, which the scorecard
says.

## What it deliberately does not do

**It does not guess a type it has not got evidence for.** A pointer's shape is
inferred from the offsets the code touches through it, which is a statement
about what was observed and not a declaration. Where the code does something
the emitter has no C for, a named helper appears (`__bits`, `__clobbered`,
`__condition`, `__indirect_branch`) and the count of unmodelled operations is
reported with the function.

**It does not silently drop anything.** Code disappearing from the output is
the most serious class of bug this subsystem can have, because the reader has
no way to notice.

## How it is measured

`clang -c` on the whole unit; the roundtrip gate above; the goto ceiling; and a
port of Ghidra's decompiler datatests, which is a third-party statement of what
a decompiler ought to get right. Each datatest that still fails is an
`#[ignore]` naming the defect, so the list of known defects is in the test
suite rather than in someone's head.
