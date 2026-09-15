# Function recovery

`crates/e5r-analysis`

## What it is for

Deciding what is code, where functions start and end, what references what,
and which calls never return.

## The decision that shaped it

**Evidence before scanning, and the evidence is recorded.** Every function
carries how it was found and how strongly: a symbol table entry, an
`.eh_frame` FDE, a PE `.pdata` entry, the target of a direct call, a jump
table entry, or last of all a prologue that looks like one. `Strength` orders
them, and the output prints it.

That ordering is not decoration. A user looking at a stripped binary needs to
know which boundaries are facts and which are a scanner's opinion, because the
two fail differently and the second one needs checking. `--no-scan` turns the
heuristic layer off entirely, leaving only evidence-led discovery, and the
difference between the two runs is itself information.

## Iteration to a fixed point

Discovery is a loop. A newly found function yields new call targets; a
resolved jump table yields new blocks; a function shown never to return
changes which code after a call is reachable at all. The loop runs to a fixed
point and the round count is reported, because a binary that needs many rounds
is telling you something about itself.

**Feedback edges.** Whether a function returns is often only decidable from
its callers, so the answer propagates both ways rather than being decided once
on the way down.

## Jump tables

A jump table is where a control flow graph is either recovered or lost, and
the recovery is pattern-driven per architecture: find the bound, the base, the
entry width and the entry encoding, then prove each target lands in executable
memory. When any part of that is not established, the indirect branch stays
unresolved and the function stays incomplete. An incomplete function is
reported as incomplete rather than as a function with fewer blocks than it has.

## What it deliberately does not do

It does not emulate, and it does not follow data through memory to decide what
is code. Both produce answers that are right often enough to be trusted and
wrong often enough to be dangerous.

## How it is measured

Recall against the symbol table on binaries where one exists, then the same
binaries stripped. Against Ghidra headless on the same file, reporting what
each found that the other did not, and the wall clock for both. The numbers
are in `docs/scorecard.md`.
