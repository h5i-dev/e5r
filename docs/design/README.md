# Design documents

One per subsystem, in the order a binary passes through them. Each says what
the subsystem is for, the decision that shaped it, and what it deliberately
does not do. They are not API references; the code is the API reference.

| document | crate | what it is about |
| --- | --- | --- |
| [loading.md](loading.md) | `r12e-format` | turning a file into an address space, and refusing to guess |
| [decoding.md](decoding.md) | `r12e-arch` | bytes to instructions, and why the gate is another disassembler |
| [lifting.md](lifting.md) | `r12e-ir` | instructions to IR, and why a processor is the oracle |
| [recovery.md](recovery.md) | `r12e-analysis` | finding functions, and the difference between evidence and a scan |
| [decompiling.md](decompiling.md) | `r12e-decomp` | IR to C, and why running the C is the only real gate |
| [db.md](db.md) | `r12e-db` | the annotation store, and why it merges |

## The rule they all share

Three ideas run through every one of these, and where a document does not
repeat them it is because they are assumed.

**Wrong and missing are different.** A wrong answer is a bug with no
allowance and a test asserts zero of them. A missing answer is a gap with a
number, a floor or a ceiling that moves one way, and it stays in
`docs/scorecard.md` even when it is unflattering. Collapsing the two is how a
tool comes to be confidently wrong, which is worse than useless to someone
who has to trust it.

**An external oracle wherever one exists.** A decoder is measured against
`objdump` and `llvm-objdump`; a lifter against what a processor did with the
same instructions; a demangler against `c++filt`; debug information against
`readelf`; a merge against `git merge`; a decompiler against running its own
output. A number that compares the tool against itself is not evidence.

**Say what is not known.** An analysis that cannot work something out reports
that rather than guessing, and the type system makes the difference visible:
an `Option`, an explicit `Unresolved`, a `Strength` on the evidence. The
`Strength` ladder is `Heuristic < Inferred < Proven < Asserted`, and a
consumer is free to ask for only the top of it.
