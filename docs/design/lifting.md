# Lifting

`crates/r12e-ir`

## What it is for

An instruction becomes a sequence of IR operations with no implicit effects.
Everything above this layer is architecture-independent, which is only true if
the lifter leaves nothing unsaid.

## The decision that shaped it

**The oracle is a processor.** Not a reference interpreter, not a second
implementation, not a table of expected states. A snippet is assembled, run on
real hardware, and the register and memory state afterwards is compared against
what the IR interpreter produced from the same bytes. This machine is aarch64,
so AArch64 runs natively and x86-64 runs under `qemu-x86_64`.

A lifter is exactly the kind of code where a plausible-looking mistake
survives review: a flag set from the wrong operand, a shift that should be
modulo the width, a zero-extension where the architecture sign-extends. None
of those is visible by reading. All of them are visible the first time the
answer differs from the processor's.

## The IR

P-code in shape. A byte-addressed register file, sized varnodes, and spaces:
`Const`, `Register`, `Ram`, `Unique`, `Stack`. No operation has an effect that
is not one of its outputs, which is the property that makes dataflow sound: a
flag written by an `add` is written by an explicit operation on the flag's
varnode, not by knowing that `add` touches flags.

## SSA, and the thing that makes it hard

Locations in SSA are **canonical whole registers**. A narrow read becomes a
`SubPiece` of the whole register; a narrow write becomes a masked merge with
it. Without that, `w0` and `x0` are two unrelated locations and every
dependency between them is invisible.

Two bugs from this area are worth recording because both were silent.

A phi took its inputs from what each predecessor block itself defined, so a
value that reached the predecessor from further back arrived as `Undefined`.
The fix is to record an exit state per block during renaming.

Dead code elimination deleted call arguments and call results, because an
argument register is the calling convention rather than an operand of the
instruction. Liveness is now seeded from the ABI's argument registers at every
call site and from what is live at return, and a `Call` defines its result
register plus an `Undefine` for every caller-saved one.

## The ABI model

`abi::of(arch)` gives the argument registers, the result registers, and the
caller- and callee-saved sets. It drives liveness, argument naming, result
detection and prototype recovery. It is one place rather than five.

## What it deliberately does not do

**It does not model what it has not implemented.** An unlifted instruction is
recorded as unlifted and the count is published. A lifter that quietly treated
an unknown instruction as a no-op would make every analysis above it confidently
wrong, which is the failure this project cares most about avoiding.

## Numbers

In `docs/scorecard.md`: the share of instructions lifted per architecture, and
the number of executions matched against hardware.
