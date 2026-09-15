# Decoding

`crates/e5r-arch`

## What it is for

Bytes at an address become an `Insn`: a mnemonic, typed operands, a length,
and a `Flow` saying how control leaves it. Everything above depends on `Flow`
being right, because that is what builds the control flow graph.

## The decision that shaped it

**The gate is another disassembler, over every instruction in the corpus.**
Not a table of expected outputs written by the same person who wrote the
decoder, which only tests that the author was consistent with themselves.

`objdump -d` for AArch64, `llvm-objdump` for x86-64 and for ARM32 and Thumb-2.
Every instruction in every fixture, plus libc, libstdc++, libcrypto, bash, ls,
objdump and a static Go binary, is decoded and compared as text. A
disagreement is either a bug here or a deliberate divergence with a written
reason; there is no third category. There is exactly one divergence, and it is
that `objdump` resolves an `R_AARCH64_CALL26` relocation in a `.o` while the
decoder reports the encoded offset, which is the loader's job and not the
decoder's.

This is expensive to set up and it is the reason the decoders are trustworthy.
The corpus finds what a hand-written test never would. Adding one Go binary
found five real bugs in a decoder that had been passing over 1.4 million
instructions of C and C++ output, including a system register table with eight
wrong entries that nothing had ever read.

**For breadth, sweep encodings rather than waiting for a compiler to emit
them.** A compiler emits a narrow slice of an instruction set. Generating
random and strided encodings and pushing them through the oracle covers the
rest: about 260,000 of them found and fixed roughly 15,000 disagreements in
the ARM32 decoder before its fixture gate was first run.

## Text is part of the contract

Two spellings, both deliberate. `Style::objdump` matches the oracle exactly,
because that is what the comparison needs. The default spelling is for a human
reading a terminal. Where they differ the difference is in this crate, not
smeared through the callers.

## What it deliberately does not do

An unallocated encoding decodes to `None`. It is not an error: it is data, or
a newer extension, and the caller decides which. Printing a guess would be the
worst available answer.

A decoder declines rather than printing something it cannot represent. ARM32's
register-offset memory with a subtracted index or a non-`lsl` scale is not
decoded, because the shared `Mem` type cannot express either and printing the
nearest thing would be wrong.

## Numbers

In `docs/scorecard.md`, per architecture: instructions compared, wrong (zero),
and the share decoded, with the floor that only rises.
