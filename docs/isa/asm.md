# Structured assembly: `nocompiler asm`

`nocompiler disasm` prints a binary's functions nested by their block/loop
tree. `nocompiler asm` reads that listing back: the format is the listing.
Written by hand (or by a model) it is assembly with the structure explicit:
branches name an enclosing `block` or `loop` instead of an address, so rule
R3 holds by construction, and loop heads carry their invariants and measures
in Lean syntax, which pass through into a generated proof skeleton. The
encoder is deterministic and untrusted: what it writes is checked against the
profile before it is written, and a proof about it is checked by the Lean
kernel against its bytes.

```bash
nocompiler asm f.s -o f.elf                                  # assemble, check, write .nocompiler.struct
nocompiler asm f.s -o f.elf --skeleton F.lean --namespace My.Image   # and a proof skeleton
nocompiler export f.elf --namespace My.Image -o My/Image.lean
nocompiler disasm f.elf                                      # the listing: asm reads it back unchanged
```

The implementation is `crates/nocompiler/src/asm.rs`; the tests are
`crates/nocompiler/tests/asm.rs`.

## The format

Line-oriented. `;` starts a comment (outside annotations).

```text
name 0xADDR:                 a function at ADDR (as disasm prints it)
name:                        a function after the previous one (the first at 0x11000)
  ADDR: WORD  instr          an instruction, as disasm prints it: ADDR and WORD are checked
  instr                      an instruction, placed and encoded by the assembler
  block {   block @x {       open a block (optionally labelled)
  loop {    loop @x {        open a loop
  end block   end loop       close the innermost one, which must be of that kind

data NAME [0xADDR] r|rw:     an allocated data section (without ADDR: after the code, page-aligned)
  68 65 6c 6c 6f             bytes, in hex
  .ascii "hello\n"           or a string (escapes \n \t \0 \\ \")
  @msg:                      a label at the current offset, for `la`
bss NAME 0xADDR SIZE r|rw    a zero-filled section
```

**Instructions** are written as `disasm` prints them, which is
llvm-objdump's `-M no-aliases` syntax: `addi a0, a0, 8`, `ld a3, 0(a0)`,
`sd ra, 24(sp)`, `jalr zero, 0(ra)`, `lui a0, 16` (the 20-bit field, in
decimal), `slli a0, a0, 3`. Registers are ABI names (`zero ra sp gp tp t0-t6
s0-s11 a0-a7`, `fp` for `s0`) or `x0`-`x31`. Every instruction of the
profile is accepted ([profile.md](profile.md)), and nothing else: there is no
`.word`, since a word outside the profile is outside the profile.

**Targets** of branches and `jal`:
* `0xADDR`, an absolute address (what `disasm` prints);
* `@x`, the label of an enclosing `block` (the target is its end) or `loop`
  (its head). This is WebAssembly's `br`: a label that is not enclosing is an
  error, so a source that uses only labels has a valid block/loop tree;
* the name of a function (a call `jal ra, f` or a tail call `jal zero, f`).

**Pseudo-instructions**, for writing (`disasm` never prints them): `nop`,
`li rd, imm` (12-bit), `mv rd, rs`, `ret`, `j @x` (also `br @x`),
`beqz rs, @x`, `bnez rs, @x`, `call f`, `tail f`, and `la rd, @label`
(`auipc` + `addi` to a data label: two words).

**Annotations** are lines starting with `#`, kept verbatim as Lean text:

```text
#import Examples.MemsetSpec     a module the skeleton imports
#open Examples.Memset           a namespace it opens
#namespace Examples.Memset      the namespace its theorems go in
f:
  #spec spec                    the function's Spec (a Lean term): it gets a theorem
  #intro ⟨p, c, n⟩ s he ⟨h0, h1, h2, h3⟩   the rintro pattern of the theorem
  loop @l {
    #inv fun u => ∃ k, ...      the loop head's invariant (directly after `loop {`)
    #    ∧ ...                  `#` and a space: continues the annotation above
    #measure fun u => ...       its measure
```

The skeleton (`--skeleton OUT --namespace NS`, where NS is the namespace the
image is exported under) has, for every function with a `#spec`, the theorem
`<name>_verified : Verified code <name>_dom <name>_entry (spec)`, its
`rintro`, and one `nocompiler_auto <name>_func s he` call with a `loop_inv
ADDR (inv) measure (measure)` per loop, in tree order, the addresses
computed by the assembler. A loop without `#inv` gets `fun _ => True` and a
comment saying so. What is left after the call is the verification
conditions, as named goals; a proof is the skeleton followed by their proofs
(`examples/asm/build.sh` checks that `lean/Examples/Memset.lean` starts with
the skeleton it generates).

## What is checked

* **The encoder inverts the decoder**: `encode(decode(w)) = w` for every
  decodable word among 2,000,000 random ones (with each major opcode forced
  in half of them), and assembling `decode(w).asm(pc)` at `pc` gives `w`
  for 1,000,000 more.
* **disasm then asm is the identity** on every committed profile binary
  (`examples/elf/{sum,hello}.elf`, `demo/elf/{sum,cobs}.b.elf`): the same
  `.text` at the same address, the same function symbols, the same data
  sections, the same block/loop trees, frames and callees, and the listing of
  the output is the input. (The rest of the ELF is the assembler's own: one
  `PT_LOAD` per allocated section, `.nocompiler.struct`, `.symtab`,
  `.strtab`, no `.comment` or attributes.)
* **The output runs**: `hello` assembled from its listing prints what the
  original prints under qemu-riscv64; `examples/asm/memset.s` is tested
  under qemu (`examples/asm/test.py`).
* **The output conforms**: each function is checked with `profile::check`
  against the tree as written (R1 to R5); a violation is an error and nothing
  is written. The written file is read back and checked again, as
  `nocompiler check` would.
* **Malformed sources are refused**, with a line number: a label that is not
  enclosing, `end` of the wrong kind, an unclosed or empty block, an address
  or word in a listing line that is not what the assembler computes, an
  immediate out of range.

## The example

[examples/asm/README.md](../../examples/asm/README.md): `memset` written in
the format, assembled, run under qemu, and proved; the same function through
clang, proved against the same specification, and the two compared.
