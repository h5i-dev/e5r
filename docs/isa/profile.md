# The e5r profile

Status: version 0, 2026-11-20. The definitions this document describes are
`lean/E5R/Isa.lean` (instructions), `lean/E5R/Machine.lean` (semantics) and
`crates/e5r/src/profile.rs` (structural rules). Where this text and the code
disagree, the code is what is checked; report the disagreement.

## 1. What it is

The e5r profile is a subset of 64-bit RISC-V plus a set of rules about how
code is laid out, chosen so that a machine-code function can be proved
correct in Lean 4 with as little effort as possible, by a person or by a
model writing the proof.

Code in the profile is ordinary RISC-V. It runs unchanged on any RV64 Linux
machine or under `qemu-riscv64`; nothing is enforced at load time. The
profile only decides which binaries the proof library handles well. A proof
is a Lean theorem about the bytes of one binary, and it says what it says
whether or not anyone checked the rules first (see [spec.md](spec.md)).

The rules come from three places: NaCl's restrictions on x86 code, eBPF's
static checks, and WebAssembly's structured control flow. Unlike eBPF, a
binary that breaks a rule is not rejected by anything at run time: breaking
a rule only means the proof is harder to write, or that `e5r check` says so.

## 2. Instructions

Base: RV64I, user mode, little-endian, XLEN 64. Extensions: M, Zba, Zbb.

| Group | Instructions |
| --- | --- |
| Upper immediates | `lui`, `auipc` |
| Jumps | `jal`, `jalr` (forms restricted, section 4) |
| Branches | `beq bne blt bge bltu bgeu` |
| Loads | `lb lh lw ld lbu lhu lwu` |
| Stores | `sb sh sw sd` |
| Immediate ALU | `addi slti sltiu xori ori andi addiw slli srli srai slliw srliw sraiw` |
| Register ALU | `add sub sll slt sltu xor srl sra or and addw subw sllw srlw sraw` |
| M | `mul mulh mulhsu mulhu div divu rem remu mulw divw divuw remw remuw` |
| Zba | `sh1add sh2add sh3add add.uw sh1add.uw sh2add.uw sh3add.uw slli.uw` |
| Zbb | `andn orn xnor max maxu min minu rol ror rori rolw rorw roriw clz ctz cpop clzw ctzw cpopw sext.b sext.h zext.h rev8 orc.b` |
| Environment | `ecall` (meaning in [environment.md](environment.md)) |

Not in the profile: the C extension (every instruction is 32 bits and
4-byte aligned, so decoding is unambiguous), CSR instructions, `fence`,
`fence.i`, `ebreak`, privileged and hypervisor instructions, and the A, F,
D and V extensions. `decode` returns nothing for them, so a proof can never
step over one; a binary containing one in a function fails rule R1.

Why these: M and Zba/Zbb are what compilers use for address arithmetic,
bit manipulation and multiplication, and their semantics are total and
simple (RISC-V division by zero is defined, not a trap). A, F, D and V are
where the proof cost is: weak memory ordering, IEEE rounding, and
variable-length vector state. They are later versions of the profile
([ROADMAP](../ROADMAP.md)).

The decoder is checked against llvm-mc on every funct7/funct3 combination,
every 12-bit immediate of every immediate opcode, and 60,000 random words
(`crates/e5r/tests/decode.rs`); the Lean decoder is checked against the Rust
one (`crates/e5r/tests/semantics.rs`).

## 3. Semantics

`lean/E5R/Machine.lean` follows the RISC-V unprivileged specification for
these instructions. The profile narrows it in two places, both of which make
the model smaller than the hardware, never larger:

- **Alignment.** A load or store whose address is not a multiple of its width
  has no successor. Whether misaligned accesses trap or run slowly is up to
  the implementation; the profile excludes them, so a proof shows every
  access is naturally aligned.
- **Jump targets.** A jump or taken branch to an address that is not a
  multiple of 4 has no successor (instruction-address-misaligned: there is no
  C extension).

The semantics are compared with qemu-riscv64 on random programs covering
every instruction (`crates/e5r/tests/semantics.rs`).

## 4. Structural rules

A function is the code named by an `STT_FUNC` symbol with a nonzero size,
inside `.text`. A binary conforms when every function does. `e5r check`
decides it; each rule has an identifier in its output.

- **R1 decode.** Every word of the function decodes to a profile instruction.
- **R2 control.** Control leaves an instruction only to:
  - the next instruction;
  - a branch or `jal zero` target inside the function;
  - a call, `jal ra, f` or `auipc ra, hi; jalr ra, lo(ra)`, to the entry of a
    function, returning to the next instruction;
  - a tail call, `jal zero, f` or `auipc t1, hi; jalr zero, lo(t1)`, to the
    entry of another function;
  - a return, exactly `jalr zero, 0(ra)`.

  No other `jalr`: no computed jumps or calls in version 0. The last
  instruction of a function does not fall through.
- **R3 structure.** The function has a block/loop tree: properly nested
  intervals of its addresses, each a `block` or a `loop`. A branch or jump
  target is either the end of a block enclosing the source or the start of a
  loop enclosing the source. This is WebAssembly's `br`: no goto, a reducible
  control-flow graph, and the loop heads are exactly where invariants go. A
  jump from outside a loop into its middle has no such tree and fails R3.
- **R4 registers.** `gp` and `tp` are never written. `ra` is written only by
  a call (including the `auipc ra` half of one) or reloaded with
  `ld ra, k(sp)`.
- **R5 stack.** `sp` is written only by `addi sp, sp, k` with `k` a multiple
  of 16. Along every path the offset of `sp` from its value at entry is the
  same at each instruction, is a multiple of 16 at every call, and is 0 at
  every return and tail call. The largest depth is the function's frame.
- **M1 metadata.** If the binary has an `.e5r.struct` section, each
  function's tree, frame size and callees there are the ones the code has
  ([metadata.md](metadata.md)).

`e5r check` without `.e5r.struct` recovers the tree from the control-flow
graph and checks against that; with the section, it checks against what the
section says. The recovery is not trusted by the checker: it only proposes a
tree.

## 5. Calling convention

The standard RISC-V LP64 psABI: arguments in `a0` to `a7`, results in `a0`
and `a1`; `sp`, `s0` to `s11` callee-saved (and `gp`, `tp` never written);
`sp` 16-byte aligned at calls; no red zone. Every function specification
includes this as `Preserved` ([spec.md](spec.md)).

## 6. Building conforming code

```
clang --target=riscv64-unknown-elf -march=rv64im_zba_zbb -mabi=lp64 -mno-relax -O2 \
  -ffreestanding -nostdlib -fno-pic -c f.c
ld.lld -static -e _start f.o -o f.elf
e5r annotate f.elf -o f.e5r.elf     # check, then record .e5r.struct
```

What clang emits at `-O2` for ordinary C conforms as long as the code needs
no jump table (a dense `switch`; `-fno-jump-tables` avoids it) and no
function pointer; `e5r check` says which function fails which rule.
Recursion is allowed by the rules; bounding its stack use is then part of
the proof.
[toolchain.md](toolchain.md) has the details, and the plan for doing this
inside LLVM instead of after linking.
