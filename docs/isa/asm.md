# The structured text: `nocompiler disasm` and `nocompiler asm`

The structured form of [v1.md](v1.md), as text. A function is its block/loop
tree with the profile's instructions as leaves; what an LLM writes,
`nocompiler disasm` prints and a proof walks is the same thing. The text has
no addresses: `nocompiler asm` turns it into an ELF relocatable object, which
ld.lld links like any other.

```bash
nocompiler disasm prog.elf > prog.s       # the text (any binary nocompiler cc or asm made)
nocompiler asm prog.s -o prog.o           # back to an object, checked against the profile
ld.lld -static -e _start prog.o other.o -o prog.elf
```

The implementation is `crates/nocompiler/src/text.rs`; the tests are
`crates/nocompiler/tests/text.rs`.

## The format

```text
func sum                        ; a comment: `disasm` adds the address and level
  addi a2, zero, 0
  block $done
    beq a1, zero, $done         ; to the end of the enclosing block $done
    loop $next                  ; head 0x11198
      ld a3, 0(a0)
      add a2, a3, a2
      addi a1, a1, -1
      addi a0, a0, 8
      bne a1, zero, $next       ; to the head of the enclosing loop $next
    end
  end
  addi a0, a2, 0
  ret

func sum2
  frame 32                      ; the frame (rule R5) and its partition (R6)
    slot 0 save s2
    slot 8 save s1
    slot 16 save s0
    slot 24 save ra
  addi sp, sp, -32
  sd ra, 24(sp)
  ...
  call sum
  ...
  ret

func _start
  ...
  auipc s0, %pcrel_hi(.data)
  addi s0, s0, %pcrel_lo(.data)
  ...

data .data rw align 8
  01 00 00 00 00 00 00 00 02 00 00 00 00 00 00 00
bss .bss 4096 rw align 8
```

| statement | words | what |
| --- | --- | --- |
| an instruction of the profile ([profile.md](profile.md)), as `disasm` prints it | 1 | itself: llvm-objdump's `-M no-aliases` syntax, ABI register names |
| `block $l` ... `end`, `loop $l` ... `end` | 0 | a node of the tree; `$l` names it inside it |
| `beq a, b, $l` (any branch), `j $l` | 1 | to the end of the enclosing block `$l`, or the head of the enclosing loop `$l`; any other label is an error, so R3 holds by construction |
| `call f`, `tail f` | 2 | `auipc ra` / `jalr ra` (or `auipc t1` / `jalr zero`), `R_RISCV_CALL_PLT` to `f` |
| `ret` | 1 | `jalr zero, 0(ra)` |
| `auipc rd, %pcrel_hi(sym+k)` | 1 | `R_RISCV_PCREL_HI20`: the high part of the distance to `sym+k` |
| `addi rd, rs, %pcrel_lo(sym+k)`, `ld rd, %pcrel_lo(sym+k)(rs)`, `sd rs2, %pcrel_lo(sym+k)(rs)` | 1 | `R_RISCV_PCREL_LO12_I`/`_S`: the low part, paired with the latest `%pcrel_hi(sym+k)` before it |
| `frame N`, then `slot K save REG`, `slot K spill`, `mem K LEN` | 0 | the frame size and its partition (offsets from the bottom of the frame), first in a function |
| `data NAME r|rw [align N]` and hex bytes; `bss NAME SIZE r|rw [align N]` | | a data section: a symbol `%pcrel_hi` can name |

Every statement is a fixed number of words: there is no `li` (whose length
depends on the value), no absolute address and no `jal` call. A symbol that
the text does not define (a function in another object, a data section of
another object) becomes an undefined symbol of the object.

`disasm` names unlabelled nodes `$b<k>` and `$l<k>` (pre-order); labels a
writer gave are kept in `.nocompiler.struct`. A function below L1 is listed
as a comment with its violations: it has no tree to print.

## What `asm` checks and writes

Every function is checked with the profile checker (`profile::check_with`) at
a trial layout, with the partition the text declares: below L1 is an error
and nothing is written; at L2 the declared `frame` must be the code's. The
object has one `.text.NAME` section per function (so the linker can place and
order them), `.rela.text.NAME` with the relocations, the data sections, and a
`.nocompiler.struct` version 2 table (position-independent: ld.lld
concatenates the tables of its inputs, and `nocompiler check` reads them).

Neither `asm` nor `disasm` is trusted: a proof is about the bytes of the
linked binary, which the audit compares with the image the proof uses.

## The round trip (criterion 5)

`crates/nocompiler/tests/text.rs`, for every function at L1 or above of the
committed binaries and the C corpus: the object `asm` makes from the text
`disasm` prints holds the same relocatable function (words with relocated
fields zero, relocations) with the same tree, level, frame and partition; and
where every function of the program is at L1 or above, the object linked again
by ld.lld at the binary's section addresses and function order is the
binary's `.text` and data, byte for byte, and checks.
