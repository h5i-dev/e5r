# The `.sla` format

A `.sla` file is the compiled form of a SLEIGH language definition: what
Ghidra's SLEIGH compiler writes when it is given a `.slaspec`. Loading one is
what M2 needs, and nothing about the file layout is published, so this document
is what was worked out about it and how.

Everything here was established by observation. The method is the one this
toolkit uses on any binary format: get the producer, feed it inputs that differ
in one thing, and see which bytes move. Ghidra ships its SLEIGH compiler as
`support/sleigh`, which turns a `.slaspec` into a `.sla` in a couple of seconds,
so that loop is available and every claim below that says **proved** is backed
by a specific edit and a specific diff. Claims that say **inferred** are reads
that fit every file in the corpus but that no experiment isolated.

The SLEIGH *language* documentation was read; it is public. The SLEIGH
implementation was not, and the element and attribute names in this document
are ours, invented to describe what the numbers do.

## The corpus

| what | how many |
| --- | --- |
| `.sla` shipped with Ghidra 12.1.3 | 137 files, 417 bytes to 501 KB, 95 MB decompressed |
| `.sla` compiled here from `.slaspec` written for the experiments | 70-odd, rebuilt per experiment |
| `.slaspec` in the source and binary trees together | 152 |

The Ghidra source tree at `Ghidra/Processors/*/data/languages/` holds 152
`.slaspec` files and no `.sla`: the files are built at package time, not checked
in. A binary distribution has the built ones.

Three of the compiled experiments are committed as
`crates/r12e-sla/tests/data/*.sla`, with the `.sinc` sources that produced them,
so the work is reproducible without a Ghidra install.

## The container

```
offset  size  content
0       3     "sla"
3       1     format version, 4 in every file seen
4       ..    a zlib stream (RFC 1950), CMF/FLG = 78 9c in every file seen
```

**Proved.** All 137 shipped files begin with the same six bytes `73 6c 61 04 78
9c`. The payload inflates with a stock zlib and its Adler-32 checks, so it is an
ordinary zlib stream with no framing of its own. Truncating the file at any
length makes the inflate fail rather than produce a short payload, which is what
a real zlib stream does.

The version byte is at offset 3 rather than part of the magic because it is the
only byte that differs between `sla` and a hypothetical future `sla`: it was not
varied experimentally, since one Ghidra release writes one version. A reader
should refuse a version it has not been tested against rather than guess.

### Is the compression a problem for a no-dependency build?

No, and this was the one thing that could have sunk the work. The stream is
plain DEFLATE in a zlib wrapper, both of which are published as RFC 1951 and RFC
1950. `crates/r12e-sla/src/inflate.rs` is about 330 lines including the tests
and decompresses all 137 files with their checksums matching. No dependency is
needed and none was added.

## The payload: a tagged element tree

The decompressed payload is not text and not XML. It is a byte stream of tags
describing one tree of elements, each with numbered attributes. The smallest
file, `data-le-64.sla`, is 499 bytes decompressed and begins:

```
0000  60 a1 e0 a2 21 84 e0 a3 10 e0 a4 21 81 e0 a5 40 |`...!......!...@|
0010  60 a3 60 a4 cc 71 89 64 61 74 61 2e 73 69 6e 63 |`.`..q.data.sinc|
```

### Tag bytes

The top three bits of a tag byte pick the kind:

| bits 7-5 | kind | id |
| --- | --- | --- |
| `010` | element start | low 5 bits, 0..31 |
| `011` | element start | in following chunks |
| `100` | element end | low 5 bits, 0..31 |
| `101` | element end | in following chunks |
| `110` | attribute | low 5 bits, 0..31 |
| `111` | attribute | in following chunks |

In the extended forms the low **four** bits hold one less than the number of
following bytes, and each of those bytes contributes seven bits, most
significant first, with the top bit set. So `60 a1` is an element start with
id `0x21`, and `a0 a1` closes it.

**Proved.** The decisive evidence is that this reading parses all 137 files
exactly: every element end matches the element that is open, the payload holds
exactly one root element, and the walk consumes the last byte of every file with
nothing left over. Getting the length of any field wrong desynchronises the rest
of the file, so 95 MB of exact consumption across 137 independently compiled
files is not a coincidence. The element ids that come out are 1..84 and the
attribute ids 2..55, both dense, which is what a compiler-assigned enumeration
looks like and not what a misparse produces.

The `+1` on the extended count was forced: `0x60` has a low nibble of zero and
is always followed by exactly one id byte.

### Values

An attribute tag is followed by exactly one value, and nothing else in the
stream is. That is why the value type codes may reuse byte ranges that mean
something else in element position: the reader always knows which it is
expecting. It is also what makes an unknown element or attribute skippable
rather than fatal, which the reader relies on.

A value byte is a type in the top four bits and a count in the low four:

| type | meaning | payload |
| --- | --- | --- |
| 1 | boolean | none; the low nibble is the value, 0 or 1 |
| 2 | signed integer, not negative | `count` seven-bit chunks |
| 3 | signed integer, negative | `count` chunks holding the magnitude |
| 4 | unsigned integer | `count` chunks |
| 5 | address space | `count` chunks holding the space index |
| 7 | string | `count` chunks holding the byte length, then that many bytes |

Types 0 and 6 appear in no file in the corpus.

**Proved:** 1, 2, 4, 5 and 7. The boolean reading is forced by
`e0 ac 10 a0 ad` versus `e0 ac 11 a0 ae`, where the byte after the attribute is
the only difference and consuming a payload for it would desynchronise the next
tag. Strings are self-evident from `71 89` followed by exactly nine bytes of
`data.sinc`, and the count nibble is confirmed across name lengths 1 to 82. Type
5 is the space reference: in `data-le-64.sla` the varnode symbol for `r0`
carries `a4 = type5:4`, and 4 is the index of the `register` space in the same
file's space table. Type 4 carries `0x80000000` in a pattern mask, which needs
all 32 bits, where type 2 never carries a value with its top bit set at the same
width.

**Inferred:** that type 3 is the negative of type 2 rather than a fourth
unrelated integer kind. The evidence is that type 3 appears only where a "none"
sentinel belongs: every operand symbol carries attribute 19 as type 3 with
magnitude 1, and -1 is the obvious sentinel. No experiment isolated a field that
takes both a positive and a negative value.

Integers can need ten chunks (70 bits) to carry a 64-bit value, so a reader must
accumulate wider than 64 bits or check for overflow. The corpus maximum is ten.

## The element tree

Written with the names this project uses. Element id in brackets.

```
sleigh [33]  version, bigendian, align, uniqbase
  sourcefiles [35]
    sourcefile [36]  name, index
  spaces [34]  defaultspace
    space_other [45] | space_unique [46] | space [37]
        name, index, bigendian, delay, size, wordsize, physical
  symbol_table [38]  scopesize, symbolsize
    scope [22]  id, parent                        (scopesize of them)
    <header> ...                                  (name, id, scope)
    <body>   ...                                  (everything else)
```

The symbol table is two runs: first every scope, then a header record per
symbol carrying only its name, id and scope, then a body record per symbol
carrying the rest. Header and body are two different element ids, and in every
one of the twelve pairs the body's id is exactly one less than the header's.

| body | header | symbol kind |
| --- | --- | --- |
| 13 | 14 | operand of a constructor |
| 23 | 24 | varnode: a register or other fixed location |
| 25 | 26 | user-defined p-code op (`define pcodeop`) |
| 39 | 40 | value: a token field used as a number |
| 41 | 42 | context field |
| 43 | 44 | `inst_next` |
| 64 | 65 | `attach names` |
| 67 | 68 | `inst_next2` |
| 69 | 70 | `inst_start` |
| 71 | 72 | subtable |
| 73 | 74 | `attach values` |
| 76 | 77 | `attach variables` |

**Proved** for operand, varnode, value, context, `inst_next`, `inst_start`,
`inst_next2`, subtable and `attach variables`: a spec was compiled that defines
each, and the name string in the header identifies which element is which.
**Inferred** for `define pcodeop` (body 25 carries only an index, and the count
tracks the number of `pcodeop` declarations), `attach names` (body 64's children
are strings) and `attach values` (body 73's children are integers).

Two details a reader has to allow for. A value, name, valuemap or
`attach variables` body reads its bits from a token field (element 27) *or*
from a context field (element 29): 131 of the 7,339 `attach variables` bodies
in the corpus are over context. And a `name` entry (element 66) can carry no
name attribute at all, which is a hole in the attachment rather than an empty
string; 100 of 6,764 do.

### The root and the spaces

| attribute | meaning | evidence |
| --- | --- | --- |
| 34 `version` | 4 in every file | not varied |
| 35 `bigendian` | `define endian` | **proved**: flipping `little` to `big` flips it on the root and on every space |
| 36 `align` | `define alignment` | **proved**: 1 to 4 changed it from 1 to 4 |
| 37 `uniqbase` | base of the unique space | **inferred**: it grows with the number of temporaries a spec uses |

Spaces carry `name`, `index`, `bigendian`, `delay`, `size`, `wordsize` and
`physical`. Index 0 never appears in the table and is presumably the constant
space; the first declared index is 1 (`OTHER`), then 2 (`unique`), then the
spaces the spec declares. **Proved:** the space `size` follows `define space ...
size=`, and the index a varnode symbol refers to is the index in this table.

### Registers

A varnode symbol body (23) carries `space` (type 5), `off` and `size`.

**Proved.** `define register offset=0x0 size=8 [ sp r0 ]` gives `sp` at offset 0
and `r0` at offset 8; changing the declaration to `offset=0x40 size=4` moved
them to 64 and 68 with size 4; adding `r1` inserted a symbol, shifted every
later symbol id by one, and raised `symbolsize` from 8 to 9.

### Token fields

A token field element (27) sits inside a value, valuemap, name or varnodelist
symbol body:

| attribute | meaning |
| --- | --- |
| 35 `bigendian` | the token's endianness |
| 31 `signbit` | the field is signed |
| 14 `startbit`, 30 `endbit` | the bit range inside the token |
| 33 `startbyte`, 32 `endbyte` | the bytes of the stream the field touches |
| 29 `shift` | right shift to bring the field to bit 0 |

**Proved.** For a little-endian 16-bit token, `op = (8,15)` gives
startbit 8, endbit 15, startbyte 1, endbyte 1, shift 0; `rs = (4,7)` gives
0/…/4 with shift 4; `rd = (0,3)` gives shift 0; and adding `signed` to `imm =
(0,7)` is the only change that sets attribute 31. Context fields (29) have the
same layout without the endianness.

### Constructors

A constructor element (20) holds, in order: one `constructor_operand` (15) per
operand naming its symbol id, then the display form as an alternating run of
`print_literal` (8) and `print_operand` (17), then any context records
(32 and 79), then one `construct_tpl` (21) per p-code section. A literal piece
is one run of whitespace or one run of anything else, never a mixture, so
`" sp,"` is two pieces.

| attribute | meaning | evidence |
| --- | --- | --- |
| 22 `parent` | symbol id of the subtable it belongs to | **proved**: constructors of a `Mode:` subtable carry that subtable's id, `instruction`'s carry 0 |
| 25 `source` | index into the `sourcefiles` list | **proved**: moving two constructors into an `@include`d file gave them index 1 while the one left behind kept 0 |
| 24 `line` | line number in that file | **proved**: four constructors on lines 17-20 carry 17, 18, 19, 20 |
| 26 `length` | instruction length in bytes | **proved**: the one constructor spanning two 16-bit tokens carries 4 where the others carry 2 |
| 27 | where the mnemonic ends among the print pieces | **inferred**: it is the index of the first whitespace-only piece wherever there is one, over every constructor in the corpus that has one, and otherwise the number of pieces, which holds for all but a few hundred. 0 and -1 both occur and neither was isolated |

### Patterns

```
decision [16]     number, context, startbit, size
  decision [16]   ... recursively
  decision_pair [9]  id = constructor index
    instruction_pattern [18] | context_pattern [10] | combine_pattern [19]
      pattern_block [7]  off, nbytes
        pattern_word [6]  mask, val
```

A `pattern_block` is a run of `nbytes` bytes starting `off` bytes into the
instruction, and each `pattern_word` is a 32-bit mask and value read
**big-endian from the instruction stream**, most significant bit first, so
bit 0 of the first word is the top bit of the byte at `off`.

`decision.startbit` counts bits the same way: absolute over the stream,
most-significant-bit-first within each byte.

**Proved.** With a little-endian 16-bit token and `op = (8,15)` at stream byte
1, four constructors with `op` 0..3 produce a decision with `startbit` 14 and
`size` 2, which is exactly where `op`'s low two bits land under that numbering.
The `:add is op=0x01` pattern is `off=1 nbytes=1 mask=0xff000000
val=0x01000000`, so the word is anchored at `off` rather than at byte 0.
`:nop is op=0 & rd=0 & rs=0` constrains both bytes and gives `off=0 nbytes=2
mask=0xffff0000 val=0`. A constructor taking a subtable that fixes the top three
bits of `rs` gives `mask=0xe0ff0000`, which is the union of one partial byte and
one whole one at the right positions.

### P-code templates

```
construct_tpl [21]   delay, section, labels
  null [11] | handle_tpl [30]      what it exports; always present, always first
  op_tpl [5]  code = p-code opcode
    null [11] | varnode_tpl [2]    the output
    varnode_tpl [2] ...            the inputs
```

A `varnode_tpl` always has exactly three children, one each for the space, the
offset and the size. A `handle_tpl` always has seven. Each child is one of:

| element | meaning |
| --- | --- |
| 1 `const_real` | a literal, in attribute 2 |
| 3 `const_spaceid` | a space, in attribute 4 (value type 5) |
| 4 `const_handle` | field `select` of operand `val`'s handle: 0 space, 1 offset, 2 size |
| 31 `const_relative` | a label, by index |
| 80 `const_inst_start` | the address of this instruction |
| 81 `const_inst_next` | the address after it |
| 82 `const_inst_next2` | the address after that |
| 83 `const_curspace` | in a space slot, the space this instruction came from |
| 84 `const_curspace_size` | in a size slot, the width of an address in it |

**Proved.** `:add rd, rs { rd = rd + rs; }` compiles to one `op_tpl` with code
19, an output that is operand 0's handle in all three fields, and two inputs
that are operands 0 and 1. `{ rd = sext(imm:1); }` gives code 18. A
`goto [t]` gives code 6. `myop(rd)` after `define pcodeop myop` gives code 9,
and a `{ ... goto <skip> ... <skip> }` gives code 5 with a `const_relative`
target. Those are `INT_ADD`, `INT_SEXT`, `BRANCHIND`, `CALLOTHER` and `CBRANCH`
at their published p-code opcode numbers, so the `code` attribute is the
standard opcode enumeration and not a private one. Element 81 was identified as
`inst_next` because it is what `goto inst_next + imm` puts in the addend, and
80, 82, 83 and 84 are settled under "Template leaves" below.

Codes 60 and 65 appear around a local label and are not in the published
arithmetic set; they are presumably template-only pseudo-operations. They are
reported by number and not named.

## Pattern expressions

A disassembly action, the `[ ... ]` block of a constructor, computes a value at
decode time. The compiled form writes that computation as a tree of elements
47 to 61, and the whole run is now identified. Each one was settled the same
way: one spec, one operator, one diff against a base that differs in exactly
that line.

| id | operator | spec line that produces it |
| --- | --- | --- |
| 47 | bitwise and | `[ val = imm $and 4; ]` |
| 48 | divide | `[ val = imm / 4; ]` |
| 49 | left shift | `[ val = imm << 4; ]` |
| 50 | unary minus | `[ val = -imm; ]` |
| 51 | multiply | `[ val = imm * 4; ]` |
| 52 | bitwise not | `[ val = ~imm; ]` |
| 53 | bitwise or | `[ val = imm $or 4; ]` |
| 54 | add | `[ val = imm + 4; ]` |
| 55 | right shift | `[ val = imm >> 4; ]` |
| 56 | subtract | `[ val = imm - 4; ]` |
| 57 | bitwise xor | `[ val = imm $xor 4; ]` |
| 58 | a literal, in attribute 2 | `[ val = 7; ]` |
| 59 | `inst_next` | `[ val = inst_next + imm; ]` |
| 60 | `inst_next2` | `[ val = inst_next2 + imm; ]` |
| 61 | `inst_start` | `[ val = inst_start + imm; ]` |

**All proved.** The run is alphabetical by the operator's name, which is what
the earlier guess said, but each entry now rests on its own experiment rather
than on the pattern. Three facts that came with them, all proved the same way:

* **Nothing is folded, and the operands are in source order.** `4 - imm` gives
  `56(58:4, operand)`, the mirror of `imm - 4`. So 56 is a real subtract and not
  an add of a negative.
* **A negative literal is unary minus applied to a positive one.** `imm + -4`
  gives `54(operand, 50(58:4))`, which is a second, independent proof of 50.
* **`$and` and `&`, `$or` and `|`, `$xor` and `^` compile identically** inside
  a disassembly action.

Two leaves are not in that run. A context field appears inline as element 29,
the same element a context symbol's body carries. An operand of the constructor
appears as element 12, with `index`, `table` and `ct` naming which operand of
which constructor of which table it is; that is also always the first child of
an operand symbol's own body. A named register is **not** a usable leaf: the
compiler accepts `[ val = r3 + imm; ]` without a warning and emits `58:0`. A
global token field is rejected outright.

**Correction to an earlier reading.** These elements occur only inside
disassembly actions. A pattern *constraint* with an expression on the right,
`imm=(op $and 3)`, is folded into mask and value bits at compile time and
produces no element in this range at all.

Element 60 and element 82 appear in none of the 137 shipped files, because no
shipped specification uses `inst_next2` in a disassembly action or a semantic
body. They were found by writing one that does.

## Context changes and `globalset`

A constructor carries two kinds of context record, after its print pieces and
before its p-code.

**Element 32, a context assignment**, is what `[ field = expr; ]` writes. It
carries `word` (attribute 52), the 32-bit word of the context register the
field lives in; `shift` (29), the right shift to the field's position; `mask`
(8), the bits the field owns; and exactly one child, the pattern expression for
the value. 13,609 of them in the corpus, always with that shape.

**Element 79, a `globalset`**, is what `globalset(address, field);` writes, and
it was the single largest uninterpreted region at 24 KB. It carries no children
and four attributes:

| attribute | meaning | evidence |
| --- | --- | --- |
| 3 | symbol id of the address argument | **proved**: `inst_start` gives 1, `inst_next` 2, `inst_next2` 3, an operand gives that operand's symbol id |
| 20 | which 32-bit word of the context register | **proved**: a field at bits (32,63) of an 8-byte context register gives 1, every field in the first word gives 0 |
| 8 | mask of the field being published | **proved**: `test=(0,0)` gives `0x80000000`, `cfld=(1,4)` gives `0x78000000`, matching the sibling element 32 exactly |
| 50 | flow | **proved**: declaring the field `noflow` is the only edit that clears it, and the four `globalset`s in ARM are all of `LRset`, which is `noflow` |

## Template leaves

The three unidentified leaves of a p-code template are settled, and a fourth
was found that no shipped file contains.

| id | meaning | spec line |
| --- | --- | --- |
| 80 | the address of this instruction | `{ rd = inst_start; }` |
| 81 | the address after it | `{ rd = inst_next; }` |
| 82 | the address after that | `{ rd = inst_next2; }` |
| 83 | in a space slot, the space this instruction was decoded from | `{ goto inst_next; }` |
| 84 | in a size slot, the width of an address in that space | the same |

**All proved.** 83 and 84 always occur as a pair, around a code address:
`goto`, `call` and the target of a conditional branch all produce
`varnode_tpl(83, <offset>, 84)`, including `goto 0x1234`, where the offset is a
plain literal and the two markers still appear. Narrowing the default space
from eight bytes to four leaves the fragment byte-identical, so 84 is a
symbolic width and not the number. A data reference is the contrast:
`*[ram]:8 rd = rs` writes a literal space id and a literal size. That the two
elements occur exactly 2,067 times each across the corpus is the same fact
counted a different way.

## Operand numbering

An operand has two numbers and they are not the same number.

The **symbol ids** of a constructor's operands are handed out in *display*
order, the order the operands appear in the constructor's display section.
Every **index** in the file is a position in the constructor's `operands` list
(element 15), and that list is in *resolution* order: the order a decoder has
to work them out in, which differs wherever a disassembly action computes one
operand from another.

**Proved.** In `skel.slaspec`, `ixMem8: (IX-val) is IX & simm8 & sign8=1
[ val = -simm8; ]` has three operands. The headers are `IX` = 63, `val` = 64,
`simm8` = 65, which is display order with the pattern-only `simm8` last. The
constructor's operand list is `15:63, 15:65, 15:64`, which is resolution order,
because `val` cannot be computed until `simm8` is read. The bodies agree:
symbol 64, named `val`, carries index 2, and symbol 65, named `simm8`, carries
index 1. The print pieces use the same numbering: the display prints `IX` then
`val` and the pieces are `17:0` and `17:2`.

Attribute 18 of an operand body is **how many instruction bytes the operand's
own bits occupy**: the width of the token a field is cut from, the shortest
match of a subtable, and **zero** for a fixed register, a context field, or a
value the disassembly action computes. **Proved** by the same constructor,
where `IX` is a register and carries 0, `val` is computed and carries 0, and
`simm8` is an eight-bit field and carries 1.

## The seven slots of a `handle_tpl`

A handle is what a constructor exports, and it has seven `ConstTemplate`
slots:

| slot | meaning |
| --- | --- |
| 0 | space |
| 1 | size |
| 2 | pointer space, a literal 0 when the handle is static |
| 3 | offset, or pointer offset when it is dynamic |
| 4 | pointer size |
| 5 | space of the temporary holding the pointer |
| 6 | offset of that temporary |

**Proved** for 0, 1 and 3: `export 0:1` and `export 1:1` produce handles that
differ in slot 3 alone, and both carry the constant space in slot 0 and a size
of 1 in slot 1. **Inferred** for the rest, from the shape of a dynamic export:
`ixMem8: (IX+simm8) ... { ptr:2 = IX + simm8; export *:1 ptr; }` gives
`ram, 1, unique, 0x2900, 2, unique, 0x2a00`, which is a one-byte value in the
`ram` space reached through a two-byte pointer in a unique temporary, with the
last two slots naming that temporary. A static export leaves slots 2, 4, 5 and
6 as literal zeroes.

Unique offsets in that example are 0x2900 and 0x2a00, and every unique offset
seen is a multiple of 0x100, with `uniqbase` one step past the last one used.
What decides how many steps a constructor takes is not established.

## What is still not established

The element tree is fully named. What is left is a handful of attributes, and
three facts a *writer* needs that a reader does not.

| what | where | what is missing |
| --- | --- | --- |
| attribute 19 | operand symbol body | the operand an offset is measured from, with -1 for the start of the instruction. Consistent with the front end's own model, not isolated |
| attribute 27 | constructor | where the mnemonic ends among the print pieces. It is the index of the first whitespace piece wherever there is one; where there is none it is usually the number of pieces, and 0 and -1 both occur |
| attribute 7 | operand symbol body | a boolean on 2,992 of 336,390 operands. **Inferred**: in `skel.slaspec` it is set on exactly the six operands whose subtable is a jump destination, `Addr16` or `RelAddr8`, so it looks like "this operand is a code address". It cannot be derived from the pattern alone, only from what the semantic body does with the operand |
| attribute 28 | `const_handle` | present on 67,414 of 1,071,955 |
| attributes 38, 39, 40 | the root element | 38 on thirteen files, 39 and 40 on one |
| the unique space allocation | p-code templates | offsets are multiples of 0x100 and `uniqbase` is one past the last, but what decides how many a constructor takes is not known |
| opcodes 60 and 65 | p-code templates | template-only operations. 60 appears once per subtable operand with the operand index as its input, and 65 at a local label, which is what `BUILD` and `LABEL` would look like, but neither was isolated |

The reader carries every one of these through unchanged, and the writer puts
them back where they were, which is why the rebuild below is byte exact
without their meaning being known.

One thing is established and worth stating as an absence: **the compiled form
does not record how a field prints**. `imm = (0,7) signed hex` and
`imm = (0,7) signed dec` compile to trees that are identical but for the source
file name, so `dec` reaches the `.sla` nowhere and anything decoding from one
has to print in hex. Nine of the 152 specifications use `dec` at all, and none
of AArch64, x86-64 or RISC-V does.

## Measured coverage

From `cargo test --release -p r12e-sla`, over the 137 shipped files plus the
committed fixtures. "Interpreted" counts the bytes of every element whose
meaning is established, where an element's bytes are its own tags, ids and
attribute values, excluding its children; summing that over the tree gives the
payload length exactly, so the figure cannot flatter itself.

| measure | before the nine experiments | now |
| --- | --- | --- |
| files read | 140 | 140 |
| decompressed payload | 95,576,250 bytes | 95,576,250 bytes |
| interpreted | 95,483,898 bytes, 99.90% | 95,576,250 bytes, 100.00% |
| kept as raw nodes | 92,352 bytes | 0 bytes |
| least covered file | `PIC/pic16.sla`, 99.36% | every file, 100.00% |

The 92 KB that was uninterpreted was the pattern expression operators, the
`globalset` record and the template leaves, and it is the same 92 KB the
experiments above account for.

Coverage is not the same as usefulness, and it is not the strongest check
available. The test also asserts self-consistency on every file: every symbol
id referenced by a context field, an attached varnode list, an operand or a
constructor resolves to a symbol that exists; every space index resolves; every
symbol has a header record; the symbol and scope counts the file declares match
what was found; and every node's byte range lies inside the payload. All 140
files pass with zero inconsistencies.

## Writing one

Reading a format and writing it are different claims, and the second is the
stronger one: a reader that is careless about which of two encodings a field
used still produces the right model, while a writer that is careless the same
way produces a file nothing else will read. `crates/r12e-sla/src/encode.rs`
writes the tag stream, `src/emit.rs` decides what tree to write, and
`src/deflate.rs` compresses it. The gates are in `tests/writer.rs`:

| gate | result |
| --- | --- |
| decode every shipped `.sla`, encode the tree straight back | 140/140 payloads byte for byte, 95,576,250 bytes |
| read every shipped `.sla` into the structured model, rebuild the tree from the model, encode | 140/140 files byte for byte |
| our own inflater reads what our deflater writes | every file, both block strategies |
| python's zlib reads what our deflater writes | every stream offered |

The second row is the one that matters, because the tree it encodes was
rebuilt out of spaces, symbols, constructors, patterns and templates rather
than copied. It is the claim that the model holds everything the file did.

Four things a writer has to get right that a reader never notices:

* **The value type is part of the field.** A varnode's offset is written as an
  unsigned integer (type 4) and its size as a signed one (type 2), in the same
  element. Attribute 19 of an operand is negative (type 3) when it is the -1
  sentinel and non-negative (type 2) otherwise. Attribute 7 of an operand is a
  boolean, not a small integer. There is no rule that derives these; they were
  read off the corpus one `(element, attribute)` pair at a time.
* **Attribute order is fixed per element.** A constructor writes parent, 27,
  length, source, line, in that order, and 130,696 constructors across the
  corpus have exactly that order. An operand writes id, then `subsym` if it has
  one, then off, 19, 18, then 7 if it has one, then index.
* **An absent element is not an empty one.** A decision pair holds either a
  `context_pattern`, an `instruction_pattern`, or a `combine_pattern` wrapping
  both; a pattern with no context half and a pattern whose context half holds
  no blocks are different files.
* **A `construct_tpl` always writes its export slot**, and always first: a
  `handle_tpl` when the constructor exports something, an explicit `null` when
  it does not, including when there is no p-code at all. All 128,421 in the
  corpus have it.

Small choices the format leaves open, both read off the shipped files and both
enforced by the byte gate: an id below 32 uses the short tag form and anything
else the extended form with the fewest chunks that hold it; an integer uses the
fewest chunks that hold its magnitude, so a zero is a type byte and nothing
else. A space with a word size of one omits attribute 43 entirely.

### The compressor

`src/deflate.rs` is the other half of `inflate.rs` and is there for the same
reason: no dependency. It runs LZ77 with a hash chain and codes the result with
the fixed Huffman tables of RFC 1951 section 3.2.6. It does not build dynamic
tables, which costs size: rewriting all 140 files gives 14,065,307 bytes where
the reference compiler's zlib gives 12,233,121, a factor of 1.15. Stored blocks
are available as a control and are what the test uses to tell a compressor bug
from an encoder bug.

Nothing here reproduces zlib's own bit stream and nothing tries to. A `.sla` is
compared after decompression, because the compressed form is not part of the
format's meaning.

### Compiling a `.slaspec`

`crates/r12e-sla/tests/sleighc/` turns an `r12e-sleigh` specification into the
model above and writes it. It lives in the test harness rather than the library
because `r12e-sleigh` will depend on `r12e-sla` for its decode engine and cargo
refuses a cycle between two normal dependencies; moving it is a file move.

Over all 152 `.slaspec` files in the source and binary trees: 152 parse, 152
compile, 152 read back with zero inconsistencies and a model that agrees with
what the front end parsed. 131,727 constructors, with 13,633 context
assignments, 5,225 computed operands and 1,323 `globalset`s.

What it does not write is p-code: a `construct_tpl` needs the unique space
allocation rule and the template-only opcode numbers, neither of which is
established, and the section above says so rather than guessing them.

#### Four things the reference compiler does that the source does not say

Each was found by compiling the same specification both ways and diffing, and
each moved our output closer to the reference's.

* **An unreferenced table is dropped.** `ADDR8` in `6502.slaspec` is defined
  and named by no operand. The reference warns "Unreferenced table" and its
  `.sla` holds neither the table nor its constructor, and every symbol id after
  it shifts down by two. 402 tables across the corpus are in that position.
* **An `attach` over a context field replaces the context symbol.** After
  `attach variables [ cc ] [ ... ]` the reference refuses `cc` as a context
  block lvalue and in a `globalset` call, both times calling it a
  `varnodelist_symbol`. So the symbol written is the family symbol, with the
  context field (element 29) inline where a token field would otherwise be.
  That is why 131 of the corpus's 7,339 `attach variables` bodies read their
  bits from context.
* **A constraint between two fields is enumerated.** `Rn=Rm` is not a bit test
  and the format has nowhere to put it, so the reference writes one alternative
  per value the two fields share: `:same is op=0x30 & rd=rs` with two four-bit
  fields gives a decision whose `number` is 17, sixteen for that constructor
  and one for its sibling.
* **A computed operand carries its computation.** `[ val = -imm; ]` writes
  `12(...)` and then `50(12(...))` under the symbol named `val`, in `val`'s own
  body rather than on the constructor. A context assignment is the other way
  round: it is element 32 on the constructor.

#### Where it still differs, and why

* **The decision tree.** It writes one flat node per subtable, whose pairs are
  tried in order, where the reference splits on a run of bits it picks per
  subtable. Both are correct decision trees; only one of them is the
  reference's bytes.
* **`length` under an ellipsis.** For `:ADC OP1 is (cc=1 & aaa=3) ... & OP1`
  the reference writes 1 and we write 2. `;` concatenation agrees: a
  constructor whose own token is one byte followed by a one-byte subtable
  carries 2 in both. So the reference's `length` counts the constructor's own
  bits plus what a `;` places after them, and `... &` composes by taking the
  wider of the two rather than the sum. The front end's `PatternAlt::length`
  sums, and that is where the difference comes from.
* **`define pcodeop` ids**, numbered together rather than at the point of
  declaration, because the front end does not record where one was declared.

#### The byte comparison

152 languages compiled both ways and diffed after decompression:

| measure | count |
| --- | --- |
| payload byte for byte | 2 |
| same number of spaces | 150 |
| same register table | 147 |
| same symbol count | 145 |
| same constructor count | 148 |

The two that match byte for byte are languages whose constructors are all
`unimpl`, which is the only case where writing no p-code is the same as writing
what the reference wrote. Our payload is 43% of the reference's, and the
missing 57% is the p-code.

#### Decoding with what we wrote

The strongest gate, because it does not compare us against ourselves.
`r12e-sleigh`'s decode engine is measured at zero disagreements with objdump on
AArch64, x86-64 and RISC-V. `crates/r12e-sla/tests/slaload/` rebuilds a
decodable model out of a compiled file, so the same bytes can be decoded twice:
once from the specification the front end parsed, once through a `.sla` this
compiler wrote and this reader read. Over 20,000 pseudo-random encodings each:

| language | agree | differ |
| --- | --- | --- |
| AArch64 | 19,992 | 8 |
| RISC-V | 20,000 | 0 |
| x86-64 | 20,000 | 0 |

The eight are AArch64 alias constructors such as `cinv`, whose pattern is
`Rn=Rm & (Rn!=0x1f) & (b_15=0 | b_14=0 | b_13=0)`. The equality is enumerated
as above, but the inequality and the disjunction are not, so the pattern
written matches more than it should and the alias wins an encoding that belongs
to `csinv`. That is a wrong decode, it is counted rather than excused, and the
number is a ceiling the test asserts against.

Everything a decoder needs therefore survives the round trip: the spaces, the
register table, every token field and its width, every attachment, the context
register and its fields, and each constructor's display, operands, patterns and
disassembly actions.

## Reproducing any of this

```
ghidra/support/sleigh some.slaspec some.sla
```

takes a second or two on a small spec. Change one line, recompile, and diff the
two decoded trees. That loop is the whole method, and it is why this document
can say which claims are proved: each one names the edit that moved the bytes.

The tests find a Ghidra tree at `$R12E_GHIDRA_DIR`, at
`~/.local/share/ghidra-cli/ghidra`, at `~/ghidra`, at `~/Ref/ghidra` or at
`/opt/ghidra`, and report and return when there is none.
