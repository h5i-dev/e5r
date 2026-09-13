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
| `.sla` compiled here from `.slaspec` written for the experiments | 30-odd, rebuilt per experiment |

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
`print_literal` (8) and `print_operand` (17), then one `construct_tpl` (21) per
p-code section.

| attribute | meaning | evidence |
| --- | --- | --- |
| 22 `parent` | symbol id of the subtable it belongs to | **proved**: constructors of a `Mode:` subtable carry that subtable's id, `instruction`'s carry 0 |
| 25 `source` | index into the `sourcefiles` list | **proved**: moving two constructors into an `@include`d file gave them index 1 while the one left behind kept 0 |
| 24 `line` | line number in that file | **proved**: four constructors on lines 17-20 carry 17, 18, 19, 20 |
| 26 `length` | instruction length in bytes | **proved**: the one constructor spanning two 16-bit tokens carries 4 where the others carry 2 |
| 27 | where the mnemonic ends among the print pieces | **inferred**: 1 in every case observed, and negative values exist in the corpus |

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
construct_tpl [21]   labels, section, delay
  null [11] | handle_tpl [30]      what the constructor exports
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
| 81 | the address after the instruction |
| 80, 83, 84 | not established |

**Proved.** `:add rd, rs { rd = rd + rs; }` compiles to one `op_tpl` with code
19, an output that is operand 0's handle in all three fields, and two inputs
that are operands 0 and 1. `{ rd = sext(imm:1); }` gives code 18. A
`goto [t]` gives code 6. `myop(rd)` after `define pcodeop myop` gives code 9,
and a `{ ... goto <skip> ... <skip> }` gives code 5 with a `const_relative`
target. Those are `INT_ADD`, `INT_SEXT`, `BRANCHIND`, `CALLOTHER` and `CBRANCH`
at their published p-code opcode numbers, so the `code` attribute is the
standard opcode enumeration and not a private one. Element 81 was identified as
`inst_next` because it is what `goto inst_next + imm` puts in the addend.

Codes 60 and 65 appear around a local label and are not in the published
arithmetic set; they are presumably template-only pseudo-operations. They are
reported by number and not named.

## What is not established

These element ids parse cleanly and their place in the tree is known, but their
meaning was not isolated, so the reader keeps them as raw nodes and counts their
bytes:

| ids | what they are | what is missing |
| --- | --- | --- |
| 47-50, 52, 53, 55-57 | pattern expression operators | which operator each one is |
| 59, 61 | leaves of a pattern expression | which symbol each stands for |
| 79 | a record attached to some constructors | its meaning |
| 80, 83, 84 | template leaves | which special value each stands for |

Ids 51, 54 and 58 in that run *were* isolated: a spec containing
`[ val = imm * 4 + 2; ]` produces `54(51(operand, 58:4), 58:2)`, so 51 is
multiply, 54 is add and 58 is a literal. That places the run 47..57 as an
alphabetical enumeration (and, div, lshift, minus, mult, not, or, plus, rshift,
sub, xor) which would name the rest, but an alphabetical run is a pattern and
not a proof, so the reader does not use it. Each is one more small experiment
away.

Attributes 18, 19, 28, 38, 39, 40, 52 are likewise carried through as values
without a name.

## Measured coverage

From `cargo test --release -p r12e-sla`, over the 137 shipped files plus the
committed fixtures. "Interpreted" counts the bytes of every element whose
meaning is established, where an element's bytes are its own tags, ids and
attribute values, excluding its children; summing that over the tree gives the
payload length exactly, so the figure cannot flatter itself.

| measure | value |
| --- | --- |
| files read | 140 |
| decompressed payload | 95,576,250 bytes |
| interpreted | 95,483,898 bytes, 99.90% |
| kept as raw nodes | 92,352 bytes |
| least covered file | `PIC/pic16.sla`, 99.36% |

The raw bytes by element id, largest first: 79 (24,624), 49 (18,276),
53 (10,564), 83 (8,268), 84 (8,268), 56 (6,980), 80 (3,912), 47 (3,088),
61 (2,816), 50 (1,616), 55 (1,512), 52 (1,048). Those are the pattern
expression operators and the three unidentified template leaves, which is
exactly the list in the previous section: the gap the document admits to and
the gap the reader measures are the same gap.

Coverage is not the same as usefulness. Every byte of the spaces, the register
table, the token fields, the symbol table, the constructors, their patterns and
their p-code templates is interpreted; what is missing is the operator names
inside pattern expressions, which matters for a `.sla` whose operands are
computed rather than read straight out of a field.

The test also asserts self-consistency on every file: every symbol id
referenced by a context field, an attached varnode list, an operand or a
constructor resolves to a symbol that exists; every space index resolves; every
symbol has a header record; the symbol and scope counts the file declares match
what was found; and every node's byte range lies inside the payload. All 140
files pass with zero inconsistencies, which is a second independent check that
the format reading is right.

## Reproducing any of this

```
ghidra/support/sleigh some.slaspec some.sla
```

takes a second or two on a small spec. Change one line, recompile, and diff the
two decoded trees. That loop is the whole method, and it is why this document
can say which claims are proved: each one names the edit that moved the bytes.
