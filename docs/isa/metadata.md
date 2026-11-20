# The `.nocompiler.struct` section

Each function's block/loop tree (with labels), its callees, its frame's
partition into slots and address-taken ranges, the conformance level the
checker reached and its stack depth (docs/isa/v1.md, "Metadata v2"). It is
written by `nocompiler annotate` for clang's output and by `nocompiler asm`
for the structured form. The section has no `SHF_ALLOC` flag, so it is not
loaded: stripping it, or never having it, changes nothing about how the
binary runs. The encoder and decoder are `crates/nocompiler/src/meta.rs`.

## Use

- `nocompiler check` checks a binary with the section against what it
  records, and reports rule M1 when a recorded level, frame, callee list or
  size is not what the code has. The recorded tree and frame partition are
  the checker's input for R3 and R6, as a declaration is: a wrong one makes
  the function fail those rules, never pass them. Without the section the
  checker recovers the tree itself.
- `nocompiler disasm` prints the code nested by the tree, with the labels;
  with the tree, the structured program is the listing.
- `nocompiler export` writes the tree, the partition and the level as Lean
  definitions, and the kernel evaluates the checker on them
  (`<name>_checked`).

Nothing in a proof depends on the section being right: a proof that relied
on a wrong tree or partition would not check.

## Encoding, version 2

Little-endian throughout. Every position is an offset from the function's
entry, and functions and callees are named by symbol, so a table stays true
wherever the linker places the functions (and the same object linked twice
carries the same bytes).

```text
table    magic "NCST"  version:u16 = 2  reserved:u16 = 0  nfunc:u32  func * nfunc
func     name:str                          the function's symbol
         size:u32                          bytes of code
         level:u8                          0 = L0, 1 = L1, 2 = L2
         reserved:u8 = 0  reserved:u16 = 0
         frame:u32                         own frame: bytes below the entry sp (R5)
         depth:u32                         frame + deepest callee's depth (T4);
                                           0xffffffff = not known
         ncallees:u16  callee:str * ncallees           (symbols, sorted, distinct)
         nnodes:u32    node * nnodes                   (pre-order)
         nslots:u16    slot * nslots
         nranges:u16   range * nranges
         next:u32      ext:[u8; next]                  reserved for proof hints
node     kind:u8 (0 block, 1 loop)  depth:u8  reserved:u16 = 0
         start:u32  end:u32                            offsets from the entry
         label:str                                     length 0: no label
slot     off:u32  kind:u8 (0 save, 1 spill)  reg:u8  reserved:u16 = 0
range    off:u32  len:u32  source:u8  reserved:u8 = 0  reserved:u16 = 0
str      len:u16  bytes:[u8; len]                      UTF-8, not terminated
```

- A node covers `[start, end)`. Pre-order with depths rebuilds the tree: a
  node at depth `d + 1` is a child of the closest preceding node at depth
  `d`. The function body is the implicit root and has no node. A block's
  label names its end, a loop's its head (`br $l`).
- Slot and range offsets count from the bottom of the frame (the entry `sp`
  minus `frame`). A slot is 8 bytes, 8-aligned. A save slot names the
  register whose entry value it holds (`reg`, 1 for `ra`); a spill slot has
  `reg` 0. Bytes in no slot and no range are unused.
- A range's `source` says where its length came from: 0 declared by the
  writer (the structured form), 1 the variable's size in the DWARF debug
  information, 2 a heuristic (the gap up to the next slot or range) when
  there was none (v1 decision 5). `nocompiler annotate` reports which.
- `depth` is unknown when a callee is not described by the same section (an
  object not yet linked with it).
- `ext` is carried through unchanged by readers; its contents are not yet
  defined.

A section is one or more tables back to back: a linker concatenates the
`.nocompiler.struct` sections of its inputs. A reader rejects a bad magic, an
unknown version, nonzero reserved bytes, a node kind other than 0 or 1, a
depth that increases by more than one, an unknown level, slot kind or range
source, and a table cut short. A callee that names no function of the file,
or a function whose name is not one, is an error when the section is placed
on a file.

## Version 1

Version 1 tables are still read: they gave the entry and node positions as
absolute addresses and callees as entry addresses, and had no labels, slots,
ranges, level or depth. Read, a version 1 function is at level L1 with an
empty partition.

```text
header   magic "NCST"   version:u16 = 1   reserved:u16 = 0   nfunc:u32
func     entry:u64   size:u64   frame:u64
         name_len:u16   name:[u8; name_len]
         ncallees:u32   callee:u64 * ncallees      (entries, ascending)
         nnodes:u32     node * nnodes              (pre-order)
node     kind:u8 (0 block, 1 loop)   depth:u8   reserved:u16   start:u64   end:u64
```

The spec's "function identified by its symbol table index" is implemented as
the symbol's name: indices change when a linker merges symbol tables, names do
not.
