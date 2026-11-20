# The `.e5r.struct` section

Each function's block/loop tree, frame size and callees, written by
`e5r annotate` (and, later, by the compiler). The section has no `SHF_ALLOC`
flag, so it is not loaded: stripping it, or never having it, changes nothing
about how the binary runs. The encoder and decoder are
`crates/e5r/src/meta.rs`.

## Use

- `e5r check` checks a binary with the section against the trees in it, and
  reports rule M1 when a recorded frame, callee list or size is not what the
  code has. Without the section it recovers the trees itself.
- `e5r disasm` prints the code nested by the tree; with the tree, the
  structured program is the listing.
- A compiler that knows the structure writes it, and a proof uses it to find
  the loop heads, which is where invariants go.

Nothing in a proof depends on the section: `e5r export` writes the tree's
information (entries, code regions) as Lean definitions next to the
instruction words, and a proof that relied on a wrong one would not check.

## Encoding

Little-endian throughout.

```text
header   magic "E5RS"   version:u16 = 1   reserved:u16 = 0   nfunc:u32
func     entry:u64   size:u64   frame:u64
         name_len:u16   name:[u8; name_len]       (UTF-8, not terminated)
         ncallees:u32   callee:u64 * ncallees      (entries, ascending)
         nnodes:u32     node * nnodes              (pre-order)
node     kind:u8 (0 block, 1 loop)   depth:u8   reserved:u16   start:u64   end:u64
```

A node covers `[start, end)`. Pre-order with depths rebuilds the tree: a node
at depth `d + 1` is a child of the closest preceding node at depth `d`. The
function body is the implicit root and has no node. `frame` is the number of
bytes below the entry `sp` the function's own code uses (rule R5); callees'
frames are not included.

A reader rejects an unknown version, a node kind other than 0 or 1, a depth
that increases by more than one, and trailing bytes.
