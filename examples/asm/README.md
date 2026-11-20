# memset, written in structured assembly and proved

The review's first proposal: a model (or a person) writes structured
assembly with the block/loop nesting and the loop-head invariants, and a
deterministic, untrusted encoder produces the bytes and `.nocompiler.struct`
([docs/isa/asm.md](../../docs/isa/asm.md)). This directory does that for
`memset`, and compares it with the clang path for the same function.

```bash
examples/asm/build.sh                 # assemble memset.s, compile memset.c, compare with examples/elf/
python3 -I examples/asm/test.py       # the assembled binary under qemu-riscv64
cd lean && lake build Examples.Memset Examples.MemsetCc
```

| | hand-written (`nocompiler asm`) | clang (`nocompiler cc -O2`) |
| --- | --- | --- |
| source | [memset.s](memset.s): 12 lines of code and structure, 8 annotation lines | [memset.c](memset.c) |
| binary | `examples/elf/memset.elf`, memset 7 instructions | `examples/elf/memset_cc.elf`, memset 8 instructions |
| proof | [lean/Examples/Memset.lean](../../lean/Examples/Memset.lean) | [lean/Examples/MemsetCc.lean](../../lean/Examples/MemsetCc.lean) |
| specification | [lean/Examples/MemsetSpec.lean](../../lean/Examples/MemsetSpec.lean), shared | the same |

**The specification**: `memset(p, c, n)` returns `p` and leaves the `n` bytes
at `p` all equal to `c`'s low byte; it writes those bytes and nothing else and
uses no stack (with `Verified`: memory safety, the calling convention,
termination).

## How the hand-written one goes

`memset.s` is the listing format with labels and annotations:

```text
memset:
  #spec spec
  #intro ⟨p, c, n⟩ s he ⟨ha0, ha1, ha2, hn⟩
  mv a3, a0
  block @done {
    beqz a2, @done
    loop @fill {
      #inv fun u => ∃ k L, u.reg 13 = p + BitVec.ofNat 64 k ∧ ...
      #measure fun u => (u.reg 12).toNat
      sb a1, 0(a3)
      ...
      bnez a2, @fill
    end loop
  end block
  ret
```

`nocompiler asm memset.s -o memset.elf --skeleton ... --namespace
Examples.Memset.Image` assembles it (the branches to `@done` and `@fill` go
to the block's end and the loop's head; nothing else is expressible, so R3
holds by construction), checks it against the profile, writes
`.nocompiler.struct`, and writes the theorem with the `nocompiler_auto` call
and the invariant at the loop's address (0x11008), which the author never
had to look up. `lean/Examples/Memset.lean` is that skeleton
(`build.sh` checks it starts with exactly what `asm` writes) followed by the
seven verification conditions.

## The comparison

Code lines and tokens, as `demo/tools/count.py` counts them (no comments or
blank lines):

| | invariant + measure | verification conditions | theorem total |
| --- | --- | --- | --- |
| hand-written (`Memset.lean`) | 4 lines, 76 tokens | 7 lines, 80 tokens | 14 lines, 188 tokens |
| clang (`MemsetCc.lean`) | 4 lines, 76 tokens | 7 lines, 80 tokens | 14 lines, 188 tokens |
| shared spec and its two lemmas (`MemsetSpec.lean`) | | | 17 lines, 262 tokens |

**The proofs are the same length, and in fact the same text** apart from
the addresses in the case names. As in the [A/B demo](../../demo/README.md),
the cost of a proof is in the invariant and the facts about the
specification, not in the encoding, and `nocompiler_auto` does everything
that depends on the code on both paths. For a loop this simple clang kept
the same registers (pointer in a3, count in a2) and only reordered the body
(decrement first, the pointer advanced through a4), which the invariant at
the head does not see.

What the hand-written path changes is **effort, not length**:

* **No reverse engineering.** On the clang path the invariant is written
  after reading what clang emitted: which register holds what, where the loop
  head is (0x11198), whether the count is tested before or after the
  decrement. On the hand-written path the author writes the invariant next to
  the code they are writing, at a loop they placed, and the address comes from
  the assembler. For `sum` (lean/Examples/Sum.lean) clang rotated the loop and
  counted down, and the invariant had to be found from the listing; there
  the difference would be larger.
* **No C to shape.** The demo's COBS source had to be rewritten so that clang
  produced a structured loop (demo/README.md); structured assembly cannot
  express an unstructured one.
* **The skeleton is free.** The theorem, its `rintro` and the
  `nocompiler_auto` call with every `loop_inv` at the right address are
  generated; only the verification conditions are written by hand.
* **The code is not what a compiler would choose**, and is as fast as the
  author makes it: 7 instructions here against clang's 8.

The checks: `test.py` runs the assembled binary under qemu on 300 random
payloads (each set to its first byte, the 16 bytes after untouched);
`scripts/check-proof-controls.sh` mutates both binaries (the stored
register, the stride, the loop test, the start of the fill), each of which
must break its proof; `scripts/check-spec-mutations.py` alters the shared
specification, which must break both proofs; and `lean/Audit.lean` checks
both theorems' axioms and that both images are the committed binaries.
