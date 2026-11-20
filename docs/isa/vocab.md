# Spec vocabulary and spec quality

The specification is the last trusted object in a proof (see
[trust.md](trust.md)): the kernel checks that the binary meets it, and
nothing checks that it says what was meant. This page covers the library
specifications are written with, and three checks on specifications
themselves.

## The vocabulary (`lean/NoCompiler/Vocab/`)

Predicates and lemmas for stating a specification and closing the
verification conditions `nocompiler_auto` leaves. `import NoCompiler.Vocab`,
`open NoCompiler.Vocab`.

| Module | What |
| --- | --- |
| `Vocab/List.lean` | lists as buffers. A buffer rewritten in place from the front (`L.drop d = M.drop d`: the rest is still the original; `take_set_succ`: the written prefix grows by the byte written; `drop_set_of_drop`, `take_append_drop_of`). Reading at an index (`getD_take`, `getD_of_drop_eq`, `take_drop_succ`). The first element that passes a test, `List.findIdx` (a terminator, a separator): `getD_not_of_lt_findIdx`, `findIdx_eq_of_getD`, `succ_le_findIdx_of_getD`, in the `getD` form the normal form produces. |
| `Vocab/Fold.lean` | folds over a prefix, for accumulating loops, counted up (`foldl_take_succ`, `foldl_eq_take_succ`) or down, the way clang rotates them (`foldl_take_sub_pred`, `foldl_eq_last`), and the empty case. |
| `Vocab/Word.lean` | fixed-width facts the normal form does not cover: bytes as numbers (`byte_beq_zero_iff`, ...), the sign bit of a small result (`neg_ofNat_ushiftRight_63`: `srli a0, a0, 63` of an error), alignment of a frame below an aligned `sp` (`aligned_sub_ofNat`, `aligned_of_dvd`). |
| `Vocab/Memory.lean` | memory, regions and frames. A buffer survives a change outside it (`readBytes_frame`; `arr64_congr` for words is in `NoCompiler/Mem.lean`); `Region.Disjoint.not_mem`; a function's permission from its own regions and stack (`Spec.canWrite_of_mem`, `canRead_of_mem`, `canWrite_stack`); a callee with no writes and no stack writes nothing (`Spec.not_writable_of_nil`, the frame of a call to it); slots of the frame below the entry `sp` (`stack_covers`) and a callee's stack inside the caller's (`stack_within`). |

The predicates themselves are the core's: `arr64` and `arrRegion`
(`NoCompiler/Mem.lean`), `readBytes`, `Region`, `Region.Disjoint` and
`Region.within`, `writtenTo` (`NoCompiler/Trace.lean`).

**What moved, and what it saved** (`examples/demo/tools/count.py`: code lines and
tokens without comments or blank lines):

| | before | after |
| --- | --- | --- |
| `Demo/CobsSpec.lean`: lemmas about the specification | 132 lines, 1899 tokens | 59 lines, 980 tokens |
| `Demo/CobsSpec.lean`: the specification | 38 lines, 465 tokens | 36 lines, 454 tokens (`frameLen` is `List.findIdx (· == 0)`) |
| `Demo/SumSpec.lean`: lemmas | 13 lines, 205 tokens | 7 lines, 152 tokens |
| `Demo/CobsB.lean`, `CobsA.lean`: the proof | 95 lines, 1412 / 1413 tokens | 94 lines, 1403 / 1404 tokens |
| `Demo/SumB.lean`, `SumA.lean` | 12 lines | 12 lines (unchanged) |
| `lean/NoCompiler/Vocab/` (new, shared) | | 197 lines, 2817 tokens |

What remains in `CobsSpec.lean` is about COBS (one block of
`decodeFrame`, the loop invariant unfolded by a block, the report). The
proofs themselves hardly change: their verification conditions were already
calls to named lemmas, and the cost of a new function is in its
spec-specific lemmas, which is what the vocabulary takes the generic part
of. `Examples/Sum2.lean` and `Examples/Hello.lean` (frames, calls,
syscalls) are being re-proved with `nocompiler_auto`; the frame lemmas in
`Vocab/Memory.lean` are for that and for callers in general.

## Spec mutation tests (`scripts/core/check-spec-mutations.py`)

`scripts/core/check-proof-controls.sh` changes the binary and requires the proof
to fail: the proof depends on the code. This script changes the
specification and requires every proof of it to fail: the specification
pins down what the code does. For each mutation it alters one piece of one
specification in a copy of `lean/`, rebuilds the proofs, and requires each
to fail; then it requires the unaltered copy to pass.

| kind | mutation | if a proof still checks |
| --- | --- | --- |
| `post` | a constant of the postcondition changed, the result read from another register, the result function changed (`sumW` starting at 1, or xor instead of add), a count off by one | the postcondition does not determine that part of the result: **too weak** |
| `pre` | a conjunct of the precondition replaced by `True` (in place, so the proof's `rintro` still matches and a failure means the fact was used) | the precondition has a conjunct no proof needs: the theorem could be stronger |
| `frame` | a region narrowed (`reads` empty, one word short, 16 of the 24 result bytes), a smaller stack | the permission is wider than the code needs |

A mutation counts only if the altered specification is well formed: an
error inside a `def` or `structure` (rather than in a theorem) is reported
as INVALID. A surviving mutation is a failure of the check either way; the
fix is to the specification (or, for a `pre` that turns out unnecessary, to
drop the conjunct and re-prove), never to the list.

```bash
python3 -I scripts/core/check-spec-mutations.py --list           # what it does
python3 -I scripts/core/check-spec-mutations.py --only Examples/Sum
python3 -I scripts/core/check-spec-mutations.py                  # all (about 20 minutes: COBS is ~40 s a build)
```

**Result** (2026-11-20): all 33 mutations break their proofs, on `sum`,
`sum2`, `write_all`, `hello` and the demo's `sum` and `cobs_decode` (both
builds); no specification was found too weak. Two observations:

* The COBS postcondition mutations (the tag, the counts, the 255 rule, the
  empty case) fail in the lemmas about the specification
  (`CobsSpec.lean`: `report_of`, `decodeFrame_drop`, `report_empty`), not in
  the two proofs over the code: those lemmas are stated about `report`, so
  altering `report` breaks them first. That is still the proof failing, but
  the check does not show the proof over the code would have failed on its
  own.
* The precondition conjuncts tested are all needed: alignment, the length
  bound, the array's contents, and, for COBS, the slot's alignment, its
  disjointness from the buffer and `len < 2^63`.

The core job of CI runs every mutation but COBS's (a few minutes); the
manual `spec-mutations` workflow runs all of them (about 15 minutes).

## Executable specifications against references (`scripts/core/check-spec-references.py`)

Where a specification is computable, evaluating it is a way of reading it.
`lake exe spec-eval` (`lean/SpecEval.lean`) runs the specifications' own
definitions on inputs from stdin; the script compares the answers with
references written independently, in Python, from the description of each
function rather than from the Lean text:

| function | specification | reference |
| --- | --- | --- |
| `sum`, `sum2` | `Examples.Sum.sumW`, `Demo.Sum.sumW` (sum2's post is `sumW xs + sumW ys`) | Python's `sum` mod 2^64 |
| `cobs_decode` | `Demo.Cobs.report` | the decoder of `examples/demo/test/cobs_test.py`, the one the binaries are tested against under qemu |
| `write_all` | `NoCompiler.writtenTo` | the bytes of a trace of writes to one fd |
| `hello` | `Examples.Hello.message` and the full length in `helloSpec` | the string in `examples/hello.c` |

**Result** (2026-11-20): 3,000 cases each for `sum`, `cobs_decode` and
`write_all`, all agreeing. On the rename commit it caught a real
inconsistency: the message in `examples/hello.c` had become 18 bytes while
the specification said 11 (main's fix, cb1a45f, made it 11 again). It runs
in the core job of CI.
