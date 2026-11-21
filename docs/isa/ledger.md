# The ledger of verified functions

A library of verified functions is useful only if a caller can find one by
what it does and use it without regenerating it. The unit is the triple the
review asked for: bytes, specification, proof. Since v1's proofs are about
relocatable functions (`Verified M f spec`, with `spec : Layout → Spec α`,
[v1.md](v1.md)), the bytes are
the function's relocatable form, which is the same wherever it is linked.

`nocompiler ledger FILE [--proofs TSV]` writes one JSON object per function
of the binary's module (`nocompiler module`, `crates/nocompiler/src/module.rs`):

```json
{"name":"sum","sha256":"75e31c5d...","level":"L2","depth":0,
 "theorem":"Examples.Link.sum_relocatable","spec":"Examples.Sum.spec"}
```

| field | what |
| --- | --- |
| `name` | the symbol, for reading only: not part of the hash |
| `sha256` | SHA-256 of the function's canonical form (`module::canonical`): the line `nocompiler-rfunc 1`, then every word in hex with its relocated fields zero, then every relocation as `reloc OFF KIND SYM ADDEND HIOFF`. Independent of the address and of the function's own name |
| `level` | the conformance level the checker gives it (L0, L1, L2) |
| `depth` | T4's stack bound in bytes: its frame plus its deepest callee's depth; `null` if a callee is unknown or the calls recurse |
| `theorem`, `spec` | the Lean theorem (`Verified M f spec`) and specification, from the TSV (`function<TAB>theorem<TAB>spec`); `null` without a proof |

**Trust.** The ledger is an index, not evidence. A hit says "a function with
these exact relocatable bytes has this theorem"; the theorem is checked by
the Lean kernel, and that the module the theorem is about holds those bytes
at the caller's layout is checked by `nocompiler-audit` (the module audit).

**Example.** `examples/link/ledger.jsonl`, for the module that
`examples/elf/sum.link1.elf` and `sum.link2.elf` are both linked from:
`crates/nocompiler/tests/module.rs` checks that both binaries give that
ledger, hash for hash.

Not yet: search by specification (the spec is named, not indexed), and
ledger entries for theorems whose specification depends on the layout (data
addresses).
