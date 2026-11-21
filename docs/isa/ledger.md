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
{"name":"sum","sha256":"75e31c5d...","closure":"b58d12d1...","level":"L2","depth":0,
 "theorem":"Examples.Link.sum_relocatable","spec":"Examples.Sum.spec"}
```

| field | what |
| --- | --- |
| `name` | the symbol, for reading only: not part of the hash |
| `sha256` | SHA-256 of the function's canonical form (`module::canonical`): the line `nocompiler-rfunc 1`, then every word in hex with its relocated fields zero, then every relocation as `reloc OFF KIND SYM ADDEND HIOFF`. Independent of the address and of the function's own name |
| `closure` | the reuse key: SHA-256 over the function's and every callee's (transitively, through call relocations) name and canonical form, sorted by name. Two builds agree on it exactly when `Verified.of_sub`'s side condition holds for the function (below) |
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

## Reuse of unchanged code

`Verified.of_sub` (`lean/NoCompiler/Relocate.lean`): a theorem `Verified M f
spec` holds in every module `M'` that contains `M`'s functions unchanged as
`RFunc`s, wherever `M'` puts them. Its side conditions are decided by
comparing those `RFunc`s, which costs the kernel about what comparing their
words costs:
- `∀ g ∈ M.funcs, g ∈ M'.funcs`;
- `M`'s names are distinct.

The ledger's `closure` key says, without Lean, which functions this applies
to: those whose closure key is the same in both builds.

`Refines.of_sub` / `Refines.of_sub_verified`
(`lean/NoCompiler/RefineReuse.lean`): two modules that both hold `M`'s
`RFunc`s and link at a layout `L`. On `f`'s code region, the second image
refines the first, with no stepping (`RefinesRel.of_code_eq`: the images
agree there). A's run comes from `M`'s `Verified` theorem.
`Examples.LinkReuse.sum_refines_rev`: `sum` in a module with the functions in
the other order, at sum.link1.elf's layout, all conditions decided.

**How a module is recovered** (`module::of_binary`):
- **Self-check.** Every recovered relocation is checked: the module,
  relinked at the binary's own addresses (`module::patched`, the Rust twin
  of Lean's `Reloc.apply`), must give back the binary's words, or recovery
  fails ("a misattributed relocation").
- **Unique names.** Local functions that share a symbol (a crate linked
  twice) get `#k`, their rank by address among the namesakes.
- **Low parts.** The `%pcrel_lo` users of an `auipc` are the instructions its
  value reaches, by a reaching-definitions dataflow over the function's
  control flow. Branches and `jal zero` are followed, and a call keeps the
  callee-saved registers. A read reached by several definitions is left
  unattributed: its word stays in the key, a missed reuse but not a wrong
  one.

**Measured** on the rustc artifact of criterion 7' (examples/refine/targets,
1235 functions, 685 at L1 or above; built with
`scripts/core/bench-scale-build.sh` in three directories, `a`, `b`, and `e`
with `w_num_chars` returning `+ 1`). `nocompiler ledger` takes 0.27-0.31 s
per binary, self-check included:

| | own key changed | closure key changed |
| --- | --- | --- |
| identical rebuild (a vs b) | 0 of 1235 | 0 of 1235 |
| one-line edit (a vs e) | 1 of 1235 | 1 of 1235 |
| one-line edit, L1+ functions | 1 of 685 | 1 of 685 |

- **Linked bytes vs keys.** For the same edit, linked bytes change for 191
  of the 685 L1+ functions (criterion 7', v1-results.md). The relocatable
  key changes for exactly one: `w_num_chars`, the edited function, and its
  closure key with it.
- **Before the dataflow,** a linear scan missed one low part in `acos` and
  reported 2 own and 3 closure keys changed.
- **Not yet:**
  - the Lean-side measurement on the whole artifact. It needs the whole
    module as Lean, the format A is redesigning (round2-next.md, 03:58).

Not yet: search by specification (the spec is named, not indexed), and
ledger entries for theorems whose specification depends on the layout (data
addresses).
