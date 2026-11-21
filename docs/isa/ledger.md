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
{"name":"sum","sha256":"a3944f27...","closure":"4ef4bfc7...","level":"L2","depth":0,
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
  of Lean's `Reloc.apply`), must give back the binary's words; a function
  whose words differ is left out ("a misattributed relocation").
- **Per function.** A function that cannot be recovered (an `auipc` with no
  low part, as musl's `__cos` loads a constant with `fld`; a pc-relative
  address in no section) or fails the self-check is left out of the module
  and listed in `Module.skipped` with its reason; `nocompiler module` and
  `ledger` report each on standard error. The rest of the binary is
  recovered: on jq (swe-bin jqlang__jq-2650 base.jq.elf), 1235 functions
  kept, 102 skipped, 3.31 s. Calls to a skipped function stay relocations
  to its symbol, and the Lean layout still gives its address.
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
- **The Lean side, on the whole artifact (7').** Modules in chunks
  (lean/NoCompiler/ModuleChunks.lean; `module::lean_chunks`): one `RChunk`
  per function, all numbers (words, packed relocations, names and symbols
  as numbers), the functions in groups of 32. `module::reuse_lean` writes
  for every function of `a` whose call closure is unchanged in the other
  build a theorem from `Verified` of its closure module in `a` to
  `Verified` of the whole other module (`Verified.of_groups`), or the
  `Refines` of the two images at one layout (`Refines.of_groups`); for a
  changed one, a control (the kernel decides the check is `false`). Each
  file compiled alone (`lean -o`, under the 6 GB cap, shared host):

  | file | theorems | controls | time | max RSS |
  | --- | --- | --- | --- | --- |
  | module a / b / e (1235 functions, 87,242 words) | | | 15.9 / 12.7 / 10.5 s | 1.83 GB |
  | import of two modules only (baseline) | | | 1.40 s | 1.58 GB |
  | Verified, identical rebuild (a to b) | 1235 | 0 | 35.6 s | 2.76 GB |
  | Verified, one-line edit (a to e) | 1234 | 1 (`w_num_chars`) | 34.5 s | 2.84 GB |
  | Refines, identical rebuild | 1235 | 0 | 55.1 s | 2.87 GB |
  | Refines, one-line edit | 1234 | 1 | 54.5 s | 2.90 GB |

  About 28 ms per reused function for `Verified` after the baseline, 0.4 ms
  per instruction of the artifact. Axioms: `r_570` uses propext,
  Classical.choice, Quot.sound; the control `c_1233` none. In the kernel,
  one `RChunk` comparison takes 1.7-2.1 ms (`decide +kernel`, profiler);
  the rest is the walk to the function and the elaboration of each
  statement. The theorems take the closure's `Verified` as a hypothesis:
  the cost measured is the reuse step, not a proof of the function.
- **What made it fit.** Measured on the way, same artifact:
  - names as strings: one name comparison costs 0.2 s in the kernel and the
    distinct-names check is quadratic; a 1235-theorem file did not finish
    in 900 s. Names are numbers now, and distinct names follow from the
    sublist and the larger module's `Ok`, so no string is compared;
  - one flat list: walking to function 1000 costs 50-90 ms, a file 72-90
    s and 4.10 GB. Groups of 32: 34-36 s, 2.8 GB;
  - one literal for `.rodata` (78,496 bytes): 11.2 s for that literal
    alone; parts of 1024 bytes. Relocations as 10,259 structure instances:
    the module took 36.3 s; packed into one number per function, 8-16 s.
- **The CLI:** `nocompiler module FILE --namespace NS --format chunks`
  writes the module in chunks (tests/module_chunks.rs: it is the committed
  Link/{One,Two}Chunks.lean). The reuse files are written by
  `module::reuse_lean`, which has no command yet; the measurement used a
  driver over it.
- **Callees in another order.** When the new build puts a callee before its
  caller, the closure is found in the new order and the theorem carried
  through `Verified.of_perm` (`of_groups_perm`; the `List.Perm` is between
  the same constants, so the kernel compares no chunk twice).
  Examples/LinkChunks.lean `start_reordered`, with a control. None on this
  artifact: the files above are unchanged by it (regenerated, byte-equal).

Not yet: search by specification (the spec is named, not indexed), and
ledger entries for theorems whose specification depends on the layout (data
addresses).
