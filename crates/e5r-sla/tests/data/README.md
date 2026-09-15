# `.sla` fixtures

Three tiny compiled SLEIGH files, used by `tests/corpus.rs` so the suite has
something to read on a machine with no Ghidra installed.

Provenance: the `.sinc` sources next to them were written for this repository,
and the `.sla` files are what Ghidra 12.1.3's shipped SLEIGH compiler
(`support/sleigh`, Apache-2.0) produced from them. They are the output of a
compiler run on our own input, and they exist so the format work in
`docs/sla-format.md` is reproducible: recompiling a `.sinc` must give the same
`.sla`.

| file | what it exercises |
| --- | --- |
| `minimal.sla` | the smallest legal language: spaces, two registers, a context field, one constructor with no token |
| `tokens.sla` | a token with four fields, `attach variables`, four constructors, p-code with `INT_ADD`, `INT_SEXT` and `BRANCHIND`, a two-token instruction |
| `subtable.sla` | a subtable operand, `define pcodeop`, a local label and the p-code branch around it |

To rebuild one:

```
/path/to/ghidra/support/sleigh <name>.slaspec <name>.sla
```

with a `.slaspec` that sets `ENDIAN` and `RAMSIZE` and includes the `.sinc`.
