# Toolchain and workflow

## Today: clang, then `e5r`

The profile needs no compiler changes for straight-line, branching and
looping code with direct calls. The flags:

| Flag | Why |
| --- | --- |
| `--target=riscv64-unknown-elf -march=rv64im_zba_zbb -mabi=lp64` | the instruction set; no C, so every instruction is 32 bits |
| `-mno-relax` | calls stay as the compiler wrote them; the linker does not rewrite them |
| `-fno-pic`, static link | no PLT or GOT: calls are direct |
| `-ffreestanding -nostdlib` | no libc, whose code would also have to conform |
| `-fno-jump-tables` (when needed) | a `switch` becomes branches instead of an indirect jump |

`examples/build.sh` is the reference build. Then:

```
e5r check f.elf                     # which functions conform, which rule each one breaks
e5r annotate f.elf -o f.e5r.elf     # record .e5r.struct (docs/isa/metadata.md)
e5r disasm f.e5r.elf                # the code, nested by block and loop
e5r export f.e5r.elf --namespace My.Image -o lean/My/Image.lean
```

`e5r check --json` gives the same report as JSON. Exit status 1 means a
function violates the profile.

## Proving a function

1. Build and annotate the binary; commit the ELF the proof is about (proofs
   are about exact bytes; `examples/elf/` holds the committed ones).
2. `e5r export` it into a Lean module. The module has the `.text` words, an
   `@[e5r_image]` lemma per address naming its instruction, and for every
   conforming function `<name>_entry` and `<name>_dom` (its code and its
   callees').
3. Write the specification and the proof, as in `lean/Examples/Sum.lean`
   ([spec.md](spec.md)). Loop invariants go at the loop heads `e5r disasm`
   shows.
4. Add the ELF and its image to `images` in `lean/Audit.lean`, and the
   theorems to its axiom checks.
5. `lake build && lake exe e5r-audit` in `lean/`.
6. Add mutations of the instructions the proof depends on to
   `scripts/check-proof-controls.sh`; each must make the proof fail.

## Next: inside LLVM

Doing the structure in the compiler means the tree is the compiler's own
(no recovery), and it can be extended to what recovery cannot see. The plan,
not started:

- **A target feature on the RISC-V backend** (`+e5r`) rather than a new
  backend: the profile is a way of using RISC-V.
- **Structured control flow from the WebAssembly backend's passes:**
  `WebAssemblyFixIrreducibleControlFlow` (make the CFG reducible),
  `WebAssemblyCFGSort` (make loops contiguous) and `WebAssemblyCFGStackify`
  (compute the block/loop nesting), run after block placement and branch
  folding, with the tree emitted as `.e5r.struct` by the AsmPrinter.
- **Jump tables** as a fixed pseudo-instruction sequence (bounds check, then
  a table of offsets in `.rodata`) expanded late, so the checker can
  recognise the pattern. Version 0 rejects them.
- **Typed indirect calls** for function pointers, C++ virtual calls and Rust
  `dyn Trait` (which `core::fmt` uses): a call through a table of known
  entries with matching signatures. Version 0 rejects indirect calls.
- **Rust** through a custom target specification: `arch` riscv64, features
  `+m,+zba,+zbb,-c,+forced-atomics`, `panic-strategy` abort, static
  relocation, built with `-Z build-std`, starting from `no_std`.
  `+forced-atomics` lowers atomics to plain loads and stores, which is sound
  for one thread, the profile's model.
- **Proof hints:** loop and source information from the compiler (DWARF line
  tables, Rust's non-aliasing of `&mut`) written next to the tree, as input
  to whoever writes the invariants.

The compiler stays untrusted in all of this: what it writes is either
checked (`e5r check`) or used only as a hint.
