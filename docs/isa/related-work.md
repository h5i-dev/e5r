# Related work

What the profile borrows, and from where.

- **Software fault isolation** (Wahbe, Lucco, Anderson and Graham, SOSP 1993)
  and **Native Client** (Yee et al., IEEE S&P 2009): restrict machine code
  so a small validator can establish a property of it. NaCl aligned x86 code
  in 32-byte bundles and masked indirect jumps. **RockSalt** (Morrisett et
  al., PLDI 2012) verified such a validator in Coq. The e5r profile takes
  the "restrict the code, then checking is easy" idea, without enforcement
  at load time.
- **eBPF**: the kernel runs only programs its verifier accepts, which checks
  bounded loops, memory access ranges and types statically. The profile's
  rules R1 to R5 are in that spirit; unlike eBPF, a program that breaks them
  still runs, and the guarantee comes from a proof, not from the checker.
- **WebAssembly**: structured control flow (`block`, `loop`, `br`) and a
  mechanised specification. Rule R3 is WebAssembly's structuring applied to
  machine code, and LLVM's WebAssembly backend already computes it
  ([toolchain.md](toolchain.md)).
- **Proof-carrying code** (Necula, POPL 1997) and **typed assembly
  language** (Morrisett, Walker, Crary and Glew, POPL 1998): ship code with
  a proof that a small checker validates. e5r is this with Lean as the
  checker; the cost that kept it rare, someone having to write the proofs,
  is what a model writing them changes.
- **Decompilation into logic** (Myreen, Gordon and Slind): machine code
  translated into functions inside a theorem prover, with a proof of the
  translation. The block/loop tree is what makes that translation direct.
- **Vale** and **Jasmin**: verified cryptographic code written close to
  assembly.
- **CompCert** and **CakeML**: observable behaviour as a trace of I/O events,
  with the environment as an oracle. `lean/E5R/Env.lean` follows them.
- **Sail**: the official formal model of RISC-V, with a Lean backend. The
  definitions in `lean/E5R/Machine.lean` are hand-written for the subset and
  tested against qemu; generating them from Sail and proving the two equal
  is on the [roadmap](../ROADMAP.md).
- **LNSym** (AWS): symbolic simulation of Armv8 machine code in Lean 4, used
  to verify cryptographic code; a reference for state representation and
  automation in Lean at this level.
- **Islaris** (PLDI 2022): machine-code verification against full ISA models
  with separation logic in Iris.
