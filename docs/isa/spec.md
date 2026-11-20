# Function specifications and what a proof establishes

The definitions are in `lean/NoCompiler/Spec.lean`; the run predicates in
`lean/NoCompiler/Step.lean`; what they mean for the machine in
`lean/NoCompiler/Adequacy.lean`. This page explains them.

## The predicate a proof is about

`Reach c P D Q s`: every execution from state `s`, with instructions taken
from the code image `c`, reaches a state satisfying `Q`; until it does, it
stays inside the code region `D`, never faults (misaligned access or jump,
an instruction outside the profile, an unmodeled syscall), and only reads and
writes memory the permission `P` allows. It is an inductive predicate, so
every execution is finite: termination is always part of the claim. Where
the environment chooses (how much a `write` accepts, what a `read` returns),
every choice has to reach `Q`.

`Exec c P D Q s` is `Reach` stopped at the first state that leaves `D` or
has exited. That first state is the return, seen from inside a function.

## A specification

```lean
structure Spec (α : Type) where
  pre    : α → State → Prop                 -- on entry
  post   : α → State → State → Prop         -- entry state, state at the return address
  onExit : α → State → State → Prop := ...  -- if it may end the process; False by default
  reads  : α → State → List Region := []    -- memory it may read
  writes : α → State → List Region := []    -- memory it may read and write
  stack  : Nat := 0                         -- bytes below the entry sp it may use
```

`α` holds the logical arguments: for `sum`, the array's address and its
contents as a list. Memory regions may depend on them and on the entry state
(a region at the address passed in `a0`).

`VerifiedImg c D entry spec` says: for every `a` and every state `s` with
`Entry D entry s` (pc at the entry, not exited, return address outside `D`
and 4-byte aligned, `sp` 16-byte aligned) and `spec.pre a s`,

```lean
Exec c (spec.perm a s) D (spec.Done a s) s
```

where `spec.perm a s` allows `reads` for reading, `writes` and
`[sp - stack, sp)` for both, and `spec.Done a s s'` is either

- returned: not exited, `s'.pc = s.reg ra`, `Preserved s s'` (sp, gp, tp,
  s0 to s11 unchanged) and `spec.post a s s'`; or
- exited, and `spec.onExit a s s'`.

So one theorem gives functional correctness (`post`), memory safety (every
access inside `perm`, every access aligned), the calling convention
(`Preserved`, return to `ra`) and termination.

`D` is the function's code together with everything it calls, transitively;
`nocompiler export` writes it as `<name>_dom`. Requiring the return address outside
`D` is what lets "leaving `D`" mean "returning".

### Over every layout: `Verified M f spec` (v1)

`VerifiedImg` is about one code image at fixed addresses. The v1 statement
(`lean/NoCompiler/Module.lean`, [v1.md](v1.md)) is about a module: relocatable
functions (words with their relocated fields zero, and the `call`,
`pcrelHi`, `pcrelLoI`/`S` relocations medany code has) and data.

```lean
def Verified (M : Module) (f : Sym) (spec : Spec α) : Prop :=
  ∀ L, M.Ok L → VerifiedImg (M.link L) (M.dom L f) (L.addr f) spec
```

`L : Layout` gives every symbol an address; `M.Ok L` says the functions are
aligned, inside the image, disjoint, uniquely named, and every relocation in
reach; `M.link L` is the image they make there and `M.dom L f` the code of
`f` and its callees. `Verified.img` gives the code-level statement at any one
layout. `link` is not trusted: the audit compares it, at the layout read from
an ELF, with the ELF's bytes.

## What comes for free

- **Frame** (`VerifiedImg.frame`): memory outside `writes` and the stack region
  is unchanged at return. It is derived from the permission once, in
  `Reach.frame`, and never has to be proved per function.
- **Calls** (`VerifiedImg.call`): inside a caller's proof, a call to a verified
  function continues from every state the callee's specification allows,
  with its frame property, provided the callee's region and permission are
  within the caller's. This is the modular rule: a caller's proof uses the
  callee's specification, never its code.
- **Loops** (`Reach.loop`): an invariant `I` at the loop head and a measure
  that decreases on every trip around the loop.
- **The machine** (`VerifiedImg.hw`, from `lean/NoCompiler/Adequacy.lean`): the step
  relation proofs use takes instructions from the image and checks
  permissions. The machine (`HwStep`) fetches from memory and checks
  nothing. Given that memory holds the image when the function is entered
  (`Code.Loaded`, what the loader does) and that nothing the function may
  write overlaps the code (`Protected`), every machine execution from the
  entry state
  - can always take a step while inside `D`, and every step it can take is
    one the permission allows (`Exec.hw_safe`);
  - satisfies `Done` when it leaves `D` or exits (`Exec.hw_final`);
  - cannot stay in `D` forever (`Exec.hw_terminates`).

## The conditions are the caller's

Nothing enforces a specification at run time. The theorem is conditional:
if the function is entered as `Entry` and `pre` say, the conclusions hold.
Unverified code in the same process can break the precondition, for example
by overwriting the array while `sum` runs (there are no threads in the
model, so only by being the caller). VerifiedImg callers discharge callee
preconditions in their own proofs; the conditions at the outermost verified
function are the assumptions of the whole result.

## Writing a proof

`lean/Examples/Sum.lean` is the worked example: the specification of
`u64 sum(const u64 *a, u64 n)`, the loop invariant at the loop head the
compiler chose, and the proof over the compiled instructions.
`lean/Examples/Sum2.lean` is the example for calls: a 32-byte frame saving
`ra` and three callee-saved registers, two calls through `VerifiedImg.call`, and
the frame reloaded with the lemmas of `lean/NoCompiler/Mem.lean` (a load after a
store at the same and at a disjoint slot, an array untouched by writes
outside it). `lean/Examples/Hello.lean` is the example for syscalls: a
`write_all` loop whose invariant is the trace (`writtenTo` in
`lean/NoCompiler/Trace.lean`), an `ecall` stepped with `Reach.sys_step` and taken
apart by the outcomes `Sys` allows, and a function that ends the process
(`onExit`) and reads `.rodata` (`Segment.Loaded`). The tactics:

| Tactic | Does |
| --- | --- |
| `nocompiler_step [facts]` | steps over one instruction: looks it up in the image, discharges "pc in region" and "not exited", proves the permission side condition when there is none, normalises the next state. A load or store leaves its permission goal and alignment `if`. |
| `nocompiler_steps n [facts]` | `nocompiler_step` n times |
| `nocompiler_norm [facts]` | the normaliser on its own |
| `nocompiler_same` | closes `Same s0 s' rs` (registers outside `rs` unchanged) along a sequence of writes |
| `nocompiler_auto f s he (loop_inv pc inv measure μ)*` | the whole run of a leaf function (`lean/NoCompiler/Auto.lean`): steps every path between the loop heads of its block/loop tree `f`, discharges the permission, alignment, `Same`/`Preserved` and return conditions, and leaves each invariant, measure and postcondition as a goal named after its path, in a normal form of natural numbers and lists |

A conditional branch leaves an `if` on its condition, taken apart with
`by_cases` or `split`. `lean/NoCompiler/Arith.lean` has the word-arithmetic
rewrites compiled code needs (a counter decremented with `addi -1`, a
pointer advanced by a constant, alignment of `a + 8k`). Prefer them to
`simp` on `toNat` of an expression with a 64-bit literal, which can be
very slow.

Facts about the specification rather than the code (buffers updated in
place, folds, the first zero byte, frames and regions) are in
`lean/NoCompiler/Vocab/`; [vocab.md](vocab.md) lists them, and the checks
that a specification says what it should (spec mutation tests, and
computable specifications run against independent references).
