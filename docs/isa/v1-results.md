# Version 1: acceptance criteria, as measured

The criteria are those of [v1.md](v1.md), "Acceptance criteria". Each entry
is filled in by whoever finishes the criterion, with what was run and what
came out, failures included. Criterion 8 decides whether the project may
claim "easier to prove".

| # | Item | Status | Result |
| --- | --- | --- | --- |
| 1 | `sum2` proof size | open | |
| 2 | syscall functions through `nocompiler_auto` | open | |
| 3 | relocation (two links, one proof) | partial (leaf functions) | below |
| 4 | corpus conformance levels | passed | below |
| 5 | `asm(disasm(x)) = x` | open | |
| 6 | negative controls | checker side passed (Rust and Lean, A); audit side passed (B) | below |
| 7 | checking cost at 55/160/500 instructions | open | |
| 8 | demo A/B with calls and frames | open | |
| 9 | LLM-written structured RV64 | open | |

## 4. Corpus conformance (Rust checker)

`cargo test -p nocompiler --test corpus -- --nocapture`, with clang 15.0.7 and
ld.lld 20 on the development host (the spec's survey used clang 18.1.3). The
corpus is every C program in the repository built with `nocompiler cc`
(examples/, demo/src, crates/nocompiler/tests/cc), including tests/cc/frames.c,
24 functions written for R6: saves, spills, address-taken scalars, arrays and
structs passed to callees, sret, calls in loops, eight and nine arguments, a
variable-length array.

- 58 functions, every one with a level: 54 at L2, 2 at L1, 2 at L0.
- Below L2, each with its rule: `nine_args` L1 (R6c: it reads its ninth
  argument above the entry `sp`), `vla` L1 (R5: `sp` written by `sub`),
  `apply` L0 (R2: a call through a function pointer), `call_in_loop` L0 (R3:
  clang 15 rotates this loop into a forward jump into it despite
  `-disable-block-placement`; a clang shape, not a frame question).
- Functions with a frame: 22, of which 21 at L2; the one that is not is `vla`.
- Range lengths: on frames.c the heuristic and DWARF (`-gdwarf-4` and
  `-gdwarf-5`) give the same 10 ranges; with `-g` every range reports DWARF as
  its source, without it the heuristic.

The test asserts all of this except `call_in_loop`, whose level depends on the
clang version.

In Lean: the committed images (examples/elf/{sum,hello}.elf,
demo/elf/{sum,cobs}.b.elf) state `<name>_checked : Struct.level ... = some .l2`
for all 11 of their functions, proved by `decide` against the certificate
`nocompiler export` writes (lean/NoCompiler/Frame.lean). The corpus beyond the
committed images is checked in Rust only.

## 6. Negative controls, checker side

`cargo test -p nocompiler --test levels`: mutations of `sum2` in
examples/elf/sum.elf, checked both against the partition as recorded and with
the partition inferred again from the mutant. Each is below L2 and names the
fault.

| Mutation | Level | Rule |
| --- | --- | --- |
| `ld s0, 16(sp)` replaced by a nop (a restore removed) | L1 | R6e: returns without the entry value of s0 |
| `mv s2, a0` replaced by `sd a0, 16(sp)` (a save slot written mid-function) | L1 | R6e: writes the save slot of s0 with a0 (declared); R6e (inferred) |
| `mv a0, s1` replaced by `addi a0, sp, 16` (a slot's address taken) | L1 | R6d: takes the address of the slot at 16 (declared); R6 (inferred) |
| call distance changed by 4 bytes | L0 | R2: the call no longer reaches an entry |
| `mv s0, a3` replaced by a write to `gp` | L1 | R4 |
| `sd sp, 0(a0)` (sp stored) | L1 | R6a |
| `ld ra, 40(sp)` (past the entry sp) | L1 | R6c |
| a declared partition missing s0's save slot | L1 | R6 |

lean/Examples/FrameControls.lean makes the same faults (and an unbalanced
`addi sp, sp, 16`) in `sum2`'s words and has the kernel refute L2 for each
against the recorded frame and certificate, with no help from Rust; the
unmutated code keeps L2.

tests/profile.rs `each_rule_is_enforced` adds the rules on small assembly
functions: `sp` in arithmetic or stored (R6a), a stack argument (R6c), half a
slot read with `lw` (R6c), a save without a restore and a write without a
save (R6e), and a saved-and-restored register (L2).
## 3. Relocation (agent B, 2026-11-20)

**Done for leaf functions; open for functions with calls.**

* One object, `examples/sum.c` compiled once with `-ffunction-sections`, is
  linked twice (`examples/link/build.sh`): `examples/elf/sum.link1.elf`
  (`.text` at 0x11190, order sum, sum2, _start) and `sum.link2.elf` (`.text` at
  0x40000, order _start, sum2, sum). `nocompiler module` recovers the
  relocatable module of each (words with relocated fields zero; `call`,
  `pcrelHi`, `pcrelLoI` relocations); the two are equal
  (`Examples.Link.same_module`, by kernel evaluation).
* `Examples.Link.sum_relocatable : Verified One.module "sum" Examples.Sum.spec`,
  over every layout. It is not a new proof: `Verified.of_leaf`
  (`lean/NoCompiler/Relocate.lean`) carries `Examples.Sum.sum_verified`, the
  existing proof about `examples/elf/sum.elf`, to every layout, through the
  translation theorem `VerifiedImg.shift` (`lean/NoCompiler/Shift.lean`): code
  with no relocations whose instructions neither read nor write `ra` (other
  than the return) and contain no `auipc` runs the same anywhere. `sum_link1`
  and `sum_link2` are that one theorem at the two layouts; the proof text is
  the same.
* `nocompiler-audit` reads each ELF's layout from its symbol table, checks
  `Module.Ok` there, and that the module linked there is the ELF's `.text` and
  data byte for byte: both pass. This checks `link` (calls and data addresses
  included: `sum2` and `_start` have relocated words) on both binaries.
* All axioms standard (`lean/Audit.lean`).

**Not done:** `sum2` and `_start` call `sum`, so their words differ between
the layouts; a proof of them over every layout needs the call-distance
reasoning at a symbolic layout (T1, owned by A). Functions that read data
(`hello`) need their specification to name the layout (the data's address);
also open.

## 6. Negative controls, audit side (agent B, 2026-11-20)

`scripts/check-audit-controls.sh` patches a copy of a relinked binary and
requires the audit to fail for the stated reason; then the unpatched copy
must pass. All pass:

| mutation | the audit says |
| --- | --- |
| sum2's first call lands 4 bytes past sum (link2) | the module linked at the ELF's layout is not its .text |
| the same, on link1 | the same |
| _start's data address is a page off | the same |
| the symbol table moves sum by 4 | the layout is not the ELF's |
| a byte of .data changes | the module's data at the ELF's layout is not its data sections |
