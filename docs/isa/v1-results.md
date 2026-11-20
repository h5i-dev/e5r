# Version 1: acceptance criteria, as measured

The criteria are those of [v1.md](v1.md), "Acceptance criteria". Each entry
is filled in by whoever finishes the criterion, with what was run and what
came out, failures included. Criterion 8 decides whether the project may
claim "easier to prove".

| # | Item | Status | Result |
| --- | --- | --- | --- |
| 1 | `sum2` proof size | open | |
| 2 | syscall functions through `nocompiler_auto` | open | |
| 3 | relocation (two links, one proof) | open | |
| 4 | corpus conformance levels | passed (Rust checker; Lean side pending) | below |
| 5 | `asm(disasm(x)) = x` | open | |
| 6 | negative controls | checker side passed; audit side (B) open | below |
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

tests/profile.rs `each_rule_is_enforced` adds the rules on small assembly
functions: `sp` in arithmetic or stored (R6a), a stack argument (R6c), half a
slot read with `lw` (R6c), a save without a restore and a write without a
save (R6e), and a saved-and-restored register (L2).
