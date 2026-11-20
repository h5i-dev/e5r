# Refinement: B refines A

The relational layer of [spec-v1's criterion 9'](v1-results.md): an edited function B is proved to behave like the original A. A itself is the specification. No postcondition is written by hand.

Status:
- Items 1 and 2 are done.
- Certificates with lockstep pairs and regions are done, with the base case of a region: a changed instruction.
- Item 6 (straight-line equivalence, B) is done for register-only blocks.
- Still to do: the rest of item 3 (same-shaped loops), item 4 (differently shaped regions), item 5 (tree diff, B), and loads and stores in item 6. See the end of this page.

## The statement (`lean/NoCompiler/Refine.lean`)

```lean
def Refines (sp : Spec α) (cA : Code) (DA : Dom) (eA : Word) (cB : Code) (DB : Dom) (eB : Word) : Prop :=
  ∀ a s, Entry DA eA s → ¬ DB.mem (s.reg Reg.ra) → sp.pre a s →
    Exec cA (sp.perm a s) DA (fun _ => True) s →
    Exec cB (sp.perm a s) DB
      (fun tb => ∃ ta, Run cA (sp.perm a s) DA s ta ∧ Final DA ta ∧ Obs (sp.dead s) ta tb)
      (s.setPc eB)
```

On every entry state where A's run under the permission `sp.perm` is safe and terminates, B's run from the same state (at B's entry), under the **same** permission, is safe and terminates too. Every way B can end is a way A can end (`Run`: some run of A), with the same observations. Only `pre` and the permission of `sp` play a part. Its postcondition is not used.

- **Observations** (`Obs`).
  - On return: the pc, a0 and a1, the preserved registers (sp, gp, tp, s0–s11), the event trace, and all of memory except the dead stack (the `sp.stack` bytes below the entry sp).
  - On exit: the exit status and the trace.
  - Caller-saved registers other than a0/a1 may differ, and so may the dead stack.
- **Syscalls.** The environment's choices (how much a `write` accepts, what a `read` returns) are matched through the trace, which records them. This makes the claim trace refinement: B's behaviours are a subset of A's.
- **Aborts.** An exit is an observation. Wherever A aborts, B must abort with the same status after the same events.
- **Where A fails.** If A faults, steps outside the permission, makes a syscall the model does not admit, or does not terminate, the claim says nothing about B on that state. The permission and the precondition are therefore part of what is claimed. A permission too small for A would make the claim vacuous, so each use should come with a proof that A runs under it, for example A's own `VerifiedImg`.

## What it gives

| Theorem | Says |
| --- | --- |
| `Refines.refl` | every function refines itself |
| `Refines.trans` | a sequence of proved edits is proved |
| `Refines.verified` | a `VerifiedImg` of A gives one of B, for every spec whose postcondition sees only observations (`Spec.ObsInv`) and that does not look at the entry pc (`Spec.PcFree`). It holds for callers whose return address is not in A's code (`Spec.avoid DA`), which is decidable at a concrete call site. The call rule and the adequacy theorems then apply to B unchanged. |
| `Refines.of_sim` | the proof method: a simulation relation between A- and B-states. Every B step is matched by one or more A steps, or by none with a measure decreasing. B's termination comes from A's, by induction on A's `Reach`. |
| `Refines.of_bigSim` | the same with big steps. From related states, every run of B reaches states related to states A reaches in one or more steps. The obligation may use A's whole safe run from there. Single steps, blocks and regions are all instances. |

## The congruence rule (`lean/NoCompiler/RefineCongr.lean`)

`Agree L sa sb` means equal on the registers in `L`, on memory, on the trace and on the exit status. The pc is related separately, so the two functions may be at different addresses.

- `exec_congr`, proved once for every straight-line instruction: from states agreeing on `uses i ∪ (L ∖ defs i)`, the instruction faults on both or on neither, and the results agree on `L`.
- `sys_congr` does the same for `ecall`: B's environment outcome is one A's environment allows, with agreeing results.
- `instrOk_congr` (the permission an instruction needs) and `evalBr_congr` (branch direction) follow the same pattern.

Liveness is not trusted. The live sets are a certificate, and what is used of them is the inclusion `Instr.transfer`, decided by the kernel.

## Lockstep certificates (`lean/NoCompiler/RefineLockstep.lean`)

A certificate is a list of pairs `(pb, pa, live)`: B at `pb` runs in step with A at `pa`, agreeing on `live`. `Lockstep.check` decides in the kernel that:

- each pair has the same word on both sides, inside the two code regions, and does not write ra;
- every successor of a pair (fall-through, branch target, `jal` target) is a pair, with the transfer inclusion holding at each one;
- a return is reached with ra, a0, a1 and the preserved registers live;
- the two entries are a pair.

`Refines.of_lockstep` is the soundness theorem: `check … = true → Refines sp A B`, for every `sp`. It covers leaf functions only. It is the base case of paired execution (item 3), whose other cases add pairs of *different* instructions, each with an equivalence obligation.

**Regions** (`lean/NoCompiler/RefineRegion.lean`). A certificate also has regions, `RRegion`. Each pairs an interval of B's code with one of A's, with one entry and one exit each and live sets at both, and stands for a changed interval. Its obligation `RRegion.Ok` is a local refinement under every permission:
- from agreeing entry states where A's run through its interval is safe, B's run through its interval is safe;
- every way B leaves it is matched by a way A does: both at their exits, agreeing on `liveOut`, with ra kept; or both exited with the same status and trace.

The check decides a region's shape: entries inside the intervals, exits outside them, intervals inside the functions' code, and the exit a point of the certificate whose live set `liveOut` covers. The contents are proved separately.

`Refines.of_cert`: `check … = true → (∀ r ∈ regions, r.Ok cA cB) → Refines sp A B`. `RRegion.Ok.of_instr` proves the one-instruction case from the two instructions' equivalence on agreeing states (and B's access being A's). Straight-line blocks (item 6) and loops (items 3 and 4) are further ways of proving `Ok`.

**Example** (`lean/Examples/Refine/Relink.lean`). `sum` as linked in examples/elf/sum.link2.elf (`.text` at 0x40000) refines `sum` in examples/elf/sum.elf. The 9-pair certificate is checked by `decide +kernel` in about a second. `Refines.verified` then turns `Examples.Sum.sum_verified` into `sum`'s theorem at link 2 (for callers outside A's code), a second, independent route to what `Examples.Link.sum_link2` gets by translation.

**Example with an edit** (`lean/Examples/Refine/Peephole.lean`). B is `sum` with `addi a0, a2, 0` replaced in place by `add a0, a2, zero`. The certificate has 8 lockstep pairs and 1 region (the changed instruction, by `Ok.of_instr`, about 10 lines). `sum_peephole` gives B `sum`'s theorem. Controls:
- the loop's `add` changed to `sub` outside the region is rejected by the check;
- `sub a0, zero, a2` inside the region passes the check, because the check does not look at a region's contents, but the region's equivalence is false at a2 = 1.

**Negative controls** of the relink example, in its file: four mutated B's (`add`→`sub`, `ld`→`lw`, `bne`→`beq`, stride 8→4) are rejected by the check, and the unmutated B passes. These controls only show that the certificate fails. Showing that the mutant is *not* a refinement is the job of the differential runner (open).

All theorems use only the standard axioms (`lean/Audit.lean`).

## Item 6: straight-line equivalence (B)

`lean/NoCompiler/RefineStraight.lean`. Two sequences of register
instructions (`Instr.alu`: `lui`, the immediate and register ALU operations,
the W forms, shifts, Zbb's unary operations; no loads, stores, jumps or
`ecall` in this first version) are equivalent from live-in registers `L` to
live-out registers `L'`:

```lean
def SeqEquiv (L L' : List Reg) (as bs : List Instr) : Prop :=
  ∀ ga gb : RegFile, (∀ r ∈ L, ga.get r = gb.get r) →
    ∀ r ∈ L', (runRegs as ga).get r = (runRegs bs gb).get r
```

`SeqEquiv.agree` lifts it to machine states and `Agree` (RefineCongr.lean):
from states agreeing on `L`, both sequences run without faulting
(`execSeq`), end agreeing on `L'` with memory, trace and exit status
unchanged, at `pc + 4 * length` on each side. That is the obligation a pair
of different straight-line intervals leaves in paired execution (item 3).

Two tactics, two trust tiers ([trust.md](trust.md)):

- `seq_equiv`: one bit-vector equation per live-out register, closed in the
  kernel (`rfl`, `bv_normalize`, `bv_omega`, `simp`, `ac_rfl`). Standard axioms.
- `seq_equiv_bv`: the same, then `bv_decide`. The theorem depends on an axiom
  of native computation; the audit checks it with `#assert_bv_tier` and lists
  it separately.

**As a region** (`lean/NoCompiler/RefineStraightRegion.lean`):
`RRegion.ok_of_seqEquiv` proves C's `RRegion.Ok` for a straight-line
changed interval: A's interval holds `as` at `pa` (`Code.holds`, decided by
the kernel), B's holds `bs` at `pb`, each `domX` is exactly those words
(`seqDom`), the exits are just past them, `as` does not write `ra`, and
`SeqEquiv liveIn liveOut as bs`. No entry condition. Example: `mulRegion_ok`.

**Examples** (`lean/Examples/Refine/Straight.lean`): in the kernel tier,
`slli a0,a0,3` = `sh3add a0,a0,zero`; strength reduction `li t0,8; mul
a0,a0,t0` = `slli a0,a0,3` (t0 dead); `slli t0,a1,3; add a0,a0,t0` =
`sh3add a0,a1,a0`. In the bv_decide tier: a branchless minimum (5
instructions) = Zbb `min`; rounding up to 8 by shifts = by `andi`. Controls,
refuted in the kernel by a counterexample: `slli 3` is not `slli 2`, and
the strength reduction is not an equivalence when the temporary is live out.

## Open (plan: STATUS-C)

- **Item 3, paired execution (rest).** Same-shaped loops with relational invariants at the paired heads (by default, the live state is equal), as a way to prove `RRegion.Ok`.
- **Item 6 (B), loads and stores** in straight-line sequences (above: registers only).
- **Item 5 (B), tree diff.** `nocompiler refine A.elf B.elf FUNC`: pairs the two block/loop trees, prints the changed intervals, and writes the certificate and the obligations.
- **Item 4, region equivalence.** A differently shaped interval is cut out as a subtree on both sides, with an exit relation (k:1 unrolling, local summaries). Assumptions not derivable from A become explicit, reported preconditions.
- **Frames.** Memory equal outside the dead stack, with different frame layouts in A and B (after A's T2).
- **Calls.**
- **A differential runner** that reports `refuted` with a counterexample.
