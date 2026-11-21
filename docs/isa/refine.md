# Refinement: B refines A

The relational layer of [spec-v1's criterion 9'](v1-results.md): an edited function B is proved to behave like the original A. A itself is the specification. No postcondition is written by hand.

Status:
- Items 1 and 2 are done.
- Certificates with lockstep pairs and regions are done, with the base case of a region: a changed instruction.
- Item 6 (straight-line equivalence, B) is done for register-only blocks.
- Still to do: the rest of item 3 (same-shaped loops), item 4 (differently shaped regions), item 5 (tree diff, B), and loads and stores in item 6. See the end of this page.

## The statement (`lean/NoCompiler/Refine.lean`)

```lean
def ARuns (sp : Spec α) (cA : Code) (DA : Dom) (eA : Word) : Prop :=
  ∀ a s, Entry DA eA s → sp.pre a s → Exec cA (sp.perm a s) DA (fun _ => True) s

def RefinesRel (sp : Spec α) (cA : Code) (DA : Dom) (eA : Word) (cB : Code) (DB : Dom) (eB : Word) : Prop :=
  ∀ a s, Entry DA eA s → ¬ DB.mem (s.reg Reg.ra) → sp.pre a s →
    Exec cA (sp.perm a s) DA (fun _ => True) s →
    Exec cB (sp.perm a s) DB
      (fun tb => ∃ ta, Run cA (sp.perm a s) DA s ta ∧ Final DA ta ∧ Obs (sp.dead s) ta tb)
      (s.setPc eB)

structure Refines (sp : Spec α) (cA DA eA cB DB eB) : Prop where
  runs : ARuns sp cA DA eA            -- A runs, from every entry sp allows
  rel  : RefinesRel sp cA DA eA cB DB eB
```

`Refines` has two parts (decision 2026-11-21 (3)). `runs` is a full proof
that A runs safely and ends from every entry `sp` allows; `ARuns.of_verified`
gets it from A's `VerifiedImg`. `rel` is the relation: on every entry state
where A's run is safe and terminates, B behaves as A. `RefinesRel` alone is
conditional on A's run, and is vacuous for an A that never runs:
lean/Examples/Refine/Vacuous.lean shows an A of one illegal word with a
`RefinesRel` to any code, and no `Refines` from it. The proof methods
(`RefinesRel.of_sim`, `.of_bigSim`, `.of_cert`) prove `rel`. `Refines.of_sim`,
`.of_bigSim`, `.of_cert` and `.of_lockstep` take `hA : ARuns …` as well.

On every entry state where A's run under the permission `sp.perm` is safe and terminates, B's run from the same state (at B's entry), under the **same** permission, is safe and terminates too. Every way B can end is a way A can end (`Run`: some run of A), with the same observations. Only `pre` and the permission of `sp` play a part. Its postcondition is not used.

- **Observations** (`Obs`).
  - On return: the pc, a0 and a1, the preserved registers (sp, gp, tp, s0–s11), the event trace, and all of memory except the dead stack (the `sp.stack` bytes below the entry sp).
  - On exit: the exit status and the trace.
  - Caller-saved registers other than a0/a1 may differ, and so may the dead stack.
- **Syscalls.** The environment's choices (how much a `write` accepts, what a `read` returns) are matched through the trace, which records them. This makes the claim trace refinement: B's behaviours are a subset of A's.
- **Aborts.** An exit is an observation. Wherever A aborts, B must abort with the same status after the same events.
- **Where A fails.** `rel` says nothing about B on a state where A faults, steps outside the permission, makes a syscall the model does not admit, or does not terminate. `runs` rules such entry states out: every entry `sp` allows is one where A runs.

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

`Refines.of_lockstep` is the soundness theorem: `ARuns sp A → check … = true → Refines sp A B`, for every `sp`. It covers leaf functions only. It is the base case of paired execution (item 3), whose other cases add pairs of *different* instructions, each with an equivalence obligation.

**Regions** (`lean/NoCompiler/RefineRegion.lean`). A certificate also has regions, `RRegion`. Each pairs an interval of B's code with one of A's, with one entry and one exit each and live sets at both, and stands for a changed interval. Its obligation `RRegion.Ok` is a local refinement under every permission:
- from agreeing entry states where A's run through its interval is safe, B's run through its interval is safe;
- every way B leaves it is matched by a way A does: both at their exits, agreeing on `liveOut`, with ra kept; or both exited with the same status and trace.

The check decides a region's shape: entries inside the intervals, exits outside them, intervals inside the functions' code, and the exit a point of the certificate whose live set `liveOut` covers. The contents are proved separately.

`Refines.of_cert`: `ARuns sp A → check … = true → (∀ r ∈ regions, r.Ok cA cB) → Refines sp A B`. `RRegion.Ok.of_instr` proves the one-instruction case from the two instructions' equivalence on agreeing states (and B's access being A's). Straight-line blocks (item 6) and loops (items 3 and 4) are further ways of proving `Ok`.

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

## Item 5: the tree diff (B)

`nocompiler refine A.elf B.elf FUNC [--func-b NAME] [--namespace NS -o OUT.lean
[--images IMG_A IMG_B] [--bv]]` (`crates/nocompiler/src/treediff.rs`). It
aligns the two functions' words (longest common subsequence; a conditional
branch or a `jal zero` is compared without its offset, so the same branch
with a moved target aligns and becomes a jump pair). Aligned words become
lockstep pairs; the gaps between them become changed intervals, each grown
until it is an `RRegion`:

- every branch of a pair (each side with its own offset) targets a pair or a
  region's entry, or it joins the region;
- a region is non-empty on both sides: a pure insertion or deletion takes in
  a neighbour (the next instruction if it is not a jump, else the previous);
- one entry: nothing outside jumps into the interior (the source joins);
- one exit: nothing inside jumps out other than to the end (the target
  joins);
- no node cut: a region lies inside a block or loop of each tree, or covers
  it whole.

A straight-line region whose two sides, run from equal registers, differ on
a live-out register (random and edge-value tests, in the simulator's ALU)
takes in the next pair while that is a register instruction, and the diff
settles again: `xor a4,a4,a2; sltiu a4,a4,1` against `sub a4,a4,a2; sltiu
a4,a4,1` is one region, not `xor` against `sub` (which differ on a4). If it
cannot grow, the summary says `DIFFERS on <reg>` and its `Ok` becomes a
hypothesis of `refines` (B is likely wrong there).

A `ret` inside a change is refused: a region has one exit. Live sets come
from backward liveness on each side, with `Instr.uses`/`Instr.defs` as in
RefineCongr.lean, x0 always live, and a return's observed registers live;
inside a region (not checked against `uses`) a zeroing idiom (`xor`/`sub rd,
rs, rs`) reads nothing. A pair's set, and a region's live-in and live-out,
are the union of the two sides'. The output: `region<k> : RRegion`, `cert :
Lockstep.Cert` (pairs and regions), and for each straight-line region its two
instruction lists `region<k>_as`/`_bs`. With `--images` (the modules of
`nocompiler export`'s images of A and B) also the proofs, by the automation
below: `region<k>_ok` by `nocompiler_region` (`nocompiler_region_bv` with
`--bv`) for each straight-line region, and `refines {α} (sp : Spec α) (hA :
ARuns sp A) : Refines sp A B` by `nocompiler_refine`, taking A's run and each
structured region's `Ok` as hypotheses (`hA`, `h<k>`). None of it is trusted: the kernel checks the
certificate and every proof.

**Example** (`examples/refine/diff/`, `lean/Examples/Refine/Diff.lean`):

- `sum` with the loop's `add` commuted: 8 pairs and 1 straight-line region;
  the generated `AB.refines` is the whole proof.
- `sum` with `xor t5, t5, t5` inserted in the loop: the loop's `beq` and
  `bne` keep their op and registers but move their targets, so they are jump
  pairs; 8 pairs and 1 straight-line region (A's `add` against C's `xor;
  add`), proved by the generated `AC.refines`.
- `sum` counting down by 2 then up by 1 (`addi a1,a1,-2; addi a0,a0,8; addi
  a1,a1,1` against `addi a1,a1,-1; addi a0,a0,8`): the changed `addi` alone
  differs on a1, so the region grows to 2 against 3 instructions; `AD.refines`.
- `sum` against itself: 9 pairs, no region.

`crates/nocompiler/tests/treediff.rs` checks these numbers and that the
generated Lean is the committed one.

## Unchanged functions (`lean/NoCompiler/RefineReuse.lean`)

A function unchanged between two builds, as relocatable code (the same
`RFunc`, docs/isa/ledger.md), refines itself at function granularity, with no
stepping:
- `RefinesRel.of_code_eq`: code that agrees with A's on A's region refines A
  there;
- `Refines.of_sub_verified`: for two modules holding the function's closure
  unchanged, at one layout, from its `Verified` theorem.

The side conditions are decided by comparing `RFunc`s. The ledger's
`closure` key finds, without Lean, the functions it applies to: on the 7'
artifact's one-line edit, all but 1 of 1235 (the edited function).

## Automation (`lean/NoCompiler/RefineAuto.lean`)

A task's proof is generated. The tree diff (item 5) writes the certificate and, per region, its two instruction sequences. The proof then reads:

```lean
theorem region_0_ok : region_0.Ok cA cB := by nocompiler_region region_0 [as…] [bs…]
theorem refines (hA : ARuns spec cA DA eA) : Refines spec cA DA eA cB DB eB := by
  nocompiler_refine cert [region_0_ok]
```

- `nocompiler_region r as bs` closes the straight-line region `r` with `RRegion.ok_of_seqEquiv` and `seq_equiv` (kernel tier). Its side conditions are decided.
- `nocompiler_region_bv` does the same with `seq_equiv_bv`, so the result is in the bv_decide tier.
- `nocompiler_refine cert [h, …]` applies `Refines.of_cert`: A's run comes from a hypothesis in the context, the kernel decides the check, and `h, …` are the regions' proofs in the certificate's order.

Example: `Examples.Refine.Peephole.Auto.refines'` is the peephole refinement in two lines.

**Jump pairs.** A pair may also be the same branch (or `jal zero`) with a different offset on each side: an insertion or deletion moves branch targets, and the check then requires the two targets to be a pair. So a loop whose body changed stays a lockstep skeleton, and only the changed straight-line pieces are regions. Example (`lean/Examples/Refine/Jump.lean`): `sum` against `sum` with `xor t5, t5, t5` inserted in its loop (B's example C, which the diff currently makes one 6-against-7 region). It is 8 pairs (two of them jump pairs: the `beq` and the `bne`) and one straight-line region (`xor t5; add` against `add`, t5 dead), proved by `nocompiler_region` and `nocompiler_refine` with nothing written by hand. Controls: dropping the pair formed by the `beq`'s targets fails the check, and with t5 live the region is not an equivalence. Not automated yet are regions that are not straight-line equivalences: loops whose relation at the heads is not "the live registers are equal" (plan RA2 in STATUS-C: relational cut points). For those, `RRegion.Ok.of_bigSim` is the proof method.

## Open (plan: STATUS-C)

- **Item 3, paired execution (rest).** Same-shaped loops with relational invariants at the paired heads (by default, the live state is equal), as a way to prove `RRegion.Ok`.
- **Item 6 (B), loads and stores** in straight-line sequences (above: registers only).
- **Item 4, region equivalence.** A differently shaped interval is cut out as a subtree on both sides, with an exit relation (k:1 unrolling, local summaries). Assumptions not derivable from A become explicit, reported preconditions.
- **Frames.** Memory equal outside the dead stack, with different frame layouts in A and B (after A's T2).
- **Calls.**
- **A differential runner** that reports `refuted` with a counterexample.
