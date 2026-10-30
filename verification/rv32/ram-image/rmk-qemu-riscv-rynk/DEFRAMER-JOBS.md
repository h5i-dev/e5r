# Deframer and session runner jobs (CONDITIONAL; no safety claim)

These jobs check main's Deframer and session proofs (`Projects/rmk/Deframer/*`, support-lean4
through `5661ea9`) on the runner image. None of them claims RMK, the deframer or the session
is safe. **Every result here takes memmove's `CopyContract` as an explicit hypothesis.** The
peer's `Memmove.contractAll` (isa-review `89ab0a6`) now covers every memmove case, but the
bridge from its `PreM`/`PostF` to `CopyContract` is main's pending work. Until a job checks
that bridge, nothing here is discharged. **`SessionSafe` is not proved**: the dispatch/send
path, the UART read future, the executor between polls, other tasks and interrupts are open
(`verification/rv32/rmk-audit/SESSION-BOUNDARY.md`).

| Job | Headline | Hypotheses still open |
| --- | --- | --- |
| `jobs/rmk/rmk-deframer-conditional.json` | `E5R.RmkDeframer.conditional`: `(CopyContract → Tail ∧ Park ∧ Unpark) ∧ (CopyContract → CobsReportContract → Next)` | `CopyContract`, `CobsReportContract` |
| `jobs/rmk/rmk-deframer-cobs-discharged.json` | `E5R.RmkDeframerCobs.conditional_copy`: `CopyContract → Tail ∧ Park ∧ Unpark ∧ Next` | `CopyContract` (COBS: `E5R.Rmk.Cobs.cobs_report_contract`, proved) |
| `jobs/rmk/rmk-session-conditional.json` | `Session.recv_step`, `Session.unpark_step`, `E5R.RmkSession.{recv_conditional, unpark_conditional, unpark_then_recv}`; `next_from_copy`; both COBS discharges (main's `cobs_report`, mine); `reach_on_runs`/`reach_avoids` (main), `Closure.*` (mine) | `CopyContract`; `Quiet` is a precondition of every step |

All jobs use the runner's image and board: `img_eq` and `board_eq` relate them to
`RamElf.imageOf` of the generated packed file and to the QEMU virt board at its rwBase. The
symbols are pinned to their addresses: `tail`, `park_pending`, `unpark_pending`, `next`, both
`decode_in_place` functions, and `from_decoded` for the session. The runner checks every
module from source in job order: an import must be a module checked earlier in the same run,
so no olean from outside the run is loaded.

## Official runs (main's committed files; no copies, no runner policy change)

Main inlined `csr_chain` in `357b7ba`, which removed the policy block. Branch `185a20a`;
receipts are `*.result.json` and `official-runs.txt`.

| Job | Result | Seconds |
| --- | --- | --- |
| rmk-deframer-conditional | proved | 635 |
| rmk-deframer-cobs-discharged | proved | 913 |
| rmk-session-conditional | proved (`--resume`) | 313 |

The session job's first run ended `failed` (exit 10, 476 s). The first error was in MY
wrapper `Projects/ramimage/Session.lean`: `B`/`img` were ambiguous after `open E5R.Rmk`. That
was a wrapper error, not a rejection of main's proofs. After the fix the job proved. Every
audited theorem's axioms are within {propext, Classical.choice, Quot.sound}.

## Negative controls, on UNEXPANDED copies of main's files

`scripts/test-rmk-deframer-job.py E5R_VERIFY JOB --official`. A mutation counts as rejected
only if the run is `failed` and its first error is inside a theorem of the copied chain. An
import or unknown-identifier error does not count. A tool error is exit 13.

* `rmk-deframer-conditional`: 8/8 as stated (`deframer-conditional-controls-official.txt`):

  | Mutation | Rejected in |
  | --- | --- |
  | none (control) | proved |
  | `tailStack` without memmove's 48-byte frame | `Tail.tail_from_copy` |
  | `Inv` admitting filled = len + 1 (panic bound) | `TailNoCopy.nocopy` |
  | `TailPost` filled′ off by one | `TailNoCopy.nocopy` |
  | `NextPost` Some(k) with 3 < k | `NextRet.ret_post` |
  | ELF 0x8001d58e `bltu` → `bgeu` (tail's bound check) | its instruction fact `f8001d58e` |
  | missing module | `error` (tool) |

  Probe: `CobsPost.ok := True` breaks `Wrap.wrap`, so `next` depends on the COBS length bound.
* `rmk-session-conditional`: 11/11 as stated (`session-conditional-controls-official.txt`). The
  same eight as above, plus three session mutations:

  | Mutation | Rejected in |
  | --- | --- |
  | `RecvOut`: message length ≥ 4 (was 3) | `Session.recv_step` |
  | `RecvW`: stack window 0x6c bytes (was 0x70) | `Session.recv_step` |
  | `UnparkAt`: parked ≤ 488 + 1 | `SessionLoop.unpark_step` |

  Probe as above.

## Earlier runs on macro-expanded copies (kept, superseded)

Before `357b7ba`, results came from copies with `csr_chain` expanded:
* conditional: controls 7/7 (`deframer-conditional-controls.txt`);
* COBS-discharged: proved in 516 s, with a bundle (746 s) and `recheck.sh` (432 s) OK
  (`deframer-discharged-bundle/`).

## Next: the discharged job

`scripts/make-rmk-discharged-job.py BRIDGE_MODULE BRIDGE_THEOREM` writes
`Projects/ramimage/SessionDischarged.lean` and `jobs/rmk/rmk-session-discharged.json`. The
wrapper applies main's bridge (`theorem copy : CopyContract := BRIDGE_THEOREM`) and states
the four Deframer contracts, `recv`, `unpark` and `unpark_then_recv` with no hypothesis. The
job's module list is the wrapper's import closure in dependency order, so it includes the peer's
memmove chain. The conditional jobs and receipts above stay unchanged.
