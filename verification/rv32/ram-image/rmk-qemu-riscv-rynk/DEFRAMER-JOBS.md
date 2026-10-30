# Deframer runner jobs (CONDITIONAL; no safety claim)

These jobs check main's Deframer proofs (`Projects/rmk/Deframer/*`, from support-lean4
`6a6e5d6`) on the runner image. None of them claims RMK or the deframer is safe:
**`CopyContract` (memmove) is still open.** That covers the backward and misaligned memmove
paths.

| Job | Headline theorem | Hypotheses still open |
| --- | --- | --- |
| `jobs/rmk/rmk-deframer-conditional.json` | `E5R.RmkDeframer.conditional`: `(CopyContract → Tail ∧ Park ∧ Unpark contracts) ∧ (CopyContract → CobsReportContract → NextContract)` | `CopyContract`, `CobsReportContract` |
| `jobs/rmk/rmk-deframer-cobs-discharged.json` | `E5R.RmkDeframerCobs.conditional_copy`: `CopyContract → Tail ∧ Park ∧ Unpark ∧ Next contracts` | `CopyContract` only. `CobsReportContract` is the theorem `E5R.Rmk.Cobs.cobs_report_contract` (Projects/rmk/Cobs/Bridge.lean), proved from the machine-code contract of `decode_in_place_report`. |

Both jobs use the runner's image and board. `img_eq` and `board_eq` relate them to
`RamElf.imageOf` of the generated packed file and to the QEMU virt board at its rwBase.
The symbols `tail`, `park_pending`, `unpark_pending`, `next`, `decode_in_place` and
`decode_in_place_report` are pinned to their addresses.

**Status: runner policy blocks both.** Main's `NextExit.lean` defines `macro "csr_chain"`,
and the runner forbids `macro` in any checked module. Main has been asked to inline it.
Until then, every result below comes from mechanically produced copies with that macro
expanded to its own right-hand side (`scripts/test-rmk-deframer-job.py`,
`build/testjobs/defmut/`). The official job files themselves stop with `error`.

On the expanded copies:
* **Conditional job:** baseline `proved`. Controls 7/7, transcript in
  `deframer-conditional-controls.txt`:

  | Mutation | Rejected in |
  | --- | --- |
  | `tailStack` without memmove's 48-byte frame | `Tail.tail_from_copy` |
  | `Inv` admitting filled = len + 1 (panic bound) | `TailNoCopy.nocopy` |
  | `TailPost` filled′ off by one | `TailNoCopy.nocopy` |
  | `NextPost` Some(k) with 3 < k | `NextRet.ret_post` |
  | ELF 0x8001d58e `bltu` → `bgeu` (tail's bound check) | its instruction fact |
  | missing module | `error` (tool) |

  Probe: with `CobsPost.ok := True`, `Wrap.wrap` no longer checks. `next` relies on the
  COBS decoded-length bound, which the bridge supplies.
* **COBS-discharged job:** `proved` (516 s). `e5r-verify bundle` took 746 s and
  `recheck.sh` 432 s; the packing check passed and the 8 theorems recheck with exactly the
  recorded axioms (`deframer-discharged-bundle/`).
