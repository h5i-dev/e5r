# Hybrid proofs: abstract interpretation + directly proved machine-code summaries

Original e5r work, Apache-2.0. Everything here is stated over the unchanged concrete semantics
(`Theories/Platform.lean`: `Step`, `Reach`, `Escapes`, `Event`) and proves the same property as
`E5R.AI.check_sound`: no reachable machine can escape, and every device write satisfies the
configuration's `allow` list.

| File | What it proves |
| --- | --- |
| `Theories/Hybrid/Basic.lean` | Masked runs (`MRun`: deterministic steps with `mstatus.MIE = 0`), `Summary`, `hybrid_sound` (closed invariant + summaries), `seq_sound`. |
| `Theories/Hybrid/Wrap.lean` | The branch-free wrap rustc emits (`addi +1; addi -4; seqz; addi -1; and`) computes `next h` for `h < 4`. |
| `Theories/Hybrid/AIBridge.lean` | Masked runs as the checker's hybrid obligations: `regionOf` (a `Region` for delegated nodes, d6ae986), `safeStep_of_mrun` (`SumSound` for summaries, 34fadf2). |
| `Ring.lean` | Firmware (ELF 1d8e45ce…): the Embassy channel ring-head update 0x20010698..0x200106ae as a masked run of 8 instructions, checked against the image. |
| `RingAI.lean` | The same region between checker states: `enterOk`/`post`, `adapter`, `spec : SumSpec` and `spec_sound` (for `check_sound_hybrid`'s `hsums`), `hentry_of` (for delegation). |
| `demo/ring.rs`, `demo/Proof.lean` | Real binary (sha256 2f43781c…): boot-to-store region proved directly, the rest by the checker; `demo_safe` via `seq_sound`. |
| `demo/ring_loop.rs`, `demo/LoopProof.lean` | Real binary (sha256 bb337c3f…): the checker covers the loop, the wrap-and-store region (run every iteration) is delegated; `loop_safe` via `check_sound_hybrid`. |
| `demo/LoopControls.lean` | Kernel refutations: a false postcondition, a weakened precondition (the real binary stores 5 from head 4), and an unmasked interrupt obligation are false. |
| `test_controls.py` | Ten mutations, each required to fail in the expected declaration for the expected reason (REJECTED vs ELAB). |

Neither demo binary can be proved by abstract interpretation alone: the analyzer reports a possible
pwmcmp1 write of 132 (`results/ai-alone-*.txt`). The summary supplies the relational fact the
non-relational domain loses (`a2 = a1 - 4` across `seqz`).

## Commands (from `verification/rv32`)

```sh
# Each job: build the binary with the pinned toolchain, export the image, check every module from
# source with the pinned Lean, replay with leanchecker, audit axioms.
../../target/release/e5r-verify check Projects/hifive1/hybrid/jobs/hybrid-ringhead-firmware.json --out build/results/hybrid-ringhead-firmware.json
../../target/release/e5r-verify check Projects/hifive1/hybrid/jobs/hybrid-ring-demo.json --out build/results/hybrid-ring-demo.json
../../target/release/e5r-verify check Projects/hifive1/hybrid/jobs/hybrid-ring-loop-demo.json --out build/results/hybrid-ring-loop-demo.json
python3 Projects/hifive1/hybrid/test_controls.py          # needs the modules' .olean files (after the jobs)
# Untrusted certificate producers (outputs are committed, the kernel checks them):
lake env lean --run Projects/hifive1/hybrid/demo/AnalyzeDemo.lean Projects/hifive1/hybrid/demo/Cert.lean
lake env lean --run Projects/hifive1/hybrid/demo/BuildLoopCert.lean Projects/hifive1/hybrid/demo/LoopCert.lean
```

The job files are under `Projects/hifive1/hybrid/jobs/`, not `jobs/`, so CI's `jobs/*.json` loop does
not run them until the owner moves them.

## Limits

- The firmware theorem is not claimed: the firmware certificate still has other possible-fault sites
  (nullable saved channel pointer 0x2001063c, sampler 0x20010438, waker 0x200108be). The ring-head
  summary is ready to be used there (`RingAI.spec`, `spec_sound`).
- Summaries must be masked (MIE = 0 in the precondition, proved preserved). Unmasked regions need
  `Region` with `MainInv` at interruptible machines; not done here.
- `enterOk` needs `s1` (the channel) to be one exact address and the head in 0..3 in the abstract
  entry state; the head bound must be kept by the analyzer (the summary's `post` re-establishes it in
  the head word).
