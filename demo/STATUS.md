# Status (work in progress, not finished)

Done and checked:
- demo/src: one C source each for sum and cobs_decode; demo/build.sh builds A (clang -O2 rv64gc) and B (e5r cc -O2); committed ELFs in demo/elf.
- cobs_decode tested against a reference under qemu on 20,000 buffers plus 2,000 round trips, on both A and B (demo/test/cobs_test.py).
- lean/E5R/Auto.lean: e5r_auto, the tree-driven cut-point symbolic executor (B side).
- lean/E5R/Ext/Rvc.lean: the RVC extension (decodeC, CCode, execC, StepC/ReachC/VerifiedC) and e5r_auto_c, which takes its cut points from the user.
- decodeC agrees with llvm-mc on all 49,152 16-bit words (demo/test/rvc_decode.py); execC agrees with qemu on 3,000 cobs_decode runs (demo/test/rvc_exec.py).
- Demo/SumB.lean and Demo/SumA.lean: sum proved on both builds, no sorry, about 3.5 s each; the per-function proofs are the same size.

Not done:
- Demo/CobsB.lean / CobsA.lean: e5r_auto completes every path, but memory then grows past 5–7 GB, apparently while the final proof term is instantiated and kernel-checked. The cause is still being bisected: memory stays flat with trivial invariants, and the copy-loop invariant (ghosts p cnt dst L c e) alone is enough to trigger it. Next ideas: put each cut-point body in its own auxiliary theorem (mkAuxTheorem), and shrink the passes in e5r_vnorm. The COBS VCs are still to be proved with the lemmas in Demo/CobsSpec.lean.
- Audit entries (demo/tools/Audit.demo-additions.lean.txt), mutation controls (in scripts/check-proof-controls.sh, untested), demo/tools/count.py, demo/README.md. demo/run.sh is drafted but untested.
