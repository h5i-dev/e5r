# memmove regression matrix: results (stopped by owner redirect)

Model executions on chosen inputs, not proofs. The program is
`MemmoveMatrix.lean`, run by `matrix.sh` and summarized by
`summarize_matrix.py` (output in `matrix-summary.txt`).

* **Main matrix, final binary, complete:** every n in 0..488 × 16 src/dst
  residue pairs × up to 7 placements (disjoint below/above, src = dst, forward
  and backward overlap at the nearest and farthest distance with that residue).
  * 48,548 runs, 30,900,622 model steps, **0 failures**. Each case is checked
    byte for byte against memmove of the snapshot over dst±16, src±16 and
    sp−64..sp+16, plus the ABI registers.
  * Changed frame bytes per class (offsets from the caller's sp):
    * n < 16 and all src ≡ dst classes: only the save slots −12..−1.
    * Misaligned forward: −34, −32, −28..−25.
    * Misaligned backward: −22, −20, −16..−13.
  * About 5 min 20 s wall on 16 shards.
* **Boundary set:** completed 2,134 runs with 0 failures in the earlier run, an
  identical checker logic before the control parameters were added (its log was
  overwritten). The final-binary pass was stopped by the owner's redirect.
* **Controls (final binary):** all 6 detected (`matrix-summary.txt`).
