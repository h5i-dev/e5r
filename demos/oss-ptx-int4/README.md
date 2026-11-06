# OSS low-bit PTX optimization report

No accepted whole-kernel optimization win was established. The concrete
bitsandbytes FP4 direct edit removes 56 static SASS instructions, but a strong
CUDA bitcast control reaches the same counts. Actual A10G measurements show
localized gains around 4–5% and essentially no gain at the largest size; the
predeclared adjacent-size performance criterion was not met. Whole-kernel
proof remains unaccepted because of frontend/semantic gaps.

| Artifact | Concrete result | Proof / measurement limits |
| --- | --- | --- |
| [FP4 sign insertion](fp4-sign/README.md) | Two direct-edit versions, full-TU original/control/edited artifacts, 408 adversarial configurations per validation session, two tightened-edit timing sessions with 48 configurations each | Exact finite-table/sign and scale lemmas pass Lean kernel reduction and axiom audit; **no whole-kernel direct proof**. Raw samples and exporter failures retained. |
| [llama.cpp / Marlin](llm-screen/README.md) | Preserved completed screen and Q4_K GPU run from the preceding workers; Q4_K 107→103 instructions, 26 registers; mixed timing ratios | No useful broad speedup and no accepted proof. Marlin already implements the LOP3/half2 technique. |
| [bitsandbytes initial screen](bitsandbytes-screen/README.md) | Preserved pinned upstream normal dispatch, six kernel variants and original emitted PTX/SASS | Screen metadata describes that earlier stage; subsequent FP4 experiments are in their own directory. |
| [Parquet pivot](parquet-screen/README.md) | Pinned real cuDF decoder, source/license, normal configure and unchanged-TU build attempts | Incomplete screen: dependency/toolchain failures; no generated normal PTX, direct edit, GPU result or proof. Existing source already uses funnelshift/guarded fast loads. |

`ledger.json` separates measured candidate families, local proofs, source/compiler
screens and accepted results. Dtype variants and two FP4 versions are not
counted as distinct successful kernels. This task does not claim to fulfill
the older roughly-50-kernel expansion request; the current INT4 priority
superseded that breadth.

All existing worktree changes outside this directory were retained. The earlier
screen workers' results are attributed as inherited artifacts; their compilation
was not repeated unnecessarily. Their retained PTX/SASS hashes were checked.
No reverse-engineering tool implementation was used to write E5R code. Original
OSS implementation source and its licenses are retained for provenance.

The useful result is a measured compiler opportunity in a specified ordinary
nvcc route, together with a source-level implementation, local semantic evidence,
and clear reasons it does not qualify as the requested verified GPU speedup.
No universal limitation of CUDA, new Marlin technique, end-to-end inference
improvement, or verified SASS execution is asserted.
