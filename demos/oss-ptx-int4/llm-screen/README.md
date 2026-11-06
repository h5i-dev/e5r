# Pinned LLM INT4 screening

This is a compiler screen, not an accepted equivalence proof or a speedup result.
The retained baseline is the complete upstream translation unit with its real
dispatch and optimized build flags. The bounded-byte candidate was also
execution-tested and timed on the A10G; it did not produce a broad speedup.

| Implementation | Pin / license | Normal route and domain | Finding |
| --- | --- | --- | --- |
| llama.cpp Q4_0 | `67107ac34f62882d8b53ea41ad68010ea635b9be`, MIT | `ggml_get_to_fp32_cuda` / `ggml_get_to_fp16_cuda` select `dequantize_row_q4_0_cuda`, 32 threads, 8 blocks of 32 values per CTA, whole quantization blocks | Byte low/high nibbles are already simple mask/shift instructions. No new packed-half conversion win established. |
| llama.cpp Q4_1 | same | Corresponding Q4_1 normal conversion dispatch | Same nibble findings; minimum offset changes FP arithmetic. |
| llama.cpp Q4_K | same | Corresponding Q4_K normal conversion dispatch, 32 threads per 256-value block | Six-bit scale reconstruction already receives SASS LOP3/LEA fusion. Four high-nibble conversions retain a redundant `0xffff` SASS mask after the shift of a zero-extended byte. |
| llama.cpp Q4_K with CUDA conversion intrinsic | same complete TU, `llama-intrinsic.patch` | Same launch/dispatch/layout. High nibble explicitly uses `__uint2float_rn(static_cast<unsigned>(q[l]) >> 4)` | Same four masks, same registers and static instruction counts. This plausible integer range propagation gap survives this source-level intrinsic. |
| llama.cpp Q4_K with CUDA inline PTX | same complete TU, `llama-inline.patch` | Same dispatch, helper uses `shr.u32` before `__uint2float_rn` | Float output: 107 to 103 non-NOP instructions, 26 registers unchanged, four masks removed. This valid CUDA comparison reaches the direct-edit result. |
| Direct edited llama PTX | exact original generated PTX, `edit.py` | Only the four high-nibble shift/conversion pairs in the float Q4_K entry change | Same 103 instruction count, 26 registers, zero masks. Exploratory candidate; timed below, no accepted proof. |
| Marlin original | `1f25790bdd49fba53106164a24666dade68d7c90`, Apache-2.0 | Complete `marlin_cuda_kernel.cu`, normal `marlin_cuda` shape dispatch, groupsize -1 or 128, FP16 activation/output, FP32 tensor-core accumulation | Already contains inline `lop3.b32` and packed half subtraction/FMA conversion, based on FasterTransformer. This is the existing strong baseline, not a new optimization. |
| Marlin plain CUDA adaptation | same complete TU, `marlin-plain.patch` | Only helper implementation changes to `(a & b) \| c`; static assertion binds the actual LUT | SASS has the same LOP3 counts and register counts in all ten dispatch instances. More constant-move instructions appear. Reproducing original inline PTX is not a new win. |
| FasterTransformer conversion | `df4a7534860137e060e18d2ebf019906120ea204`, file SPDX BSD-3-Clause; repository license retained | `FastInterleavedAndBiasedNumericArrayConverter<half_t,uint4b_t,8>` | Source-only corroboration of existing inline LOP3 plus packed-half arithmetic. Not independently built or measured; Marlin is the compiled derivative baseline. |

Sources: [llama.cpp](https://github.com/ggml-org/llama.cpp/tree/67107ac34f62882d8b53ea41ad68010ea635b9be),
[Marlin](https://github.com/IST-DASLab/marlin/tree/1f25790bdd49fba53106164a24666dade68d7c90),
[FasterTransformer](https://github.com/NVIDIA/FasterTransformer/tree/df4a7534860137e060e18d2ebf019906120ea204).
Implementation source was read for this screen. No reverse-engineering tool
implementation was used to write E5R code.

Q4_0 stores an FP16 scale and 16 bytes: low nibbles produce the first 16
values, high nibbles the next 16, with symmetric zero point 8. Q4_1 stores
FP16 scale/min and 16 bytes, with unsigned nibble times scale plus minimum.
Q4_K stores two FP16 scales, 12 bytes of packed six-bit scales/minima, and
128 nibble bytes. Its dequantization uses FP32 multiply and FMA under the
upstream `-use_fast_math` flags and casts to the selected output type.
There is no assertion here of FP equivalence, NaN behavior, or rounding
preservation for a transformed kernel.

Marlin `Layer.pack` rounds weight/scale using `torch.round`, adds 8, clamps
to [0,15], permutes 16x16 tiles and interleaves nibble order
[0,2,4,6,1,3,5,7], then packs eight nibbles per uint32. Scales have separate
per-group/per-column permutations. The kernel's dequant converts to values
[-8,7] in packed half registers; group scales are multiplied in half, and
the MMA accumulates in float. Complete packing source is frozen below.

`evidence/` retains original source archives with upstream license notices,
uncompressed-content SHA256 in `artifacts.json`, full generated PTX, cubins,
objects, SASS (gzip), exact llama compile-command arrays, ptxas logs, and
per-function instruction/register summaries. CUDA is 13.2.51 targeting sm_86;
the machine reports NVIDIA A10G. The official matching nvdisasm archive hash
is in `environment.txt`. Large preprocessed intermediates remain at
`/mnt/scratch/e5r-oss-ptx/int4/llm/artifacts`.

The normal llama compile command came from CMake Release with CUDA enabled
and architecture 86, then received only `--keep`, `--keep-dir`, and
`-Xptxas=-v`. Marlin uses `-O3 -std=c++17 --expt-relaxed-constexpr
-arch=sm_86 -Xptxas=-v`; relaxed constexpr is required by its existing host
`ceildiv` calls in device code. An initial attempt without it failed, then
the required flag was added; source was not weakened to compile.

For the float Q4_K entry, the normal baseline and intrinsic adaptation use
26 registers, zero stack and spills, and 107 static non-NOP instructions.
FP16 and BF16 entries use 25 registers, zero stack and spills, and 116 such
instructions. Static counts include branch/exit and are not runtime timing.
The scope does not cover MMQ/matvec/attention paths, complete model inference,
or all valid representations of exceptional FP scale values.

The direct edit zero extends the original unsigned-byte register to u32,
shifts by four in u32, then converts that u32 integer to float. It removes
four masks in the float entry without changing registers or introducing
spills. The strong inline-PTX CUDA adaptation gets the same result. For half
and BF16 the inline adaptation reduces 116 to 113 instructions but increases
registers from 25 to 26; the direct edit intentionally leaves these alone.
This establishes a static instruction gap in the specified normal compiler
route. Inline PTX is valid CUDA, and no universal limitation of CUDA is claimed.

Rebuild serially without GPU execution using `python3 replay.py --scratch
/mnt/scratch/e5r-oss-ptx/int4/llm-replay --nvdisasm /path/to/nvdisasm`.
The script checks out the exact pins and compiles complete TUs. Then run
`python3 edit.py ORIGINAL_CONVERT.ptx EDITED_CONVERT.ptx` and assemble with
`ptxas -O3 -arch=sm_86 -v EDITED_CONVERT.ptx -o edited.cubin`.
The edit script checks the four source registers' byte-extension dataflow.

`benchmark.py` loads the complete cubins through the CUDA driver and launches
the exact two-pointer Q4_K float entry with its upstream grid/block geometry.
The input repeats a 144-byte block with finite binary scales 0.5/0.25 and
nibble/scale boundary patterns. Every output element matches a separate CPU
decoder, every variant matches normal bytes, and 64-byte output canaries
survive at all four sizes. This is execution evidence on this finite input,
not equivalence over arbitrary scale bit patterns.

The benchmark acquired `/mnt/scratch/e5r-gpu-benchmark.lock` exclusively and
refused existing foreign compute processes. It preallocated all buffers,
excluded transfers and graph construction, warmed each 32-launch graph five
times, and recorded 15 CUDA event samples per variant with rotating order.
Raw samples, output hashes and metadata are in `evidence/benchmark.json`.

| Quantization blocks | Output values | Normal median us | Edited median us | Normal / edited |
| ---: | ---: | ---: | ---: | ---: |
| 16 | 4096 | 1.312 | 1.312 | 1.000 |
| 256 | 65536 | 1.662 | 1.632 | 1.018 |
| 4096 | 1048576 | 5.920 | 6.176 | 0.959 |
| 65536 | 16777216 | 165.376 | 165.152 | 1.001 |

These are repeated-buffer measurements; the 64 MiB output case exceeds L2.
The inline-PTX CUDA control closely tracks the edited kernel. The candidate
is slower at one size and the largest-case improvement is below 0.2%, so the
screen does not establish a useful speedup or an end-to-end inference win.
No statistical significance or multi-session stability claim is made.

Remaining gates are E5R semantic support, an accepted relational proof for
the exact hashes/domain, adversarial/random validation over the intended
domain, and a useful performance result. The candidate remains exploratory.
