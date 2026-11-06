# bitsandbytes 4-bit CUDA screen

Pinned upstream: [bitsandbytes a616886cacf86701514f0cb1d6be760f967481c0](https://github.com/bitsandbytes-foundation/bitsandbytes/tree/a616886cacf86701514f0cb1d6be760f967481c0),
2026-10-27, MIT; see `LICENSE.bitsandbytes`. This screen reads the upstream CUDA
implementation for provenance and compiler evidence. No E5R implementation is
derived from another reverse engineering tool.

`result.json` freezes source hashes, exact commands, compiler/disassembler
versions, full-TU PTX/cubin hashes, and six ordinary upstream kernel entries.
Each retained `.ptx` entry is copied unchanged from the complete, unchanged
`csrc/kernels.cu` translation unit. Each `.sass` and `.resources` comes from
the full-TU cubin. They are generated evidence, not handwritten candidates.
The source and larger build files live in
`/mnt/scratch/e5r-oss-ptx/int4/bitsandbytes`.

The CUDA API's `dequantize_4bit` dispatch in
`bitsandbytes/backends/cuda/ops.py` calls the corresponding C wrapper in
`csrc/pythonInterface.cpp`; `dequantizeBlockwise` in `csrc/ops.cu` launches
`kDequantizeBlockwise<T,512,64,8,FP4/NF4>` with 64 threads and
`ceil(n/1024)` blocks. This is the normal standalone dequantization path,
with its CUB warp-transpose load/store implementation intact. A fused
matmul/GEMV has different observable work and is a separate application
comparator; this screen makes no inference about its speed.

Frozen semantics and domain:

- Packed bytes are contiguous. The high nibble produces the earlier output;
  the low nibble produces the next output. Odd `n` is predicated at the store.
  This is FP4/NF4 codebook decoding, not uniform signed INT4 arithmetic.
- Output has `n` elements and dtype FP16, BF16, or FP32. The public block sizes
  are 32, 64, 128, 256, 512, 1024, 2048, and 4096 output elements. `ops.cu`
  passes half that block size to the packed-byte kernel. The six retained
  variants use runtime `n` and block size, with no favorable shape specialization.
- NF4 uses the exact 16-entry FP32 table in `csrc/kernels.cu`. FP4 uses its
  exact eight-entry nonnegative FP32 magnitude table and nibble bit3 as sign.
  Do not substitute a hardware FP4 format or a freshly rounded decimal table.
- Dequantization multiplies the table result by an FP32 block scale, then
  converts to the output dtype. `--use_fast_math` is upstream CMake's ordinary
  option: the emitted FP32 multiply/subtract operations use FTZ, and FP16/BF16
  conversions use round-to-nearest. FP4 first multiplies by its computed
  sign, so negative zero is observable. A rewrite must preserve this order,
  exact table bits, signed zero, and output rounding.
- Nested scale decompression, public Python output allocation/shape/transpose
  behavior, zero-length host behavior, aliasing, and input validation remain
  responsibilities of the unchanged host API. No claim covers malformed or
  out-of-range raw C-ABI calls. No GPU execution was performed in this screen.

| Ordinary full-TU kernel | Static SASS instructions | Registers | Shared bytes | Stack/local bytes |
| --- | ---: | ---: | ---: | ---: |
| FP4 to FP32 | 480 | 48 | 4768 | 0/0 |
| NF4 to FP32 | 376 | 48 | 4768 | 0/0 |
| FP4 to FP16 | 536 | 48 | 2656 | 0/0 |
| NF4 to FP16 | 424 | 48 | 2656 | 0/0 |
| FP4 to BF16 | 536 | 48 | 2656 | 0/0 |
| NF4 to BF16 | 424 | 48 | 2656 | 0/0 |

Static counts include tail, loop, control, and padding instructions. They are
not dynamic execution counts or performance measurements. All six variants
have zero local memory and zero stack allocation. No spill reduction is
available in this observed baseline.

The bounded integer NF4 unpack is already lowered to shifts, masks/LOP3, and
scaled LUT addressing. This screen has no evidence of a useful integer-only
compiler miss there. The FP4 path has a concrete remaining lead: SASS retains
16 integer-to-FP32 conversions (eight `I2F.U16`, eight `I2FP.F32.U32`),
16 `FADD.FTZ`, and 32 `FMUL.FTZ` per static unrolled body. Sixteen multiplies
apply sign; sixteen apply scale. Replacing sign construction/application by
bitwise sign insertion for the known finite magnitude table might remove
work. This is a hypothesis pending a direct PTX candidate, exact correctness
proof, strongest matching CUDA comparator, and fair GPU timing. The necessary
finite-table/signed-zero argument is beyond an integer-unpack-only theorem.
No accepted proof, optimized kernel, or speedup is claimed by this screen.
Existing Marlin LOP3/half2 techniques are not a novelty claim here.

Reproduce with CUDA 13.2.51 and the matching cuobjdump/nvdisasm binaries:

```sh
mkdir -p /mnt/scratch/e5r-oss-ptx/int4/bitsandbytes
git clone https://github.com/bitsandbytes-foundation/bitsandbytes.git /mnt/scratch/e5r-oss-ptx/int4/bitsandbytes/upstream
git -C /mnt/scratch/e5r-oss-ptx/int4/bitsandbytes/upstream checkout a616886cacf86701514f0cb1d6be760f967481c0
python3 demos/oss-ptx-int4/bitsandbytes-screen/screen.py
```

The script uses one compiler job, no GPU, and no settings changes. Paths to
the locally available NVIDIA disassemblers are at the top of `screen.py`.
