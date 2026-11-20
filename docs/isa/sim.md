# The simulated performance oracle: `nocompiler sim`

Item 8 of the refinement plan (`spec-v1-refine.md`): a refinement task
claims B is faster than A, and there is no RV64 hardware on the development
machine and no timing in qemu. `nocompiler sim` runs a statically linked
profile binary and reports two numbers, both labelled **simulated**:

* **dynamic instruction counts**, exact: the whole run and, per function, its
  own instructions and inclusive of its callees;
* **cycles**, from a model of a named single-issue in-order core (below):
  approximate, and only as good as the model.

```bash
nocompiler sim prog.elf [--stdin IN] [--function NAME] [--json] [--fuel N]
```

The program's own output goes to standard output and the report to standard
error. The exit status is the program's, or 3 if it faulted (a misaligned
access or jump, an instruction outside the profile, an unmodelled syscall)
or ran out of fuel. The implementation is `crates/nocompiler/src/sim.rs`.

```text
$ nocompiler sim cobs_test.elf --stdin in.bin --function cobs_decode
model        inorder5 (single-issue in-order 5-stage, Rocket/U54-style; simulated)
exit         0
instructions 6150
cycles       6810 (simulated)
branches     1618 (28 mispredicted)
loads        1013  stores 466  ecalls 14

function                                    calls   instr (incl)  cycles (incl)  instr (own) cycles (own)
cobs_decode                                     3           5949           6561         5949         6561
```

(The demo's COBS test driver, `examples/demo/src/cobs_{,test_main}.c`, on three
1000-byte records.)

## What is executed

The instructions are the profile's (RV64IM + Zba + Zbb), with the semantics
of `lean/NoCompiler/Machine.lean`: a misaligned load, store or jump target
stops the run, as it has no successor there. The environment is
`lean/NoCompiler/Env.lean`'s: `write` (fd 1 and 2 to standard output; the
whole buffer is written), `read` (from `--stdin`), `exit` and `exit_group`.
Every allocated section of the ELF is loaded at its address; the stack
starts below 0x7fff_ff00_0000.

Attribution: an instruction counts for the function whose symbol covers its
pc. A call (`jal ra` or `jalr ra`) to a function entry opens an activation,
the matching return closes it; a tail call hands the activation over.
Inclusive counts of a recursive function count its outermost activation
only.

## The timing model: `inorder5`

A single-issue, in-order, five-stage RV64 pipeline in the style of Rocket
and the SiFive U54. Each instruction issues one cycle after the previous
one, or later if a source register is not ready; the result is ready
`latency` cycles after issue.

| parameter | value | |
| --- | --- | --- |
| base | 1 cycle per instruction | |
| load-to-use latency | 2 | a use in the next instruction waits 1 cycle |
| multiply (`mul`, `mulh*`, `mulw`) | 3, pipelined | |
| divide and remainder, 64-bit | 65, not pipelined | the divider is busy until the result |
| divide and remainder, 32-bit (`*w`) | 33, not pipelined | |
| conditional branches | 2-bit counters, 512 entries, indexed by pc / 4 | a mispredict costs 3 cycles |
| returns (`jalr zero, 0(ra)`) | 6-entry return-address stack | a miss costs 3 cycles |
| other `jalr` (calls, tail calls) | last target per pc | a miss costs 3 cycles |
| `jal` | predicted | |
| `ecall` | 1 cycle | the kernel's time is not modelled |

**What the numbers are not.** The parameters are the model's definition,
in the range published for in-order RV64 cores of this class. They are not
fitted to, or validated against, any hardware. Caches and memory latency are
not modelled: every load hits. The model is for comparing two versions of
the same function on the same input (A against B), where these effects are
mostly common to both, not for predicting absolute run times. Every report
says "simulated".

## How it is checked (`crates/nocompiler/tests/sim.rs`)

Against qemu-riscv64 8.0 or later (the test skips, loudly, with an older
qemu):

* **semantics**: random programs over every instruction of the profile (the
  generator of tests/semantics.rs) dump all registers and a scratch area; the
  simulator's dump is qemu's, byte for byte (200 programs by default; 400
  checked in an Ubuntu 24.04 container with qemu 8.2.2);
* **instruction counts**: on 20 of those programs and on the COBS driver,
  the simulator's count is the number of instructions qemu executes
  (`-one-insn-per-tb -d exec,nochain`: one log line per instruction);
* **whole programs**: the COBS test driver on 40 random inputs gives qemu's
  output and exit status.

qemu 7.2 gets `ctzw` wrong on an input whose low 32 bits are zero: it gives
the 64-bit count (63 for 1<<63) where the RISC-V specification, the Lean
semantics and qemu 8.2 give 32. The simulator gives 32.

The cycle model has no oracle. That is why it is labelled simulated, and
why the instruction counts, which have one, are always reported next to it.
