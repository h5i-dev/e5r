/* Original e5r fixture, Apache-2.0. No runtime, no syscalls. */
.option norvc
.option norelax
.section .text
.global _start, done
_start:
  lui t0, 2
  lw a0, 0(t0)
  addi a0, a0, 7
  addi t1, zero, 100
  bltu a0, t1, store
  addi a0, zero, 100
store:
  sw a0, 4(t0)
done:
  jal zero, done
.section .data
.global input, output
input: .word 0
output: .word 0xdeadbeef
