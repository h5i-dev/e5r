; memset in structured assembly (docs/isa/asm.md), written by hand: no
; compiler. `nocompiler asm` assembles it into examples/elf/memset.elf and
; writes the proof skeleton; lean/Examples/Memset.lean is that skeleton with
; the verification conditions proved.
;
;   void *memset(void *p, int c, u64 n): the n bytes at p become c's low byte.
#import Examples.MemsetSpec
#namespace Examples.Memset

memset:
  #spec spec
  #intro ⟨p, c, n⟩ s he ⟨ha0, ha1, ha2, hn⟩
  mv a3, a0                 ; a3: the next byte to write
  block @done {
    beqz a2, @done          ; n = 0: nothing to write
    loop @fill {
      ; after k bytes: a3 = p + k, a2 = n - k, the first k bytes are c
      #inv fun u => ∃ k L, u.reg 13 = p + BitVec.ofNat 64 k ∧ u.reg 12 = BitVec.ofNat 64 (n - k) ∧
      #    k < n ∧ u.reg 10 = p ∧ u.reg 11 = c ∧ readBytes u.mem p n = L ∧
      #    L.take k = List.replicate k (BitVec.ofNat 8 c.toNat)
      #measure fun u => (u.reg 12).toNat
      sb a1, 0(a3)
      addi a3, a3, 1
      addi a2, a2, -1
      bnez a2, @fill
    end loop
  end block
  ret                       ; a0 = p, untouched

; A test driver for examples/asm/test.py (not proved): reads a byte c and a
; payload from stdin into the buffer at 0x13000, sets the payload to c with
; memset, and writes the buffer and the 16 bytes after it to stdout.
_start:
  lui s0, 19                ; s0 = 0x13000
  li a0, 0
  mv a1, s0
  li a2, 2047
  li a7, 63                 ; read(0, buf, 2047)
  ecall
  mv s1, a0
  lbu a1, 0(s0)
  addi a0, s0, 1
  addi a2, s1, -1
  call memset               ; memset(buf + 1, buf[0], len - 1)
  li a0, 1
  mv a1, s0
  addi a2, s1, 16
  li a7, 64                 ; write(1, buf, len + 16)
  ecall
  li a0, 0
  li a7, 93                 ; exit(0)
  ecall
  ret

bss .bss 0x13000 4096 rw
