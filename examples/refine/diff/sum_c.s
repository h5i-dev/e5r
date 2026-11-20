func sum                ; 0x11190, L2
  addi a2, zero, 0
  block $b0
    beq a1, zero, $b0
    loop $l1        ; head 0x11198
      ld a3, 0(a0)
      xor t5, t5, t5
      add a2, a3, a2
      addi a1, a1, -1
      addi a0, a0, 8
      bne a1, zero, $l1
    end
  end
  addi a0, a2, 0
  ret

func _start
  addi a7, zero, 93
  ecall
  ret
