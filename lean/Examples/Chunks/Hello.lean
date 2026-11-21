/-
Examples/Hello.lean on the chunk image (see Examples/Chunks/SumB.lean), as follows.

Functions that talk to the kernel, from examples/hello.c as clang -O2
compiled them into examples/elf/hello.elf.

`long write_all(long fd, const char *buf, u64 n)`:

    11164  addi a3, a0, 0            fd
    11168  addi a7, zero, 64         SYS_write
           block
             loop
    1116c      beq  a2, zero, 0x11188  nothing left: return 0
    11170      addi a0, a3, 0
    11174      ecall                   r = write(fd, buf, n)
    11178      add  a1, a1, a0         buf += r
    1117c      sub  a2, a2, a0         n -= r
    11180      bge  a0, zero, 0x1116c  r >= 0: again
    11184    jalr zero, 0(ra)          r < 0: return it
    11188  addi a0, zero, 0
    1118c  jalr zero, 0(ra)

The kernel may accept fewer bytes than asked (environment.md), so the loop
invariant, after k bytes, is that the `write` events added to the trace hold
exactly the first k bytes of the buffer. `write_all_verified`: on success
the events hold the whole buffer and a0 = 0; on an error they hold a prefix
and the error is returned. It terminates because every write accepts at
least one byte.

`void hello(void)` passes the 11-byte message in `.rodata` to `write_all`
and exits with 1 on an error, 0 otherwise. `hello_verified` uses
`write_all_verified` for the call and `Segment.Loaded` for the message: it
never returns, writes exactly a prefix of the message to fd 1 and exits, and
the prefix is the whole message exactly when the status is 0.

Both are proved by `nocompiler_auto` (calls, syscalls, frames): what is
written by hand is the loop invariant, the witnesses of the existentials in
the specification, and the facts about the message.
-/
import Examples.Chunks.HelloImage
import NoCompiler.Auto

namespace Examples.Chunks.Hello
open NoCompiler Examples.Chunks.HelloImage

/-- The logical arguments of `write_all`. -/
structure Args where
  fd : Word
  buf : Word
  n : Nat

/-- How a run of `write_all` that has written `k` bytes so far ends: done, or
    an error from the kernel. -/
def Outcome (n k : Nat) (r : Word) : Prop :=
  (k = n ∧ r = 0) ∨ ∃ e, 1 ≤ e ∧ e ≤ 4095 ∧ r = -(BitVec.ofNat 64 e)

/-- `write_all`: a0 = fd, a1 = buf, a2 = n. It may read the buffer and
    nothing else, and uses no stack. -/
def spec : Spec Args where
  pre := fun ⟨fd, buf, n⟩ s =>
    s.reg Reg.a0 = fd ∧ s.reg Reg.a1 = buf ∧ s.reg Reg.a2 = BitVec.ofNat 64 n ∧ n < 2 ^ 64
  post := fun ⟨fd, buf, n⟩ s s' => ∃ evs k, k ≤ n ∧ s'.trace = s.trace ++ evs ∧
    writtenTo fd evs = some (readBytes s.mem buf k) ∧ Outcome n k (s'.reg Reg.a0)
  reads := fun ⟨_, buf, n⟩ _ => [⟨buf, n⟩]

/-- `write_all` as compiled: correct for every way the kernel splits the
    writes, memory-safe, terminating, ABI-preserving. -/
theorem write_all_verified : VerifiedImg code write_all_dom write_all_entry spec := by
  rintro ⟨fd, buf, n⟩ s he ⟨ha0, ha1, ha2, hn⟩
  nocompiler_auto write_all_func s he
    loop_inv $l1 (fun u => ∃ k evs, k ≤ n ∧ u.reg 11 = buf + BitVec.ofNat 64 k ∧
        u.reg 12 = BitVec.ofNat 64 (n - k) ∧ u.reg 13 = fd ∧ u.reg 17 = 64#64 ∧ u.mem = s.mem ∧
        u.trace = s.trace ++ evs ∧ writtenTo fd evs = some (readBytes s.mem buf k))
      measure (fun u => (u.reg 12).toNat)
  case entry_to_l1 => exact ⟨0, [], by omega, by simp, by simp, trivial, trivial, trivial, by simp, by simp [readBytes]⟩
  case l1_ret_x28 => exact .inl ⟨by omega, rfl⟩
  case l1_ret_x20 => exact .inr ⟨sys_err, nocompiler_he1, nocompiler_he2, rfl⟩
  case l1_to_l1 =>
    refine ⟨k + sys_n, evs ++ [.write fd (readBytes s.mem (buf + BitVec.ofNat 64 k) sys_n)], by omega, rfl,
      ?_, trivial, trivial, trivial, by simp, ?_⟩
    · apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_ofNat]; omega
    · rw [writtenTo_append_write, h8, readBytes_add]; rfl

/-- The message in `.rodata`. -/
def message : List Byte := "nocompiler\n".toList.map fun c => BitVec.ofNat 8 c.toNat

theorem message_in_rodata : seg_rodata.bytes.toList.take 11 = message := by decide

/-- `void hello(void)`: writes the message to fd 1 and exits, 0 if all of it
    was written, 1 if the kernel returned an error. It never returns. It reads
    `.rodata`, which must be loaded and must not overlap its 16-byte frame. -/
def helloSpec : Spec Unit where
  pre := fun _ s => seg_rodata.Loaded s.mem ∧
    ∀ x, seg_rodata.region.mem x → ¬ (Spec.stackRegion s 16).mem x
  post := fun _ _ _ => False
  onExit := fun _ s s' => ∃ evs k c, s'.trace = s.trace ++ evs ++ [.exit c] ∧ s'.exit = some c ∧
    writtenTo 1 evs = some (message.take k) ∧ ((k = 11 ∧ c = 0) ∨ (k ≤ 11 ∧ c = 1))
  reads := fun _ _ => [seg_rodata.region]
  stack := 16

theorem srl63_ok : (0#64 : Word) >>> 63 = 0 := by decide

theorem srl63_err {e : Nat} (h1 : 1 ≤ e) (h2 : e ≤ 4095) : (-(BitVec.ofNat 64 e)) >>> 63 = 1 := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_neg, toNat_ofNat_of_lt (by omega)]
  simp only [Nat.shiftRight_eq_div_pow]
  rw [Nat.mod_eq_of_lt (by omega)]
  simp; omega

/-- `hello` as compiled: writes a prefix of the message and exits, the whole
    message exactly when it exits with 0; never returns. -/
theorem hello_verified : VerifiedImg code hello_dom hello_entry helloSpec := by
  rintro ⟨⟩ s he ⟨hro, hdisj⟩
  nocompiler_auto hello_func s he [seg_rodata] calls [write_all_verified]
  case entry_exit_x30 =>
    -- The bytes written: the message, which the frame's one store did not touch.
    have hbytes : readBytes (writeLE s.mem (s.reg 2 + 18446744073709551608#64) (s.reg 1).toNat 8)
        65880#64 k = message.take k := by
      rw [Auto.readBytes_writeLE_of_outside hdisj _ _ _ _ (by nocompiler_disch)
        (by simp [Region.covers, Segment.region, seg_rodata]; omega)]
      have := Segment.readBytes_of_loaded hro 0 k (by simp [seg_rodata]; omega)
      simp only [BitVec.add_zero, List.drop_zero] at this
      rw [show (65880#64 : Word) = seg_rodata.base from rfl, this, ← message_in_rodata, List.take_take,
        Nat.min_eq_left hc_write_all_verified_1]
    refine ⟨evs, k, _, by simp, rfl, by rw [hc_write_all_verified_3, hbytes], ?_⟩
    rcases nocompiler_cpost_entry_call_write_all_verified with ⟨hk11, h0⟩ | ⟨e, he1, he2, herr⟩
    · exact .inl ⟨hk11, by rw [h0]; decide⟩
    · exact .inr ⟨hc_write_all_verified_1, by rw [herr]; exact srl63_err he1 he2⟩

end Examples.Chunks.Hello
