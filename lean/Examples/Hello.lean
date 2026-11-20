/-
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
-/
import Examples.Hello.Image

namespace Examples.Hello
open NoCompiler Examples.Hello.Image

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
theorem write_all_verified : Verified code write_all_dom write_all_entry spec := by
  rintro ⟨fd, buf, n⟩ s he ⟨ha0, ha1, ha2, hn⟩
  have hpc : s.pc = 0x11164#64 := he.pc
  have hx := he.live
  -- mv a3, a0; li a7, 64
  nocompiler_steps 2 [hpc]
  let I : State → Prop := fun u => ∃ k evs, k ≤ n ∧ u.pc = 0x1116c#64 ∧ u.exit = none ∧
    u.reg 11 = buf + BitVec.ofNat 64 k ∧ u.reg 12 = BitVec.ofNat 64 (n - k) ∧ u.reg 13 = fd ∧
    u.reg 17 = 64#64 ∧ Same s u [10, 11, 12, 13, 17] ∧ u.mem = s.mem ∧
    u.trace = s.trace ++ evs ∧ writtenTo fd evs = some (readBytes s.mem buf k)
  refine Reach.loop I (fun u => (u.reg 12).toNat) ?_ _ ?_
  · rintro u ⟨k, evs, hk, hpc', hx', h11, h12, h13, h17, hsame, hmem, htr, hw⟩
    -- beqz a2, done
    nocompiler_step [hpc', h12]
    have hra : u.reg 1 = s.reg 1 := hsame 1 (by decide)
    by_cases hz : k = n
    · -- n bytes written: return 0.
      subst hz
      simp only [Nat.sub_self, BitVec.ofNat_eq_ofNat, beq_self_eq_true, ite_true, Reach.opt_some]
      nocompiler_steps 2 [hra]
      rw [ret_mask he.retAligned]
      simp only [he.retAligned, ite_true, Reach.opt_some]
      refine .done (.inl ⟨.inl (by nocompiler_norm; exact he.ret), .inl ⟨by nocompiler_norm [hx'], by nocompiler_norm, ?_, ?_⟩⟩)
      · refine Same.preserved (rs := [10, 11, 12, 13, 17]) ?_ (by decide); nocompiler_same
      · exact ⟨evs, k, Nat.le_refl _, by nocompiler_norm [htr], hw, .inl ⟨rfl, by nocompiler_norm⟩⟩
    · -- Some left: one write.
      have hnk : 0 < n - k := by omega
      have hne : (BitVec.ofNat 64 (n - k) == 0) = false := by
        simp only [beq_eq_false_iff_ne, ne_eq]
        rw [ofNat_eq_zero_iff (by omega)]; omega
      simp only [hne, Bool.false_eq_true, ite_false, Reach.opt_some]
      -- mv a0, a3
      nocompiler_step [h13]
      -- ecall
      refine Reach.sys_step (by nocompiler_norm <;> decide) (by nocompiler_norm [hx']) (by nocompiler_norm <;> rfl)
        ⟨fun _ => ?_, fun h => ?_⟩ ⟨_, Sys.writeErr 1 (by nocompiler_norm [h17]) (by decide) (by decide)⟩ ?_
      · right
        refine ⟨⟨buf, n⟩, by simp [Spec.perm, spec], ?_⟩
        unfold Region.covers
        nocompiler_norm [h11, h12]
        rw [add_ofNat_sub_toNat buf (by omega), toNat_ofNat_of_lt (by omega)]
        omega
      · nocompiler_norm [h17] at h <;> exact absurd h (by decide)
      intro s' hs
      cases hs with
      | writeOk r h7 hle hmax hpos =>
        have hr : 1 ≤ r := by
          have := hpos (by nocompiler_norm [h12]; rw [toNat_ofNat_of_lt (by omega)]; omega); omega
        have hle' : r ≤ n - k := by
          nocompiler_norm [h12] at hle; rwa [toNat_ofNat_of_lt (by omega)] at hle
        -- add a1, a1, a0; sub a2, a2, a0; bgez a0, loop
        nocompiler_steps 3 [h11, h12, h13, ofNat_not_slt_zero hmax]
        refine .done (.inr ⟨⟨k + r, evs ++ [.write fd (readBytes s.mem (buf + BitVec.ofNat 64 k) r)],
          by omega, by nocompiler_norm, by nocompiler_norm [hx'], ?_, ?_, by nocompiler_norm [h13], by nocompiler_norm [h17], ?_,
          by nocompiler_norm [hmem], ?_, ?_⟩, ?_⟩)
        · nocompiler_norm [h11]; exact add_ofNat_add buf k r
        · nocompiler_norm [h12]
          apply BitVec.eq_of_toNat_eq
          rw [BitVec.toNat_sub, toNat_ofNat_of_lt (by omega), toNat_ofNat_of_lt (by omega),
            toNat_ofNat_of_lt (by omega)]
          omega
        · nocompiler_same
        · nocompiler_norm [htr, h13, h11, hmem]; simp
        · rw [writtenTo_append_write, hw, readBytes_add]; rfl
        · nocompiler_norm [h12]
          simp only [BitVec.toNat_sub, toNat_ofNat_of_lt (show n - k < 2 ^ 64 by omega),
            toNat_ofNat_of_lt (show r < 2 ^ 64 by omega)]
          omega
      | writeErr e h7 he1 he2 =>
        -- add a1, a1, a0; sub a2, a2, a0; bgez a0 not taken; ret
        nocompiler_steps 4 [h11, h12, h13, hra, neg_ofNat_slt_zero he1 he2]
        rw [ret_mask he.retAligned]
        simp only [he.retAligned, ite_true, Reach.opt_some]
        refine .done (.inl ⟨.inl (by nocompiler_norm; exact he.ret), .inl ⟨by nocompiler_norm [hx'], by nocompiler_norm, ?_, ?_⟩⟩)
        · refine Same.preserved (rs := [10, 11, 12, 13, 17]) ?_ (by decide); nocompiler_same
        · exact ⟨evs, k, hk, by nocompiler_norm [htr], hw, .inr ⟨e, he1, he2, by nocompiler_norm⟩⟩
      | readOk ds h7 => nocompiler_norm [h17] at h7 <;> exact absurd h7 (by decide)
      | readErr e h7 => nocompiler_norm [h17] at h7 <;> exact absurd h7 (by decide)
      | exit h7 => nocompiler_norm [h17] at h7 <;> exact absurd h7 (by decide)
  · refine ⟨0, [], by omega, by nocompiler_norm, by nocompiler_norm [hx], by nocompiler_norm [ha1], ?_, by nocompiler_norm [ha0],
      by nocompiler_norm, ?_, by nocompiler_norm, by nocompiler_norm; simp, by simp [readBytes]⟩
    · nocompiler_norm [ha2]; simp
    · nocompiler_same

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
theorem hello_verified : Verified code hello_dom hello_entry helloSpec := by
  rintro ⟨⟩ s he ⟨hro, hdisj⟩
  have hpc : s.pc = 0x11190#64 := he.pc
  have hx := he.live
  have hfb : s.reg 2 + 0xfffffffffffffff0#64 = s.reg 2 - BitVec.ofNat 64 16 := by bv_omega
  generalize hF : s.reg 2 - BitVec.ofNat 64 16 = fb at hfb
  have hfal : aligned fb 16 := by
    have : aligned (s.reg 2) 16 := he.sp
    unfold aligned at this ⊢
    rw [← hF, BitVec.toNat_sub, Nat.mod_mod_of_dvd _ (by decide : 16 ∣ 2 ^ 64)]
    rw [toNat_ofNat_of_lt (by decide)]; omega
  have hcov : (Spec.stackRegion s 16).covers (fb + 8#64) 8 := by
    unfold Region.covers Spec.stackRegion
    simp only [hF]
    rw [add_ofNat_sub_toNat fb (by omega)]; omega
  have hal8 : aligned (fb + 8#64) 8 :=
    aligned_add_ofNat (a := fb) (m := 8) (by unfold aligned at hfal ⊢; omega) (by decide) (by decide)
  -- addi sp, sp, -16; sd ra, 8(sp)
  nocompiler_step [hpc, hfb]
  nocompiler_step
  · right
    exact ⟨Spec.stackRegion s 16, by simp [Spec.perm, helloSpec], hcov⟩
  simp only [hal8, ite_true, Reach.opt_some]
  generalize hM : writeLE s.mem (fb + 8#64) (s.reg 1).toNat 8 = M
  have hMro : seg_rodata.Loaded M := by
    intro i hi
    rw [← hM, writeLE_of_not_mem hcov (hdisj _ ?_)]
    · exact hro i hi
    · show (_ - seg_rodata.base).toNat < seg_rodata.bytes.size
      rw [show seg_rodata.base + BitVec.ofNat 64 i - seg_rodata.base = BitVec.ofNat 64 i by bv_omega,
        toNat_ofNat_of_lt (by simp [seg_rodata] at hi; omega)]
      exact hi
  have hM8 : read64 M (fb + 8#64) = s.reg 1 := by rw [← hM]; exact read64_writeLE_same _ _ _
  -- la a1, message; li a0, 1; li a2, 11; call write_all
  nocompiler_steps 6
  have hPle : (spec.perm ⟨1#64, 0x10158#64, 11⟩
      (((((((((((((((s.setReg 2 fb).setMem M).setPc 70040#64).setReg 10 65536#64).setPc 70044#64).setReg 11
        65880#64).setPc 70048#64).setReg 10 1#64).setPc 70052#64).setReg 12 11#64).setPc 70056#64).setReg 1
        70056#64).setPc 70060#64).setReg 1 70064#64).setPc 69988#64)).le (helloSpec.perm () s) := by
    apply Perm.le_of
    · intro r hr
      simp only [Spec.perm, spec, List.mem_singleton] at hr
      subst hr
      exact ⟨seg_rodata.region, by simp [Spec.perm, helloSpec], by
        unfold Region.within Segment.region; decide⟩
    · intro r hr
      simp only [Spec.perm, spec, List.nil_append, List.mem_singleton] at hr
      subst hr
      refine ⟨Spec.stackRegion s 16, by simp [Spec.perm, helloSpec], ?_⟩
      unfold Region.within Spec.stackRegion
      nocompiler_norm [hF]
      have : fb - BitVec.ofNat 64 0 - fb = 0 := by bv_omega
      rw [this]; simp
  refine Verified.call write_all_verified ⟨1#64, 0x10158#64, 11⟩ ⟨by nocompiler_norm <;> rfl,
    by nocompiler_norm [hx], by nocompiler_norm <;> decide, by nocompiler_norm <;> decide, by nocompiler_norm <;> exact hfal⟩
    ⟨by nocompiler_norm, by nocompiler_norm, by nocompiler_norm, by decide⟩ (Dom.sub_of_ranges (by decide)) hPle ?_
  intro s1 hdone hfr
  obtain ⟨hx1, hpc1, hpres1, evs, k, hk, htr, hw, hout⟩ := hdone.resolve_right fun h => h.2.elim
  have h1pc : s1.pc = 70064#64 := by rw [hpc1]; nocompiler_norm
  have h1tr : s1.trace = s.trace ++ evs := by rw [htr]; nocompiler_norm
  have hm1 : s1.mem = M := by
    funext x
    rw [hfr x ?_]
    · nocompiler_norm
    · rintro ⟨r, hr, hm⟩
      simp only [Spec.perm, spec, List.nil_append, List.mem_singleton] at hr
      subst hr
      exact absurd hm (by simp [Region.mem, Spec.stackRegion])
  have hbytes : readBytes
      (((((((((((((((s.setReg 2 fb).setMem M).setPc 70040#64).setReg 10 65536#64).setPc 70044#64).setReg 11
        65880#64).setPc 70048#64).setReg 10 1#64).setPc 70052#64).setReg 12 11#64).setPc 70056#64).setReg 1
        70056#64).setPc 70060#64).setReg 1 70064#64).setPc 69988#64).mem 0x10158#64 k = message.take k := by
    nocompiler_norm
    have := Segment.readBytes_of_loaded hMro 0 k (by simp [seg_rodata]; omega)
    simp only [BitVec.add_zero, List.drop_zero] at this
    rw [show (0x10158#64 : Word) = seg_rodata.base from rfl, this, ← message_in_rodata,
      List.take_take, Nat.min_eq_left hk]
  rw [hbytes] at hw
  -- srli a0, a0, 63: the exit status, 1 exactly when write_all returned an error.
  generalize hc : s1.reg 10 >>> 63 = c
  have hcases : (k = 11 ∧ c = 0) ∨ (k ≤ 11 ∧ c = 1) := by
    rcases hout with ⟨hk11, h0⟩ | ⟨e, he1, he2, herr⟩
    · exact .inl ⟨hk11, by rw [← hc, h0]; decide⟩
    · exact .inr ⟨hk, by rw [← hc, herr]; exact srl63_err he1 he2⟩
  -- srli; li a7, 93; li a1, 0; li a2, 0
  nocompiler_steps 4 [h1pc, hc]
  -- ecall: exit
  refine Reach.sys_step (by nocompiler_norm <;> decide) (by nocompiler_norm [hx1]) (by nocompiler_norm <;> rfl)
    ⟨fun h => by nocompiler_norm at h <;> exact absurd h (by decide),
     fun h => by nocompiler_norm at h <;> exact absurd h (by decide)⟩
    ⟨_, Sys.exit (.inl (by nocompiler_norm))⟩ ?_
  intro s' hs
  cases hs with
  | exit _ =>
    refine .done ⟨.inr (by nocompiler_norm <;> simp), .inr ⟨by nocompiler_norm <;> simp,
      ⟨evs, k, c, ?_, by nocompiler_norm, hw, hcases⟩⟩⟩
    nocompiler_norm [h1tr]
  | writeOk r h7 => nocompiler_norm at h7 <;> exact absurd h7 (by decide)
  | writeErr e h7 => nocompiler_norm at h7 <;> exact absurd h7 (by decide)
  | readOk ds h7 => nocompiler_norm at h7 <;> exact absurd h7 (by decide)
  | readErr e h7 => nocompiler_norm at h7 <;> exact absurd h7 (by decide)

end Examples.Hello
