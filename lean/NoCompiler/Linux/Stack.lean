import NoCompiler.Linux.Start

/-
The Linux layer: the whole entry stack, from sp to the stack's top (LPS
theories/LinuxProcessSem/StackLayout.v#L368-L512, `at_random_bytes`,
`block_head_size`, `at_random_ptr`, `block_pad_len`, `build_stack_bytes`;
Linux v6.18.46 fs/binfmt_elf.c create_elf_tables). Bottom to top:

  argc, argv pointers, NULL, envp pointers, NULL, auxv, AT_NULL  `head`
  zero gap, so the random bytes are 16-aligned                    0 or 8
  the sixteen AT_RANDOM bytes                                     16
  the pad arch_align_stack left (zeros)                           `blockPadLen`
  argv strings, envp strings, the exec file name and its NUL      L
  the slot create_init_stack_vma skipped (zeros)                  8

`head` is `StartArgs.head` of `launchArgs` (the same words LPS writes with
`word_le8` and `auxv_bytes`), so Start.lean's lemmas read it. Every address
is a function of sp, top, the strings and `rseq`; the random draw is read
only by the sixteen bytes.

`startState_of_stack`: a state whose memory from sp holds this block, with
the block fitting below `top`, is a `StartState` for `launchArgs`.
`random_at`, `execfn_at`: AT_RANDOM and AT_EXECFN point at the random bytes
and the file name.
-/
namespace NoCompiler.Linux

/-- The sixteen AT_RANDOM bytes, little-endian. -/
def atRandomBytes (rnd : BitVec 128) : List Byte :=
  (List.range 16).map fun i => (rnd >>> (8 * i)).setWidth 8

theorem atRandomBytes_length (rnd : BitVec 128) : (atRandomBytes rnd).length = 16 := by
  simp [atRandomBytes]

/-- The auxv with AT_NULL, in bytes: 16 per entry. -/
def auxvSize (rseq : Bool) : Nat := 16 * (if rseq then 29 else 27)

/-- C: from sp to the top of the random bytes. -/
def blockHeadSize (rseq : Bool) (argv envp : List (List Byte)) : Nat :=
  let items := blockItems argv envp
  8 * items + auxvSize rseq + 8 * (items % 2) + 16

/-- AT_RANDOM: the bottom of the sixteen bytes. -/
def atRandomPtr (sp : Word) (rseq : Bool) (argv envp : List (List Byte)) : Word :=
  sp + BitVec.ofNat 64 (blockHeadSize rseq argv envp - 16)

/-- The pad: what is left of `top - sp` (clamped at 0, as LPS's `Z.to_nat`). -/
def blockPadLen (rseq : Bool) (sp top : Word) (argv envp : List (List Byte)) (execfn : List Byte) : Nat :=
  top.toNat - 8 - launchStringBytes argv envp execfn - sp.toNat - blockHeadSize rseq argv envp

/-- The arguments the entry stack lays out (Start.lean's `StartArgs`). -/
def launchArgs (la : LaunchAuxv) (ph : PhdrInfo) (entry sp top : Word) (argv envp : List (List Byte))
    (execfn : List Byte) (uid gid hwcap : Word) : StartArgs :=
  { argv := argv, envp := envp,
    auxv := auxvEntries la ph entry uid gid hwcap (atRandomPtr sp la.rseq argv envp) (atExecfnPtr top execfn),
    sbase := stringBaseAddr top argv envp execfn }

/-- The block from sp to top (LPS `build_stack_bytes`). -/
def buildStackBytes (la : LaunchAuxv) (ph : PhdrInfo) (entry sp top : Word) (argv envp : List (List Byte))
    (execfn : List Byte) (uid gid hwcap : Word) (rnd : BitVec 128) : List Byte :=
  (launchArgs la ph entry sp top argv envp execfn uid gid hwcap).head ++
    List.replicate (8 * (blockItems argv envp % 2)) 0 ++ atRandomBytes rnd ++
    List.replicate (blockPadLen la.rseq sp top argv envp execfn) 0 ++
    (flattenStrings argv ++ flattenStrings envp ++ execfn ++ [0]) ++ List.replicate 8 0

theorem head_length (la : LaunchAuxv) (hc : la.cache.length = 8) (ph : PhdrInfo) (entry sp top : Word)
    (argv envp : List (List Byte)) (execfn : List Byte) (uid gid hwcap : Word) :
    (launchArgs la ph entry sp top argv envp execfn uid gid hwcap).head.length +
      8 * (blockItems argv envp % 2) + 16 = blockHeadSize la.rseq argv envp := by
  have hn := auxvEntries_count la hc ph entry uid gid hwcap (atRandomPtr sp la.rseq argv envp)
    (atExecfnPtr top execfn)
  have hw : ∀ l : List Word, (l.flatMap wordBytes).length = 8 * l.length := by
    intro l; induction l <;> simp [wordBytes_length, *]; omega
  have hp : ∀ l : List (Word × Word), (l.flatMap fun p => [p.1, p.2]).length = 2 * l.length := by
    intro l; induction l <;> simp [*]; omega
  have hs : ∀ b (l : List (List Byte)), (stringAddrs b l).1.length = l.length := by
    intro b l; induction l generalizing b <;> simp [stringAddrs, *]
  simp only [StartArgs.head, hw, StartArgs.headWords, launchArgs, List.length_append, List.length_cons,
    List.length_nil, hp, hs, blockHeadSize, blockItems, auxvSize]
  split at hn <;> simp_all <;> omega

/-- The block fits: sp, the head, the strings and the slot lie below `top`. -/
def StackFits (rseq : Bool) (sp top : Word) (argv envp : List (List Byte)) (execfn : List Byte) : Prop :=
  sp.toNat + blockHeadSize rseq argv envp + launchStringBytes argv envp execfn + 8 ≤ top.toNat

/-- Then the block is exactly `top - sp` bytes (LPS
    `length_entry_stack_image_launch`). -/
theorem buildStackBytes_length (la : LaunchAuxv) (hc : la.cache.length = 8) (ph : PhdrInfo)
    (entry sp top : Word) (argv envp : List (List Byte)) (execfn : List Byte) (uid gid hwcap : Word)
    (rnd : BitVec 128) (hf : StackFits la.rseq sp top argv envp execfn) :
    (buildStackBytes la ph entry sp top argv envp execfn uid gid hwcap rnd).length = top.toNat - sp.toNat := by
  have h := head_length la hc ph entry sp top argv envp execfn uid gid hwcap
  simp only [buildStackBytes, List.length_append, List.length_replicate, atRandomBytes_length,
    List.length_cons, List.length_nil]
  unfold StackFits at hf
  unfold blockPadLen launchStringBytes at *
  omega

/-- Bytes `l₂` that lie after `l₁` in a run read as `l₁ ++ l₂ ++ l₃`. -/
theorem readBytes_mid {m : Word → Byte} {a : Word} {l₁ l₂ l₃ : List Byte}
    (h : readBytes m a (l₁ ++ l₂ ++ l₃).length = l₁ ++ l₂ ++ l₃) :
    readBytes m (a + BitVec.ofNat 64 l₁.length) l₂.length = l₂ := by
  rw [List.append_assoc] at h
  exact readBytes_take (readBytes_drop h)

section
variable {la : LaunchAuxv} {ph : PhdrInfo} {entry top : Word} {argv envp : List (List Byte)}
  {execfn : List Byte} {uid gid hwcap : Word} {rnd : BitVec 128} {s : State}

/-- The memory from sp holds the block. -/
def HoldsStack (la : LaunchAuxv) (ph : PhdrInfo) (entry top : Word) (argv envp : List (List Byte))
    (execfn : List Byte) (uid gid hwcap : Word) (rnd : BitVec 128) (s : State) : Prop :=
  readBytes s.mem (s.reg Reg.sp)
    (buildStackBytes la ph entry (s.reg Reg.sp) top argv envp execfn uid gid hwcap rnd).length =
    buildStackBytes la ph entry (s.reg Reg.sp) top argv envp execfn uid gid hwcap rnd

/-- AT_RANDOM points at the sixteen random bytes. -/
theorem random_at (hc : la.cache.length = 8)
    (h : HoldsStack la ph entry top argv envp execfn uid gid hwcap rnd s) :
    readBytes s.mem (atRandomPtr (s.reg Reg.sp) la.rseq argv envp) 16 = atRandomBytes rnd := by
  have hl := head_length la hc ph entry (s.reg Reg.sp) top argv envp execfn uid gid hwcap
  unfold HoldsStack buildStackBytes at h
  simp only [List.append_assoc] at h
  rw [← List.append_assoc, ← List.append_assoc] at h
  have := readBytes_mid h
  rw [atRandomBytes_length] at this
  rw [atRandomPtr, ← hl]
  simpa [Nat.add_sub_cancel] using this

/-- The strings: the block holds them at `stringBaseAddr` (with the fit). -/
theorem strings_at (hc : la.cache.length = 8) (hf : StackFits la.rseq (s.reg Reg.sp) top argv envp execfn)
    (h : HoldsStack la ph entry top argv envp execfn uid gid hwcap rnd s) :
    readBytes s.mem (stringBaseAddr top argv envp execfn)
      (flattenStrings argv ++ flattenStrings envp ++ execfn ++ [0]).length =
      flattenStrings argv ++ flattenStrings envp ++ execfn ++ [0] := by
  have hl := head_length la hc ph entry (s.reg Reg.sp) top argv envp execfn uid gid hwcap
  unfold HoldsStack buildStackBytes at h
  have := readBytes_mid (l₁ := (launchArgs la ph entry (s.reg Reg.sp) top argv envp execfn uid gid hwcap).head ++
    List.replicate (8 * (blockItems argv envp % 2)) 0 ++ atRandomBytes rnd ++
    List.replicate (blockPadLen la.rseq (s.reg Reg.sp) top argv envp execfn) 0) h
  have haddr : s.reg Reg.sp + BitVec.ofNat 64
      ((launchArgs la ph entry (s.reg Reg.sp) top argv envp execfn uid gid hwcap).head ++
        List.replicate (8 * (blockItems argv envp % 2)) 0 ++ atRandomBytes rnd ++
        List.replicate (blockPadLen la.rseq (s.reg Reg.sp) top argv envp execfn) 0).length =
      stringBaseAddr top argv envp execfn := by
    simp only [List.length_append, List.length_replicate, atRandomBytes_length]
    unfold stringBaseAddr
    unfold StackFits at hf
    unfold blockPadLen at *
    have hs := (s.reg Reg.sp).isLt
    have ht := top.isLt
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]
    omega
  rw [haddr] at this
  exact this

/-- A state whose memory from sp holds the block, fitting below `top`, is a
    start state for `launchArgs`. -/
theorem startState_of_stack (hc : la.cache.length = 8)
    (hf : StackFits la.rseq (s.reg Reg.sp) top argv envp execfn)
    (h : HoldsStack la ph entry top argv envp execfn uid gid hwcap rnd s)
    (hpc : s.pc = entry) (hlive : s.exit = none) (htr : s.trace = []) :
    StartState entry (launchArgs la ph entry (s.reg Reg.sp) top argv envp execfn uid gid hwcap) s := by
  refine ⟨hpc, hlive, htr, ?_, ?_⟩
  · have h' := h
    unfold HoldsStack buildStackBytes at h'
    simp only [List.append_assoc] at h'
    exact readBytes_take h'
  · have h1 := strings_at hc hf h
    rw [show flattenStrings argv ++ flattenStrings envp ++ execfn ++ [0] =
      (flattenStrings argv ++ flattenStrings envp) ++ (execfn ++ [0]) by simp] at h1
    exact readBytes_take h1

/-- AT_EXECFN points at the exec file name and its NUL. -/
theorem execfn_at (hc : la.cache.length = 8) (hf : StackFits la.rseq (s.reg Reg.sp) top argv envp execfn)
    (h : HoldsStack la ph entry top argv envp execfn uid gid hwcap rnd s) :
    readBytes s.mem (atExecfnPtr top execfn) (execfn.length + 1) = execfn ++ [0] := by
  have := strings_at hc hf h
  rw [List.append_assoc] at this
  have h2 := readBytes_drop this
  rw [← envp_end_eq_execfn top argv envp execfn, stringAddrs_snd, stringAddrs_snd]
  have hl : (flattenStrings argv ++ flattenStrings envp).length =
      (flattenStrings argv).length + (flattenStrings envp).length := by simp
  rw [hl] at h2
  simpa [BitVec.add_assoc, BitVec.ofNat_add] using h2

end

/-- `prog x`, no envp, no rseq: 5 items (argc, 2 pointers, 2 NULLs), 27 auxv
    entries of 16 bytes, an 8-byte gap (5 is odd), 16 random bytes. -/
example : blockHeadSize false [[0x70], [0x78]] [] = 5 * 8 + 432 + 8 + 16 := by decide

end NoCompiler.Linux
