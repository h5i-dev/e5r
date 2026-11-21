import NoCompiler.Linux.Fd
import NoCompiler.Trace

/-
The Linux layer, third step: the process start state (LPS StackLayout.v,
theories/LinuxProcessSem/StackLayout.v#L486 `build_stack_bytes`, after Linux
v6.18.46 fs/binfmt_elf.c create_elf_tables).

At entry, sp points at
  argc, argv[0..argc) pointers, 0, envp pointers, 0, auxv (type, value) pairs,
  AT_NULL (0, 0)
(`head`), each a little-endian 8-byte word, and the strings they point to lie
at `sbase` (`strs`, each NUL-terminated, argv then envp). LPS also lays the
exec file name, AT_RANDOM bytes and the alignment pads and computes `sbase`
and the auxv from the launch; here they are parameters (`StartArgs`), and
Linux/Stack.lean computes them (`launchArgs`, `buildStackBytes`,
`startState_of_stack`).

`StartState` says a machine state is such an entry state. `argc_at_sp` and
`argv_at`: from it, the word at sp is argc and the word at sp + 8 + 8i is the
address of argv[i]'s string.
-/
namespace NoCompiler.Linux

/-- A word as 8 little-endian bytes (LPS `word_le8`). -/
def wordBytes (v : Word) : List Byte :=
  (List.range 8).map fun i => (v >>> (8 * i)).setWidth 8

/-- The addresses of the strings laid from `base`, each with its NUL, and the
    address after the last (LPS `string_addrs`). -/
def stringAddrs (base : Word) : List (List Byte) → List Word × Word
  | [] => ([], base)
  | s :: rest =>
    let r := stringAddrs (base + BitVec.ofNat 64 (s.length + 1)) rest
    (base :: r.1, r.2)

/-- The strings, each followed by NUL (LPS `flatten_strings`). -/
def flattenStrings (ss : List (List Byte)) : List Byte := ss.flatMap fun s => s ++ [0]

structure StartArgs where
  argv : List (List Byte)
  envp : List (List Byte)
  auxv : List (Word × Word)
  /-- Where the strings start. -/
  sbase : Word

/-- The words at sp. -/
def StartArgs.headWords (a : StartArgs) : List Word :=
  let argvP := stringAddrs a.sbase a.argv
  let envpP := stringAddrs argvP.2 a.envp
  [BitVec.ofNat 64 a.argv.length] ++ argvP.1 ++ [0] ++ envpP.1 ++ [0] ++
    a.auxv.flatMap (fun p => [p.1, p.2]) ++ [0, 0]

def StartArgs.head (a : StartArgs) : List Byte := a.headWords.flatMap wordBytes

def StartArgs.strs (a : StartArgs) : List Byte := flattenStrings a.argv ++ flattenStrings a.envp

/-- `s` is the state at a process's entry point `entry`, started with `a`. -/
structure StartState (entry : Word) (a : StartArgs) (s : State) : Prop where
  pc : s.pc = entry
  live : s.exit = none
  trace : s.trace = []
  head : readBytes s.mem (s.reg Reg.sp) a.head.length = a.head
  strs : readBytes s.mem a.sbase a.strs.length = a.strs

theorem wordBytes_length (v : Word) : (wordBytes v).length = 8 := by simp [wordBytes]

/-- Eight bytes that are a word's read back as that word. -/
theorem read64_of_wordBytes {m : Word → Byte} {a v : Word} (h : readBytes m a 8 = wordBytes v) :
    read64 m a = v := by
  simp only [wordBytes, List.range_succ, List.range_zero, List.nil_append,
    List.map_cons, List.map_nil, List.cons_append, List.nil_append, readBytes, List.cons.injEq] at h
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, -⟩ := h
  apply BitVec.eq_of_toNat_eq
  simp only [read64, readLE, h0, h1, h2, h3, h4, h5, h6, h7, BitVec.toNat_ofNat, BitVec.toNat_setWidth,
    BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  have := v.isLt
  omega

theorem readBytes_len (m : Word → Byte) (a : Word) (n : Nat) : (readBytes m a n).length = n := by
  induction n generalizing a <;> simp [readBytes, *]

/-- A run of bytes read as `l₁ ++ l₂` holds `l₂` after `l₁`. -/
theorem readBytes_drop {m : Word → Byte} {a : Word} {l₁ l₂ : List Byte}
    (h : readBytes m a (l₁ ++ l₂).length = l₁ ++ l₂) :
    readBytes m (a + BitVec.ofNat 64 l₁.length) l₂.length = l₂ := by
  rw [List.length_append, readBytes_add] at h
  exact (List.append_inj h (readBytes_len _ _ _)).2

theorem readBytes_take {m : Word → Byte} {a : Word} {l₁ l₂ : List Byte}
    (h : readBytes m a (l₁ ++ l₂).length = l₁ ++ l₂) : readBytes m a l₁.length = l₁ := by
  rw [List.length_append, readBytes_add] at h
  exact (List.append_inj h (readBytes_len _ _ _)).1

/-- The `i`-th word of a run of words. -/
theorem read64_word {m : Word → Byte} {a : Word} {ws : List Word} {i : Nat} (hi : i < ws.length)
    (h : readBytes m a (ws.flatMap wordBytes).length = ws.flatMap wordBytes) :
    read64 m (a + BitVec.ofNat 64 (8 * i)) = ws[i] := by
  induction ws generalizing a i with
  | nil => simp at hi
  | cons w ws ih =>
    rw [List.flatMap_cons] at h
    cases i with
    | zero =>
      have := readBytes_take h
      rw [wordBytes_length] at this
      simpa using read64_of_wordBytes this
    | succ i =>
      have h' := readBytes_drop h
      rw [wordBytes_length] at h'
      have := ih (by simpa using hi) h'
      rw [show a + 8#64 + BitVec.ofNat 64 (8 * i) = a + BitVec.ofNat 64 (8 * (i + 1)) by
        apply BitVec.eq_of_toNat_eq; simp; omega] at this
      simpa using this

/-- At entry the word at sp is argc. -/
theorem argc_at_sp {e : Word} {a : StartArgs} {s : State} (h : StartState e a s) :
    read64 s.mem (s.reg Reg.sp) = BitVec.ofNat 64 a.argv.length := by
  have := read64_word (a := s.reg Reg.sp) (i := 0) (ws := a.headWords) (by simp [StartArgs.headWords]) h.head
  simpa [StartArgs.headWords] using this

/-- At entry the word at sp + 8 + 8i is the address of argv[i]'s string. -/
theorem argv_at {e : Word} {a : StartArgs} {s : State} (h : StartState e a s) {i : Nat}
    (hi : i < a.argv.length) :
    read64 s.mem (s.reg Reg.sp + BitVec.ofNat 64 (8 * (i + 1))) =
      (stringAddrs a.sbase a.argv).1[i]'(by
        have : ∀ b (l : List (List Byte)), (stringAddrs b l).1.length = l.length := by
          intro b l; induction l generalizing b <;> simp [stringAddrs, *]
        rw [this]; exact hi) := by
  have hlen : ∀ b (l : List (List Byte)), (stringAddrs b l).1.length = l.length := by
    intro b l; induction l generalizing b <;> simp [stringAddrs, *]
  have := read64_word (a := s.reg Reg.sp) (i := i + 1) (ws := a.headWords)
    (by simp [StartArgs.headWords, hlen]; omega) h.head
  rw [this]
  simp only [StartArgs.headWords, List.append_assoc, List.singleton_append]
  rw [List.getElem_append_left (by simp [hlen]; omega)]
  simp

/-! ## Where the strings go (LPS StackLayout.v#L388-L425) -/

/-- argc, the argv pointers and their NULL, the envp pointers and their NULL
    (`block_items`). -/
def blockItems (argv envp : List (List Byte)) : Nat := argv.length + envp.length + 3

/-- The string bytes with their NULs: argv, envp, the exec file name
    (`launch_string_bytes`). -/
def launchStringBytes (argv envp : List (List Byte)) (execfn : List Byte) : Nat :=
  (flattenStrings argv).length + (flattenStrings envp).length + execfn.length + 1

/-- The lowest string byte, argv[0]: the strings end 8 bytes below the stack
    top, the slot create_init_stack_vma skips (`string_base_addr`). -/
def stringBaseAddr (top : Word) (argv envp : List (List Byte)) (execfn : List Byte) : Word :=
  top - BitVec.ofNat 64 (8 + launchStringBytes argv envp execfn)

/-- AT_EXECFN: the exec file name, at the top of the string area (`at_execfn_ptr`). -/
def atExecfnPtr (top : Word) (execfn : List Byte) : Word :=
  top - BitVec.ofNat 64 (8 + execfn.length + 1)

theorem stringAddrs_snd (b : Word) (l : List (List Byte)) :
    (stringAddrs b l).2 = b + BitVec.ofNat 64 (flattenStrings l).length := by
  induction l generalizing b with
  | nil => simp [stringAddrs, flattenStrings]
  | cons x l ih =>
    simp only [stringAddrs, ih, flattenStrings, List.flatMap_cons, List.length_append, List.length_cons,
      List.length_nil]
    simp only [flattenStrings] at ih
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega

/-- The strings fit: argv, then envp, laid from the computed base, end exactly
    where AT_EXECFN's file name starts. -/
theorem envp_end_eq_execfn (top : Word) (argv envp : List (List Byte)) (execfn : List Byte) :
    (stringAddrs (stringAddrs (stringBaseAddr top argv envp execfn) argv).2 envp).2 =
      atExecfnPtr top execfn := by
  rw [stringAddrs_snd, stringAddrs_snd]
  unfold stringBaseAddr atExecfnPtr launchStringBytes
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]
  omega

/-! ## The auxiliary vector (LPS StackLayout.v#L160-L276, `auxv_entries`)

ARCH_DLINFO's ten entries first (fs/binfmt_elf.c: "ARCH_DLINFO must come
first"), then create_elf_tables' sixteen, then the CONFIG_RSEQ pair. LPS's
list ends with AT_NULL; here `StartArgs.headWords` appends it, so
`auxvEntries` stops before it. -/

/-- The launch's own values (LPS `LaunchAuxv` with its `CacheWords`). -/
structure LaunchAuxv where
  sysinfoEhdr : Word
  /-- AT_L1I_CACHESIZE … AT_L3_CACHEGEOMETRY, in that order. -/
  cache : List Word
  minsigstksz : Word
  rseq : Bool

/-- The program headers' place, entry size and count (LPS `PhdrInfo`). -/
structure PhdrInfo where
  addr : Word
  ent : Word
  num : Word

def AT_PHDR : Word := 3
def AT_PHENT : Word := 4
def AT_PHNUM : Word := 5
def AT_PAGESZ : Word := 6
def AT_BASE : Word := 7
def AT_FLAGS : Word := 8
def AT_ENTRY : Word := 9
def AT_UID : Word := 11
def AT_EUID : Word := 12
def AT_GID : Word := 13
def AT_EGID : Word := 14
def AT_HWCAP : Word := 16
def AT_CLKTCK : Word := 17
def AT_SECURE : Word := 23
def AT_RANDOM : Word := 25
def AT_RSEQ_FEATURE_SIZE : Word := 27
def AT_RSEQ_ALIGN : Word := 28
def AT_EXECFN : Word := 31
def AT_SYSINFO_EHDR : Word := 33
def AT_MINSIGSTKSZ : Word := 51
/-- AT_L1I_CACHESIZE (40) … AT_L3_CACHEGEOMETRY (47). -/
def cacheTypes : List Word := [40, 41, 42, 43, 44, 45, 46, 47]

def auxvEntries (la : LaunchAuxv) (ph : PhdrInfo) (entry uid gid hwcap atRandom atExecfn : Word) :
    List (Word × Word) :=
  [(AT_SYSINFO_EHDR, la.sysinfoEhdr)] ++ cacheTypes.zip la.cache ++ [(AT_MINSIGSTKSZ, la.minsigstksz),
    (AT_HWCAP, hwcap), (AT_PAGESZ, 4096), (AT_CLKTCK, 100),
    (AT_PHDR, ph.addr), (AT_PHENT, ph.ent), (AT_PHNUM, ph.num),
    (AT_BASE, 0), (AT_FLAGS, 0), (AT_ENTRY, entry),
    (AT_UID, uid), (AT_EUID, uid), (AT_GID, gid), (AT_EGID, gid),
    (AT_SECURE, 0), (AT_RANDOM, atRandom), (AT_EXECFN, atExecfn)] ++
  (if la.rseq then [(AT_RSEQ_FEATURE_SIZE, 28), (AT_RSEQ_ALIGN, 32)] else [])

/-- With AT_NULL, 27 entries, or 29 with CONFIG_RSEQ (LPS `auxv_count`). -/
theorem auxvEntries_count (la : LaunchAuxv) (hc : la.cache.length = 8) (ph : PhdrInfo)
    (entry uid gid hwcap atRandom atExecfn : Word) :
    (auxvEntries la ph entry uid gid hwcap atRandom atExecfn).length + 1 =
      if la.rseq then 29 else 27 := by
  unfold auxvEntries
  cases la.rseq <;> simp [cacheTypes, List.length_zip, hc]

/-- `getauxval(AT_PAGESZ)` is 4096 and `getauxval(AT_ENTRY)` the entry point. -/
theorem auxv_pagesz_entry (la : LaunchAuxv) (hc : la.cache.length = 8) (ph : PhdrInfo)
    (entry uid gid hwcap atRandom atExecfn : Word) :
    (auxvEntries la ph entry uid gid hwcap atRandom atExecfn).lookup AT_PAGESZ = some 4096 ∧
    (auxvEntries la ph entry uid gid hwcap atRandom atExecfn).lookup AT_ENTRY = some entry := by
  obtain ⟨c0, c1, c2, c3, c4, c5, c6, c7, hcl⟩ : ∃ c0 c1 c2 c3 c4 c5 c6 c7, la.cache = [c0, c1, c2, c3, c4, c5, c6, c7] := by
    match h : la.cache, hc with
    | [c0, c1, c2, c3, c4, c5, c6, c7], _ => exact ⟨c0, c1, c2, c3, c4, c5, c6, c7, rfl⟩
  constructor <;> simp [auxvEntries, hcl, cacheTypes, List.lookup, AT_PAGESZ, AT_ENTRY, AT_SYSINFO_EHDR,
    AT_MINSIGSTKSZ, AT_HWCAP, AT_CLKTCK, AT_PHDR, AT_PHENT, AT_PHNUM, AT_BASE, AT_FLAGS]

/-- Control: `prog x` with strings at 0x1000: argc 2, argv[0] at 0x1000 ("prog\0"),
    argv[1] at 0x1005; the head is 8 words with no envp and no auxv. -/
example : ({ argv := [[0x70, 0x72, 0x6f, 0x67], [0x78]], envp := [], auxv := [], sbase := 0x1000 } :
    StartArgs).headWords = [2, 0x1000, 0x1005, 0, 0, 0, 0] := by decide

end NoCompiler.Linux
