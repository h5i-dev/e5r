import NoCompiler.Linux.FsIo
import NoCompiler.Linux.Start

/-
The fuzz-driver shape `prog FILE` end to end: at a process's entry
(`StartState`, Linux/Start.lean) the word at sp + 16 is the address of
argv[1], and there lies FILE and its NUL; so `openat(AT_FDCWD, argv[1],
O_RDONLY)` in a fresh process whose file system holds FILE opens it, as fd 3
at offset 0 (`openat_argv1`). Its reads then get FILE's bytes (FsIo.lean).
-/
namespace NoCompiler.Linux

/-- The C string at `a` is `p` when `p` and a NUL lie there. -/
theorem cString_of_readBytes {m : Word → Byte} :
    ∀ {a : Word} {p : List Byte} {n : Nat}, readBytes m a (p.length + 1) = p ++ [0] → 0 ∉ p →
      p.length < n → cString m a n = some p
  | _, _, 0, _, _, hn => by omega
  | a, [], n + 1, h, _, _ => by
    simp only [List.length_nil, readBytes, List.nil_append, List.cons.injEq] at h
    simp [cString, h.1]
  | a, b :: p, n + 1, h, h0, hn => by
    rw [List.length_cons, readBytes, List.cons_append] at h
    obtain ⟨h1, h2⟩ := List.cons.inj h
    have hb : b ≠ 0 := fun hb => h0 (hb ▸ List.mem_cons_self ..)
    have ih := cString_of_readBytes (a := a + 1) (p := p) (n := n) h2
      (fun hp => h0 (List.mem_cons_of_mem _ hp)) (by simp at hn; omega)
    rw [cString, h1, if_neg hb, ih]; rfl

theorem stringAddrs_length (b : Word) (l : List (List Byte)) : (stringAddrs b l).1.length = l.length := by
  induction l generalizing b <;> simp [stringAddrs, *]

/-- String `i` of strings laid from `base` lies, with its NUL, at its address. -/
theorem string_at {m : Word → Byte} :
    ∀ {base : Word} {l : List (List Byte)} {i : Nat} (hi : i < l.length),
      readBytes m base (flattenStrings l).length = flattenStrings l →
      readBytes m ((stringAddrs base l).1[i]'(by rw [stringAddrs_length]; exact hi)) (l[i].length + 1)
        = l[i] ++ [0]
  | _, [], _, hi, _ => by simp at hi
  | base, s :: rest, i, hi, h => by
    have hf : flattenStrings (s :: rest) = (s ++ [0]) ++ flattenStrings rest := by
      simp [flattenStrings]
    rw [hf] at h
    cases i with
    | zero =>
      have := readBytes_take h
      simpa [stringAddrs] using this
    | succ i =>
      have h' := readBytes_drop h
      have hl : (s ++ [0]).length = s.length + 1 := by simp
      rw [hl] at h'
      have := string_at (base := base + BitVec.ofNat 64 (s.length + 1)) (l := rest) (i := i)
        (by simpa using hi) h'
      simpa [stringAddrs] using this

/-- At entry, argv[i]'s string and its NUL lie at the address the stack gives for it. -/
theorem argv_string {e : Word} {a : StartArgs} {s : State} (h : StartState e a s) {i : Nat}
    (hi : i < a.argv.length) :
    readBytes s.mem (read64 s.mem (s.reg Reg.sp + BitVec.ofNat 64 (8 * (i + 1))))
      (a.argv[i].length + 1) = a.argv[i] ++ [0] := by
  rw [argv_at h hi]
  have hs := h.strs
  simp only [StartArgs.strs] at hs
  exact string_at hi (readBytes_take hs)

/-- `prog FILE`: in a fresh process (fds 0, 1, 2; no file open) whose file
    system holds FILE, `openat(AT_FDCWD, argv[1], O_RDONLY)` opens FILE as
    fd 3 at offset 0. -/
theorem openat_argv1 {e : Word} {a : StartArgs} {s : State} (h : StartState e a s)
    {prog file d : List Byte} (hargv : a.argv = [prog, file]) (h0 : 0 ∉ file)
    (hlen : file.length < 4096) {k k' : Kern} (hk : k.fds = [0, 1, 2]) (hfs : k.fs.lookup file = some d)
    {o : Outcome}
    (hspec : openatSpec k ⟨sysOpenat, [atFdcwd, read64 s.mem (s.reg Reg.sp + 16), 0, 0, 0, 0], s.mem⟩ o k') :
    o = .ret { ret := 3 } none ∧ k'.files = (3, ⟨d, 0⟩) :: k.files := by
  have hi : 1 < a.argv.length := by simp [hargv]
  have hstr := argv_string h hi
  have hf : a.argv[1] = file := by simp [hargv]
  rw [hf, show BitVec.ofNat 64 (8 * (1 + 1)) = (16 : Word) by decide] at hstr
  have hc := cString_of_readBytes hstr h0 hlen
  have hfree : lowestFree k.fds = 3 := by rw [hk]; decide
  simp only [openatSpec, SyscallInput.arg, List.getD, List.getElem?_cons_succ, List.getElem?_cons_zero,
    Option.getD_some, hc, hfs, hfree] at hspec
  obtain ⟨-, -, hspec⟩ := hspec
  simp only [show (3 : Nat) < 1024 by decide, ↓reduceIte] at hspec
  obtain ⟨rfl, rfl⟩ := hspec
  exact ⟨rfl, rfl⟩

/-- Control: with FILE not in the file system, the same call gives ENOENT. -/
theorem openat_argv1_missing {e : Word} {a : StartArgs} {s : State} (h : StartState e a s)
    {prog file : List Byte} (hargv : a.argv = [prog, file]) (h0 : 0 ∉ file)
    (hlen : file.length < 4096) {k k' : Kern} (hfs : k.fs.lookup file = none) {o : Outcome}
    (hspec : openatSpec k ⟨sysOpenat, [atFdcwd, read64 s.mem (s.reg Reg.sp + 16), 0, 0, 0, 0], s.mem⟩ o k') :
    o = .ret { ret := enoent } none ∧ k' = k := by
  have hi : 1 < a.argv.length := by simp [hargv]
  have hstr := argv_string h hi
  have hf : a.argv[1] = file := by simp [hargv]
  rw [hf, show BitVec.ofNat 64 (8 * (1 + 1)) = (16 : Word) by decide] at hstr
  have hc := cString_of_readBytes hstr h0 hlen
  simp only [openatSpec, SyscallInput.arg, List.getD, List.getElem?_cons_succ, List.getElem?_cons_zero,
    Option.getD_some, hc, hfs] at hspec
  exact hspec.2.2

end NoCompiler.Linux
