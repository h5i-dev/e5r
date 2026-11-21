import NoCompiler.Env

/-
The Linux layer, first step (docs/design/prior-art-lps.md, "Plan: porting the
LPS environment model"): what a syscall sees and what it does, in the shape of
rocq-linux-process-semantics (LPS, d3f3a701).

* `SyscallInput`: LPS `SyscallInput` (theories/LinuxProcessSem/State.v#L654):
  the number (a7), the arguments (a0..a5) and the memory the kernel reads.
  LPS has two views of memory (readable, writable) because its memory is
  partial; ours is total (`Word → Byte`), so there is one.
* `Effect`: LPS `SyscallEffect` (State.v#L719): the a0 result, the byte
  ranges written, the ranges zero-filled (kept symbolic as base and size).
  LPS's `eff_unmaps` and `eff_copies` need partial memory and mmap; they come
  with that step.
* `Effect.apply`: LPS `Run.apply_effect` (Run.v#L96-L226) restricted to the
  fields above, in LPS's order (zeros, then writes), then the pc + 4
  continuation with a0 = `ret`, as `State.sysRet` (Env.lean).

Nothing here is trusted on its own: `Linux.basic_iff_sys` (Linux/Basic.lean)
proves the layer, restricted to the syscalls Env.lean admits, equal to the
trusted `Sys`.
-/
namespace NoCompiler.Linux

/-- What the kernel is handed at an `ecall`. -/
structure SyscallInput where
  sysno : Word
  args : List Word
  mem : Word → Byte

/-- The input of the `ecall` at state `s`: a7, a0..a5, the memory. -/
def SyscallInput.of (s : State) : SyscallInput :=
  ⟨s.reg Reg.a7, [s.reg 10, s.reg 11, s.reg 12, s.reg 13, s.reg 14, s.reg 15], s.mem⟩

/-- Argument `k` (a0 is 0); 0 past a5, as LPS's `in_arg`. -/
def SyscallInput.arg (i : SyscallInput) (k : Nat) : Word := i.args.getD k 0

/-- What a returning syscall does to the process. -/
structure Effect where
  ret : Word
  /-- (base, bytes), applied in order. -/
  writes : List (Word × List Byte) := []
  /-- (base, size) zero-filled ranges. -/
  zeros : List (Word × Nat) := []

/-- Zero-fill `n` bytes from `a`. -/
def zeroFill (m : Word → Byte) (a : Word) (n : Nat) : Word → Byte :=
  fun x => if (x - a).toNat < n then 0 else m x

def applyZeros (m : Word → Byte) : List (Word × Nat) → (Word → Byte)
  | [] => m
  | (a, n) :: zs => applyZeros (zeroFill m a n) zs

def applyWrites (m : Word → Byte) : List (Word × List Byte) → (Word → Byte)
  | [] => m
  | (a, bs) :: ws => applyWrites (writeBytes m a bs) ws

/-- The memory after the effect: zeros, then writes (LPS's order). -/
def Effect.mem (e : Effect) (m : Word → Byte) : Word → Byte :=
  applyWrites (applyZeros m e.zeros) e.writes

/-- How a syscall ends: it returns with an effect (and maybe an event), or it
    ends the process with a status. -/
inductive Outcome
  | ret (e : Effect) (ev : Option Event)
  | exit (code : Word)

/-- The state after the outcome, from the state at the `ecall`. -/
def Outcome.apply (s : State) : Outcome → State
  | .ret e none => (s.sysRet e.ret).setMem (e.mem s.mem)
  | .ret e (some ev) => ((s.sysRet e.ret).setMem (e.mem s.mem)).emit ev
  | .exit code => (s.halt code).emit (.exit code)

@[simp] theorem Effect.mem_nil (r : Word) (m : Word → Byte) : ({ ret := r } : Effect).mem m = m := rfl

@[simp] theorem State.setMem_self (s : State) : s.setMem s.mem = s := rfl

@[simp] theorem State.sysRet_mem (s : State) (r : Word) : (s.sysRet r).mem = s.mem := rfl

end NoCompiler.Linux
