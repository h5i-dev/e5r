import E5R.Machine

/-
The environment model: what an ECALL does (docs/isa/environment.md).

ECALL hands control to the Linux kernel, so the ISA does not say what happens.
This file says what e5r assumes happens, for the syscalls the profile admits
and nothing else. It is a relation, not a function: the kernel's choices
(how many bytes a write takes, what a read returns, which error) are left
open, and a proof has to hold for every one of them.

Assumptions, each one of them part of the trusted base:

* RISC-V Linux calling convention: number in a7, arguments in a0 to a5,
  result in a0, every other register and the pc + 4 continuation preserved.
* write(fd, buf, n), number 64: either an error -e with 1 <= e <= 4095, the
  trace unchanged; or r bytes accepted, 0 <= r <= min(n, 0x7ffff000), with
  r >= 1 when n >= 1, the event `write fd (first r bytes)` appended. Linux
  caps one transfer at MAX_RW_COUNT = 0x7ffff000. `r >= 1` excludes a
  zero-length write for a nonzero request, which Linux does not produce for
  pipes, terminals, sockets or regular files; it is what lets a write loop be
  proved to terminate.
* read(fd, buf, n), number 63: an error, or any byte string ds of length
  r <= min(n, 0x7ffff000), stored at buf, `read fd ds` appended. r = 0 is end
  of file.
* exit(code) and exit_group(code), numbers 93 and 94: the process ends with
  that status and `exit code` is appended.
* No signal handlers run, there is one thread, no other process writes this
  process's memory, and no syscall other than these four is used. A program
  that issues any other syscall has no successor here, so no proof about it
  goes through.
-/
namespace E5R

def sysRead : Word := 63
def sysWrite : Word := 64
def sysExit : Word := 93
def sysExitGroup : Word := 94

/-- Linux MAX_RW_COUNT on 4 KiB pages. -/
def maxRW : Nat := 0x7ffff000

/-- The pc + 4 continuation of a returning syscall with result `r`. -/
def State.sysRet (s : State) (r : Word) : State := (s.setReg Reg.a0 r).setPc (s.pc + 4)

inductive Sys : State → State → Prop
  | writeOk {s : State} (r : Nat) :
      s.reg Reg.a7 = sysWrite → r ≤ (s.reg Reg.a2).toNat → r ≤ maxRW →
      (0 < (s.reg Reg.a2).toNat → 0 < r) →
      Sys s ((s.sysRet (BitVec.ofNat 64 r)).emit
              (.write (s.reg Reg.a0) (readBytes s.mem (s.reg Reg.a1) r)))
  | writeErr {s : State} (e : Nat) :
      s.reg Reg.a7 = sysWrite → 1 ≤ e → e ≤ 4095 →
      Sys s (s.sysRet (-(BitVec.ofNat 64 e)))
  | readOk {s : State} (ds : List Byte) :
      s.reg Reg.a7 = sysRead → ds.length ≤ (s.reg Reg.a2).toNat → ds.length ≤ maxRW →
      Sys s (((s.sysRet (BitVec.ofNat 64 ds.length)).setMem
              (writeBytes s.mem (s.reg Reg.a1) ds)).emit (.read (s.reg Reg.a0) ds))
  | readErr {s : State} (e : Nat) :
      s.reg Reg.a7 = sysRead → 1 ≤ e → e ≤ 4095 →
      Sys s (s.sysRet (-(BitVec.ofNat 64 e)))
  | exit {s : State} :
      (s.reg Reg.a7 = sysExit ∨ s.reg Reg.a7 = sysExitGroup) →
      Sys s ((s.halt (s.reg Reg.a0)).emit (.exit (s.reg Reg.a0)))

end E5R
