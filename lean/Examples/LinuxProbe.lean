import NoCompiler.Linux.FsIo
import NoCompiler.Linux.Prot

/-
The Linux layer against Linux: Examples/LinuxProbe/probe.c makes each
modelled file syscall on a 6-byte file "abcdef" and prints what it gets
(Examples/LinuxProbe/probe.out, recorded under qemu-riscv64 user mode on a
Linux 6.12.113 host: the file calls go to the host kernel; mprotect/munmap
are qemu's emulation). Each theorem below is one line of probe.out: the
model's outcome is what Linux returned. `run.sh` reruns the probe and diffs
it against probe.out.
-/
namespace Examples.LinuxProbe
open NoCompiler NoCompiler.Linux

def abcdef : List Byte := [0x61, 0x62, 0x63, 0x64, 0x65, 0x66]

/-- `openat 3`, and `reopen 3` after `close`: the lowest free descriptor. -/
theorem openat_fd : lowestFree [0, 1, 2] = 3 := by decide
theorem reopen_fd : lowestFree (([0, 1, 2] ++ [3] : List Word).erase 3) = 3 := by decide

/-- `read4 4`, `read4.bytes abcd`. -/
theorem read4 : OpenFile.chunk ⟨abcdef, 0⟩ 4 = [0x61, 0x62, 0x63, 0x64] := by decide

/-- `lseek.cur0 4`, `lseek.end-2 4`, `lseek.data2 2`, `lseek.hole2 6`,
    `lseek.data6 -6`, `lseek.whence5 -22`, `lseek.set-1 -22`, `lseek.set0 0`
    (the offset is 4 after the read). -/
theorem lseeks :
    (seekTo ⟨abcdef, 4⟩ 0 1).1 = 4 ∧ (seekTo ⟨abcdef, 4⟩ (-2) 2).1 = 4 ∧
    (seekTo ⟨abcdef, 4⟩ 2 3).1 = 2 ∧ (seekTo ⟨abcdef, 4⟩ 2 4).1 = 6 ∧
    (seekTo ⟨abcdef, 4⟩ 6 3).1 = -6 ∧ (seekTo ⟨abcdef, 4⟩ 0 5).1 = -22 ∧
    (seekTo ⟨abcdef, 4⟩ (-1) 0).1 = -22 ∧ (seekTo ⟨abcdef, 4⟩ 0 0).1 = 0 := by decide

/-- `readv23 5`, `readv.b1 ab`, `readv.b2 cde` (iovecs of 2 and 3 bytes, offset 0). -/
theorem readv23 :
    (OpenFile.chunk ⟨abcdef, 0⟩ 5).length = 5 ∧
    scatter [(0x100, 2), (0x200, 3)] (OpenFile.chunk ⟨abcdef, 0⟩ 5) =
      [(0x100, [0x61, 0x62]), (0x200, [0x63, 0x64, 0x65])] := by decide

/-- `read10 1`, `read10.bytes f`, `read.eof 0` (offset 5, then 6). -/
theorem read_tail : OpenFile.chunk ⟨abcdef, 5⟩ 10 = [0x66] ∧ OpenFile.chunk ⟨abcdef, 6⟩ 10 = [] := by
  decide

/-- `fstat.size 6`: the size field the spec fixes is 6, little-endian. -/
theorem fstat_size : le64 abcdef.length = [6, 0, 0, 0, 0, 0, 0, 0] := by decide

/-- The error numbers: `close.again`/`read.closed`/`lseek.closed`/`fstat.closed`
    -9, `openat.missing` -2, `readv.1025`, `mprotect.unaligned` and
    `munmap.unaligned` -22. -/
theorem errnos : ebadf = -9 ∧ enoent = -2 ∧ einval = -22 ∧ enxio = -6 := by decide

/-- `readv.1025 -22`: more than 1024 iovecs on an open fd give only EINVAL. -/
theorem readv_1025 {o : Outcome} {k' : Kern}
    (h : readvSpec Kern.init ⟨sysReadv, [0, 0x100, 1025, 0, 0, 0], fun _ => 0⟩ o k') :
    o = .ret { ret := einval } none := by
  have h0 : (0 : Word) ∈ Kern.init.fds := by decide
  simp only [readvSpec, SyscallInput.arg, List.getD, List.getElem?_cons_zero, List.getElem?_cons_succ,
    Option.getD_some, h0, ↓reduceIte] at h
  simp only [show 1024 < (1025 : Word).toNat by decide, ↓reduceIte] at h
  exact h.1

end Examples.LinuxProbe
