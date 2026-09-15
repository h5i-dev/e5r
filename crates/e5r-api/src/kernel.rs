//! System call stubs: what the kernel would have answered, worked out here.
//!
//! # Safety
//!
//! Nothing in this module opens a file, creates a socket, spawns a process,
//! reads a clock, or touches anything at all outside the interpreter's own
//! memory. A stub is an answer, not an action. `write` writes nowhere: it
//! copies the bytes out of the interpreter's memory and records them. `read`
//! hands back bytes the caller put in [`Kernel::input`] and nothing else, and
//! end of file when those run out, because no descriptor exists to read more
//! from. `mmap` and `brk` hand out addresses inside a region the interpreter
//! owns. The clock calls report a fixed second the caller chose. That is the
//! entire list.
//!
//! # Why a call with no stub is refused
//!
//! A stub is a decision about what the kernel would have done, and a wrong one
//! is easy to write and nearly invisible afterwards: a plausible return value
//! propagates through the rest of the run and comes out the other end as an
//! answer nobody doubts. So a number this module does not model is refused by
//! number, the run stops there, and [`Call::returned`] is `None`. Every call
//! that *was* served is recorded too, so a run that took a stub is never
//! mistaken for a run that did not.

use e5r_core::{Addr, Arch};
use e5r_ir::Machine;

/// The most bytes one `read` or `write` moves. A longer transfer is answered
/// short, which is a legal answer for both calls and is what keeps a wild
/// length from trying to allocate the address space.
pub const MAX_TRANSFER: u64 = 1 << 20;

/// `-ENOMEM`, as the kernel returns it: a small negative number in the result
/// register.
const ENOMEM: u64 = (-12i64) as u64;

/// One system call the run reached.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Call {
    /// The instruction that made it.
    pub at: Addr,
    /// The number in the architecture's system call register.
    pub number: u64,
    /// What that number is called, where this table knows a name. A refused
    /// call is named too when the name is known: which call was refused is the
    /// point of refusing rather than guessing.
    pub name: Option<&'static str>,
    /// The six argument registers, in the system call convention's order.
    pub args: [u64; 6],
    /// True when this module has a stub for the number.
    ///
    /// `exit` has a stub and does not return, so `returned` is `None` for it
    /// as well as for a refusal; this is what tells the two apart.
    pub stubbed: bool,
    /// What the stub answered, or `None` when the call did not return: either
    /// it was refused and the run stopped, or it was `exit`.
    pub returned: Option<u64>,
}

impl Call {
    /// True when a stub answered this call rather than the run stopping on it.
    pub fn served(&self) -> bool {
        self.stubbed
    }

    /// How the call reads in a report.
    pub fn describe(&self) -> String {
        let name = self.name.unwrap_or("?");
        match (self.stubbed, self.returned) {
            (true, Some(v)) => format!("{name}({}) = {:#x}", self.number, v),
            (true, None) => format!("{name}({}) did not return", self.number),
            (false, _) => format!("{name}({}) refused: no stub", self.number),
        }
    }
}

/// Bytes a stubbed `write` was handed.
///
/// Nothing was written anywhere. This is the record of what the program tried
/// to send, which for a decryptor or a packer is usually the answer being
/// looked for.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Output {
    /// The descriptor number the program passed, which was not consulted.
    pub fd: u64,
    /// The bytes it asked to send.
    pub bytes: Vec<u8>,
}

/// What the stubs answer with.
#[derive(Debug, Clone)]
pub struct Kernel {
    /// Bytes a stubbed `read` hands back, consumed from the front across the
    /// whole run. When they run out `read` returns zero, which is end of file.
    pub input: Vec<u8>,
    /// Where the region `mmap` and `brk` hand addresses out of starts. Away
    /// from the image and from the stack, so a pointer that came from one of
    /// them is recognizable on sight.
    pub arena: u64,
    /// How large that region is. It bounds `mmap` and `brk` together, so a
    /// program that asks for the world is told no rather than believed.
    pub arena_size: u64,
    /// The second every clock call reports. Fixed, because a run that reads
    /// the clock has to give the same answer twice or it is not evidence.
    pub epoch: u64,
}

impl Default for Kernel {
    fn default() -> Self {
        Kernel {
            input: Vec::new(),
            arena: 0x5000_0000,
            arena_size: 1 << 24,
            // 2020-09-13T12:26:40Z. Any fixed second would do; this one is
            // recent enough that a program checking for an expiry passes.
            epoch: 1_600_000_000,
        }
    }
}

/// What a stub decided.
pub(crate) enum Answer {
    /// The call returns this in the result register.
    Returned(u64),
    /// The program asked to stop, with this status.
    Exited(u64),
    /// There is no stub for this number. The run stops.
    Refused,
}

/// The calls this module models.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Which {
    Read,
    Write,
    Mmap,
    Munmap,
    Brk,
    Exit,
    Time,
    GetTimeOfDay,
    ClockGetTime,
}

/// The stubs' state for one run.
pub(crate) struct Session {
    k: Kernel,
    /// How much of `input` a `read` has already handed over.
    taken: usize,
    /// The next address `mmap` will hand out.
    map_next: u64,
    /// The program break.
    brk: u64,
    /// Everything the stubs recorded.
    pub(crate) output: Vec<Output>,
}

impl Session {
    pub(crate) fn new(k: Kernel) -> Session {
        // The break grows up from the bottom of the arena and mappings come
        // out of the rest, so neither can walk into the other.
        let split = k.arena + k.arena_size / 4;
        Session {
            taken: 0,
            map_next: split,
            brk: k.arena,
            output: Vec::new(),
            k,
        }
    }

    /// Read the call's registers, without deciding anything about it yet.
    pub(crate) fn observe(m: &Machine<'_>, arch: &Arch, at: Addr) -> Call {
        let (number_reg, arg_regs) = convention(arch);
        let number = m.reg(number_reg, 8);
        let mut args = [0u64; 6];
        for (i, r) in arg_regs.iter().enumerate() {
            args[i] = m.reg(*r, 8);
        }
        Call {
            at,
            number,
            name: name_of(arch, number),
            args,
            stubbed: false,
            returned: None,
        }
    }

    /// Answer one call, or refuse it.
    pub(crate) fn serve(&mut self, m: &mut Machine<'_>, arch: &Arch, call: &Call) -> Answer {
        let Some(which) = which(arch, call.number) else {
            return Answer::Refused;
        };
        let a = call.args;
        match which {
            // No descriptor is opened or consulted; the caller's bytes are the
            // only thing there is to read.
            Which::Read => {
                let want = a[2].min(MAX_TRANSFER) as usize;
                let have = self.k.input.len().saturating_sub(self.taken);
                let n = want.min(have);
                if n > 0 {
                    let bytes = self.k.input[self.taken..self.taken + n].to_vec();
                    self.taken += n;
                    m.write_mem(a[1], &bytes);
                }
                Answer::Returned(n as u64)
            }
            Which::Write => {
                let n = a[2].min(MAX_TRANSFER);
                let mut bytes = Vec::with_capacity(n as usize);
                for i in 0..n {
                    bytes.push(m.read_mem(a[1].wrapping_add(i), 1) as u8);
                }
                self.output.push(Output { fd: a[0], bytes });
                Answer::Returned(n)
            }
            // A file-backed mapping would be the contents of a file, and there
            // is no file: that one is refused rather than answered with zeros.
            Which::Mmap => {
                let anonymous = a[4] == u64::MAX || a[4] as i64 == -1;
                if !anonymous {
                    return Answer::Refused;
                }
                let len = a[1].next_multiple_of(0x1000);
                let end = self.k.arena + self.k.arena_size;
                if a[1] == 0 || len > end.saturating_sub(self.map_next) {
                    return Answer::Returned(ENOMEM);
                }
                let at = self.map_next;
                self.map_next += len;
                // Nothing is written: the interpreter reads memory nobody
                // wrote as zero, which is exactly what an anonymous mapping
                // gives, so materializing the pages would cost memory and
                // change no answer.
                Answer::Returned(at)
            }
            // The bytes stay readable afterwards, which a real unmap would not
            // allow. An answer, not an action: a run that reads back through a
            // pointer it unmapped gets the old bytes here and a fault there.
            Which::Munmap => Answer::Returned(0),
            Which::Brk => {
                let limit = self.k.arena + self.k.arena_size / 4;
                if a[0] >= self.k.arena && a[0] <= limit {
                    self.brk = a[0];
                }
                // Linux answers a request it cannot meet with the break it
                // still has, not with an error.
                Answer::Returned(self.brk)
            }
            Which::Exit => Answer::Exited(a[0]),
            Which::Time => {
                if a[0] != 0 {
                    m.write_mem(a[0], &self.k.epoch.to_le_bytes());
                }
                Answer::Returned(self.k.epoch)
            }
            // Both of these fill a two-word structure, and both architectures
            // here are 64-bit, so the layout is the same eight bytes twice.
            // Every clock reports the same fixed second, monotonic included.
            Which::GetTimeOfDay | Which::ClockGetTime => {
                let out = if which == Which::ClockGetTime {
                    a[1]
                } else {
                    a[0]
                };
                if out != 0 {
                    m.write_mem(out, &self.k.epoch.to_le_bytes());
                    m.write_mem(out + 8, &0u64.to_le_bytes());
                }
                Answer::Returned(0)
            }
        }
    }
}

/// Where a system call's number and arguments live, per architecture.
///
/// This is the system call convention, which is not the C one: x86-64 passes
/// the fourth argument in `r10` because `syscall` destroys `rcx`, and AArch64
/// puts the number in `x8` rather than in a register the C convention uses.
fn convention(arch: &Arch) -> (u64, [u64; 6]) {
    match arch {
        Arch::X86_64 => {
            let r = e5r_ir::lift::x86::gpr_offset;
            // rax, then rdi rsi rdx r10 r8 r9.
            (r(0), [r(7), r(6), r(2), r(10), r(8), r(9)])
        }
        _ => {
            let r = e5r_ir::lift::aarch64::gpr_offset;
            (r(8), [r(0), r(1), r(2), r(3), r(4), r(5)])
        }
    }
}

/// The register a system call's result comes back in.
pub(crate) fn result_register(arch: &Arch) -> u64 {
    match arch {
        Arch::X86_64 => e5r_ir::lift::x86::gpr_offset(0),
        _ => e5r_ir::lift::aarch64::gpr_offset(0),
    }
}

/// Which modelled call a number is, if any.
fn which(arch: &Arch, number: u64) -> Option<Which> {
    match arch {
        Arch::X86_64 => Some(match number {
            0 => Which::Read,
            1 => Which::Write,
            9 => Which::Mmap,
            11 => Which::Munmap,
            12 => Which::Brk,
            60 | 231 => Which::Exit,
            96 => Which::GetTimeOfDay,
            201 => Which::Time,
            228 => Which::ClockGetTime,
            _ => return None,
        }),
        // The generic Linux numbering, which AArch64 uses unchanged. There is
        // no `time` call in it: userland reads the clock through
        // `clock_gettime` or the vDSO.
        Arch::AArch64 => Some(match number {
            63 => Which::Read,
            64 => Which::Write,
            93 | 94 => Which::Exit,
            113 => Which::ClockGetTime,
            169 => Which::GetTimeOfDay,
            214 => Which::Brk,
            215 => Which::Munmap,
            222 => Which::Mmap,
            _ => return None,
        }),
        // Another architecture's numbering is a different table, and guessing
        // at it would be exactly the invented answer this module refuses.
        _ => None,
    }
}

/// What a number is called, for the report.
///
/// The modelled calls plus the ones most likely to be the reason a run
/// stopped: a refusal that says `execve(59)` tells an analyst what the code
/// was about to do, and one that says only `59` does not.
fn name_of(arch: &Arch, number: u64) -> Option<&'static str> {
    let table: &[(u64, &'static str)] = match arch {
        Arch::X86_64 => &[
            (0, "read"),
            (1, "write"),
            (2, "open"),
            (3, "close"),
            (5, "fstat"),
            (8, "lseek"),
            (9, "mmap"),
            (10, "mprotect"),
            (11, "munmap"),
            (12, "brk"),
            (13, "rt_sigaction"),
            (16, "ioctl"),
            (19, "readv"),
            (20, "writev"),
            (21, "access"),
            (35, "nanosleep"),
            (39, "getpid"),
            (41, "socket"),
            (42, "connect"),
            (56, "clone"),
            (57, "fork"),
            (59, "execve"),
            (60, "exit"),
            (62, "kill"),
            (63, "uname"),
            (87, "unlink"),
            (96, "gettimeofday"),
            (101, "ptrace"),
            (158, "arch_prctl"),
            (165, "mount"),
            (201, "time"),
            (202, "futex"),
            (228, "clock_gettime"),
            (231, "exit_group"),
            (257, "openat"),
        ],
        Arch::AArch64 => &[
            (29, "ioctl"),
            (35, "unlinkat"),
            (48, "faccessat"),
            (56, "openat"),
            (57, "close"),
            (59, "pipe2"),
            (62, "lseek"),
            (63, "read"),
            (64, "write"),
            (65, "readv"),
            (66, "writev"),
            (80, "fstat"),
            (93, "exit"),
            (94, "exit_group"),
            (98, "futex"),
            (101, "nanosleep"),
            (113, "clock_gettime"),
            (117, "ptrace"),
            (129, "kill"),
            (134, "rt_sigaction"),
            (160, "uname"),
            (169, "gettimeofday"),
            (172, "getpid"),
            (198, "socket"),
            (203, "connect"),
            (214, "brk"),
            (215, "munmap"),
            (220, "clone"),
            (221, "execve"),
            (222, "mmap"),
            (226, "mprotect"),
            (40, "mount"),
        ],
        _ => &[],
    };
    table
        .iter()
        .find(|(n, _)| *n == number)
        .map(|(_, name)| *name)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn the_two_numberings_are_not_the_same_table() {
        // Number 1 is `write` on x86-64 and something unmodelled on AArch64.
        // Getting these crossed would answer the wrong call silently, which is
        // the failure this whole module is arranged against.
        assert_eq!(which(&Arch::X86_64, 1), Some(Which::Write));
        assert_eq!(which(&Arch::AArch64, 1), None);
        assert_eq!(which(&Arch::AArch64, 64), Some(Which::Write));
        assert_eq!(which(&Arch::X86_64, 64), None);
    }

    #[test]
    fn an_unmodelled_number_is_refused_by_number() {
        assert_eq!(which(&Arch::X86_64, 59), None);
        assert_eq!(name_of(&Arch::X86_64, 59), Some("execve"));
        assert_eq!(which(&Arch::AArch64, 221), None);
        assert_eq!(name_of(&Arch::AArch64, 221), Some("execve"));
    }

    #[test]
    fn every_modelled_number_has_a_name() {
        for arch in [Arch::X86_64, Arch::AArch64] {
            for n in 0..300u64 {
                if which(&arch, n).is_some() {
                    assert!(name_of(&arch, n).is_some(), "{arch:?} {n} has no name");
                }
            }
        }
    }
}
