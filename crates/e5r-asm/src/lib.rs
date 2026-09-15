//! Assembler: mnemonics and operands to bytes, one instruction at a time.
//!
//! The inverse of `e5r-arch`, and built on top of it rather than beside it.
//! Text is parsed into the same [`Insn`] the decoders produce and the encoder
//! then works from that, so the property that matters for patching falls out
//! of the structure: a line copied from `e5r disas` assembles back to the
//! bytes it came from.
//!
//! There is no linker here, no relocation, no object writer and no macro
//! language. One instruction, one address, one answer, and a typed refusal
//! everywhere else. `e5r patch` needs exactly that and nothing more.
//!
//! ```
//! use e5r_asm::assemble;
//! use e5r_core::{Addr, Arch};
//!
//! let e = assemble(&Arch::X86_64, "mov eax, 0x1", Addr(0x1000)).unwrap();
//! assert_eq!(e.bytes(), &[0xb8, 0x01, 0x00, 0x00, 0x00]);
//! ```
//!
//! One caveat on the text accepted: AArch64 branch targets must be written
//! `0x1000`, not objdump's bare `1000`, because a bare number reads as decimal
//! everywhere else in the grammar and a silently decimal branch target is the
//! kind of mistake this crate exists to refuse.

#![forbid(unsafe_code)]
#![warn(missing_docs)]

pub mod aarch64;
pub mod error;
pub mod lex;
pub mod parse;
pub mod x86;

use std::fmt;

use e5r_arch::insn::Insn;
use e5r_core::{Addr, Arch};

pub use error::AsmError;
pub use parse::parse;

/// The longest encoding either architecture has, which is x86's fifteen-byte
/// limit. AArch64 is always four.
pub const MAX_INSN: usize = 15;

/// The bytes one instruction encodes to.
///
/// Inline rather than a `Vec`: an assembler that allocates per instruction is
/// the wrong shape for filling a patch region with no-ops.
#[derive(Clone, Copy, PartialEq, Eq)]
pub struct Encoded {
    buf: [u8; MAX_INSN],
    len: u8,
}

impl Encoded {
    /// The encoded bytes, in memory order.
    pub fn bytes(&self) -> &[u8] {
        &self.buf[..self.len as usize]
    }

    /// How many bytes the instruction occupies.
    pub fn len(&self) -> usize {
        self.len as usize
    }

    /// True when nothing was encoded, which no successful encode produces.
    pub fn is_empty(&self) -> bool {
        self.len == 0
    }

    /// A fixed-width little-endian word, which is every A64 encoding.
    pub(crate) fn from_u32_le(w: u32) -> Encoded {
        let mut buf = [0u8; MAX_INSN];
        buf[..4].copy_from_slice(&w.to_le_bytes());
        Encoded { buf, len: 4 }
    }

    /// Bytes gathered by the variable-length x86 path.
    pub(crate) fn from_slice(bytes: &[u8]) -> Result<Encoded, AsmError> {
        if bytes.len() > MAX_INSN {
            return Err(AsmError::TooLong {
                what: "encoded instruction length",
                len: bytes.len(),
                limit: MAX_INSN,
            });
        }
        let mut buf = [0u8; MAX_INSN];
        buf[..bytes.len()].copy_from_slice(bytes);
        Ok(Encoded {
            buf,
            len: bytes.len() as u8,
        })
    }
}

impl fmt::Debug for Encoded {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for b in self.bytes() {
            write!(f, "{b:02x}")?;
        }
        Ok(())
    }
}

/// Assemble one instruction for `arch`, as if it were placed at `addr`.
///
/// The address matters because a branch or a pc-relative operand encodes a
/// displacement from where the instruction sits, so the same text at a
/// different address is different bytes.
pub fn assemble(arch: &Arch, text: &str, addr: Addr) -> Result<Encoded, AsmError> {
    let insn = parse::parse(arch, text, addr)?;
    encode(arch, &insn)
}

/// Encode an instruction that is already in [`Insn`] shape.
///
/// This is the path a caller takes when it has decoded an instruction, changed
/// one operand, and wants the bytes back.
pub fn encode(arch: &Arch, insn: &Insn) -> Result<Encoded, AsmError> {
    match arch {
        Arch::AArch64 => aarch64::encode(insn),
        Arch::X86_64 => x86::encode(insn),
        other => Err(AsmError::UnsupportedArch(format!("{other:?}"))),
    }
}

/// Assemble several lines, each at the address the one before it ended at.
///
/// Blank lines and comment-only lines encode to nothing, so a pasted block of
/// disassembly with its annotations still assembles.
pub fn assemble_all(arch: &Arch, text: &str, addr: Addr) -> Result<Vec<u8>, AsmError> {
    let mut out = Vec::new();
    let mut at = addr;
    for line in text.lines() {
        match assemble(arch, line, at) {
            Ok(e) => {
                out.extend_from_slice(e.bytes());
                at = at.wrapping_offset(e.len() as i64);
            }
            // A line that holds only a comment is not an error; it is what a
            // pasted listing is full of.
            Err(AsmError::Empty) => {}
            Err(e) => return Err(e),
        }
    }
    Ok(out)
}

/// Fill exactly `len` bytes with no-ops.
///
/// Padding is a patching primitive rather than a convenience: replacing a long
/// instruction with a short one leaves a hole, and a hole filled with anything
/// but a no-op is a crash waiting for the fall-through path.
pub fn pad(arch: &Arch, len: usize) -> Result<Vec<u8>, AsmError> {
    match arch {
        Arch::AArch64 => {
            if len % 4 != 0 {
                return Err(AsmError::Unaligned {
                    what: "padding length",
                    value: len as i64,
                    align: 4,
                });
            }
            let mut out = Vec::with_capacity(len);
            for _ in 0..len / 4 {
                out.extend_from_slice(&aarch64::NOP.to_le_bytes());
            }
            Ok(out)
        }
        Arch::X86_64 => Ok(x86::padding(len)),
        other => Err(AsmError::UnsupportedArch(format!("{other:?}"))),
    }
}
