//! The typed refusals.
//!
//! An assembler that guesses is worse than one that stops, because a patch
//! that assembles into the wrong instruction is discovered by the program
//! crashing. Every path that cannot encode says what it could not encode.

use std::fmt;

/// The longest instruction text the assembler will look at.
///
/// Every count read out of the text is bounded before anything is allocated,
/// and this is the outermost of those bounds.
pub const MAX_TEXT: usize = 512;

/// The most tokens one instruction may lex to.
pub const MAX_TOKENS: usize = 96;

/// Why a piece of text could not be turned into bytes.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub enum AsmError {
    /// The text held no mnemonic.
    Empty,
    /// The text is longer than [`MAX_TEXT`], or lexes to more than
    /// [`MAX_TOKENS`] tokens.
    TooLong {
        /// What was measured.
        what: &'static str,
        /// How much of it there was.
        len: usize,
        /// The most that is accepted.
        limit: usize,
    },
    /// A character or token that cannot appear here.
    Syntax {
        /// Byte offset into the text.
        at: usize,
        /// What was found, or what was expected instead.
        what: String,
    },
    /// The mnemonic is not one this assembler encodes.
    UnknownMnemonic(String),
    /// The name is not a register of this architecture.
    UnknownRegister(String),
    /// The mnemonic is known, but not with these operands.
    UnsupportedForm {
        /// The mnemonic that was asked for.
        mnemonic: String,
        /// Which part of the form is the problem.
        detail: &'static str,
    },
    /// The architecture has no encoder here.
    UnsupportedArch(String),
    /// A memory operand carries no width and no register operand implies one.
    UnsizedOperand {
        /// The mnemonic that was asked for.
        mnemonic: String,
    },
    /// A value does not fit the field that has to hold it.
    Range {
        /// Which field.
        what: &'static str,
        /// The value that was asked for.
        value: i64,
        /// Lowest value the field encodes.
        low: i64,
        /// Highest value the field encodes.
        high: i64,
    },
    /// A value fits but is not a multiple the field can scale to.
    Unaligned {
        /// Which field.
        what: &'static str,
        /// The value that was asked for.
        value: i64,
        /// The multiple it has to be.
        align: u32,
    },
    /// A branch target is out of reach of the encoding.
    ///
    /// Named separately from [`AsmError::Range`] because a truncated
    /// displacement is the one mistake an assembler must never make quietly.
    BranchRange {
        /// The mnemonic that was asked for.
        mnemonic: String,
        /// Where the branch is.
        from: u64,
        /// Where it was asked to go.
        to: u64,
        /// The most negative displacement the encoding holds.
        low: i64,
        /// The most positive displacement the encoding holds.
        high: i64,
    },
    /// A bit pattern no immediate field of this architecture can express.
    NoEncoding {
        /// The mnemonic that was asked for.
        mnemonic: String,
        /// The value that has no encoding.
        value: u64,
        /// Which family of immediates was tried.
        what: &'static str,
    },
}

impl fmt::Display for AsmError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            AsmError::Empty => f.write_str("no instruction in the text"),
            AsmError::TooLong { what, len, limit } => {
                write!(f, "{what} is {len}, the limit is {limit}")
            }
            AsmError::Syntax { at, what } => write!(f, "syntax error at byte {at}: {what}"),
            AsmError::UnknownMnemonic(m) => write!(f, "unknown mnemonic `{m}`"),
            AsmError::UnknownRegister(r) => write!(f, "unknown register `{r}`"),
            AsmError::UnsupportedForm { mnemonic, detail } => {
                write!(f, "cannot encode `{mnemonic}`: {detail}")
            }
            AsmError::UnsupportedArch(a) => write!(f, "no assembler for {a}"),
            AsmError::UnsizedOperand { mnemonic } => write!(
                f,
                "`{mnemonic}` needs an operand size: write `byte ptr`, `word ptr`, \
                 `dword ptr` or `qword ptr` before the memory operand"
            ),
            AsmError::Range {
                what,
                value,
                low,
                high,
            } => write!(f, "{what} {value} is outside {low}..={high}"),
            AsmError::Unaligned { what, value, align } => {
                write!(f, "{what} {value} is not a multiple of {align}")
            }
            AsmError::BranchRange {
                mnemonic,
                from,
                to,
                low,
                high,
            } => write!(
                f,
                "`{mnemonic}` at {from:#x} cannot reach {to:#x}: the encoding holds \
                 a displacement of {low}..={high} bytes"
            ),
            AsmError::NoEncoding {
                mnemonic,
                value,
                what,
            } => write!(f, "`{mnemonic}`: {value:#x} is not a {what}"),
        }
    }
}

impl std::error::Error for AsmError {}
