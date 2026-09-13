//! The instruction set the IR is written in.
//!
//! Modelled on Ghidra's p-code: every operation reads typed storage locations
//! and writes at most one. Two properties matter and both are deliberate.
//!
//! Operations have no side effects beyond their output. A machine instruction
//! that sets flags becomes several IR operations, one per flag, so nothing is
//! implicit and dataflow does not have to know which instruction touches what.
//!
//! Operations are sized. `IntAdd` on four bytes and on eight are the same
//! opcode with different varnode sizes, which keeps the opcode list short
//! enough to implement completely.

use std::fmt;

use serde::Serialize;

/// Where a value lives.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize)]
#[serde(rename_all = "lowercase")]
pub enum Space {
    /// A literal. The offset is the value.
    Const,
    /// The machine's register file. The offset is a byte position in it, so
    /// `eax` and `rax` overlap the way the hardware says they do.
    Register,
    /// Addressable memory. The offset is an address.
    Ram,
    /// A temporary introduced by lifting, invisible to the machine.
    Unique,
}

/// A storage location: a space, an offset in it, and a size in bytes.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize)]
pub struct Varnode {
    /// Which space.
    pub space: Space,
    /// Where in it.
    pub offset: u64,
    /// How many bytes.
    pub size: u8,
}

impl Varnode {
    /// A literal value.
    pub const fn constant(value: u64, size: u8) -> Varnode {
        Varnode {
            space: Space::Const,
            offset: value,
            size,
        }
    }

    /// A register at a byte offset in the register file.
    pub const fn register(offset: u64, size: u8) -> Varnode {
        Varnode {
            space: Space::Register,
            offset,
            size,
        }
    }

    /// A lifting temporary.
    pub const fn temp(id: u64, size: u8) -> Varnode {
        Varnode {
            space: Space::Unique,
            offset: id,
            size,
        }
    }

    /// True when this is a literal.
    pub const fn is_const(self) -> bool {
        matches!(self.space, Space::Const)
    }

    /// The literal's value, if it is one.
    pub const fn value(self) -> Option<u64> {
        if self.is_const() {
            Some(self.offset)
        } else {
            None
        }
    }

    /// A mask covering this varnode's bits.
    pub const fn mask(self) -> u64 {
        match self.size {
            0 => 0,
            1..=7 => (1u64 << (self.size as u32 * 8)) - 1,
            _ => u64::MAX,
        }
    }

    /// True when two varnodes name overlapping storage.
    pub fn overlaps(self, other: Varnode) -> bool {
        if self.space != other.space || self.space == Space::Const {
            return false;
        }
        let a = self.offset..self.offset.saturating_add(self.size as u64);
        let b = other.offset..other.offset.saturating_add(other.size as u64);
        a.start < b.end && b.start < a.end
    }
}

impl fmt::Display for Varnode {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.space {
            Space::Const => write!(f, "{:#x}:{}", self.offset, self.size),
            Space::Register => write!(f, "r[{:#x}]:{}", self.offset, self.size),
            Space::Ram => write!(f, "ram[{:#x}]:{}", self.offset, self.size),
            Space::Unique => write!(f, "u{}:{}", self.offset, self.size),
        }
    }
}

/// What an operation does.
///
/// Every arithmetic opcode is unsigned unless its name says otherwise, because
/// the machine's registers hold bits and signedness is a property of the
/// operation rather than of the storage.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize)]
#[serde(rename_all = "snake_case")]
pub enum Op {
    /// `out = in0`, with truncation or the identity.
    Copy,
    /// `out = *in0`, reading `out.size` bytes.
    Load,
    /// `*in0 = in1`.
    Store,

    /// Unconditional transfer to `in0`, which is a constant address.
    Branch,
    /// Transfer to `in0` when `in1` is non-zero.
    CBranch,
    /// Transfer to the address in `in0`.
    BranchInd,
    /// Call `in0`.
    Call,
    /// Call the address in `in0`.
    CallInd,
    /// Return to the address in `in0`.
    Return,

    /// Integer addition.
    IntAdd,
    /// Integer subtraction.
    IntSub,
    /// Integer multiplication, low half.
    IntMul,
    /// Unsigned division.
    IntDiv,
    /// Signed division.
    IntSDiv,
    /// Unsigned remainder.
    IntRem,
    /// Signed remainder.
    IntSRem,
    /// Bitwise and.
    IntAnd,
    /// Bitwise or.
    IntOr,
    /// Bitwise exclusive or.
    IntXor,
    /// Bitwise complement.
    IntNot,
    /// Two's complement negation.
    IntNegate,
    /// Shift left.
    IntLeft,
    /// Logical shift right.
    IntRight,
    /// Arithmetic shift right.
    IntSRight,
    /// Equality, producing one byte.
    IntEqual,
    /// Inequality.
    IntNotEqual,
    /// Unsigned less than.
    IntLess,
    /// Signed less than.
    IntSLess,
    /// Unsigned less than or equal.
    IntLessEqual,
    /// Signed less than or equal.
    IntSLessEqual,
    /// Unsigned carry out of an addition.
    IntCarry,
    /// Signed overflow of an addition.
    IntSCarry,
    /// Signed overflow of a subtraction.
    IntSBorrow,
    /// Zero extension.
    IntZExt,
    /// Sign extension.
    IntSExt,
    /// Count set bits.
    PopCount,
    /// Count leading zeros.
    LzCount,

    /// Logical and of one-byte booleans.
    BoolAnd,
    /// Logical or.
    BoolOr,
    /// Logical exclusive or.
    BoolXor,
    /// Logical not.
    BoolNot,

    /// Concatenate: `out = (in0 << (in1.size * 8)) | in1`.
    Piece,
    /// Extract: `out = in0 >> (in1 * 8)`, truncated to `out.size`.
    SubPiece,

    /// Something the lifter does not model. The output, if any, becomes
    /// unknown. Honest rather than wrong.
    Unimplemented,
}

impl Op {
    /// True when this ends a block.
    pub fn is_branch(self) -> bool {
        matches!(
            self,
            Op::Branch | Op::CBranch | Op::BranchInd | Op::Return | Op::Call | Op::CallInd
        )
    }

    /// How many inputs the operation takes.
    pub fn arity(self) -> usize {
        match self {
            Op::Copy
            | Op::Load
            | Op::IntNot
            | Op::IntNegate
            | Op::IntZExt
            | Op::IntSExt
            | Op::BoolNot
            | Op::PopCount
            | Op::LzCount
            | Op::Branch
            | Op::BranchInd
            | Op::Call
            | Op::CallInd
            | Op::Return => 1,
            Op::Unimplemented => 0,
            _ => 2,
        }
    }

    /// The symbol shown when an operation is printed.
    pub fn as_str(self) -> &'static str {
        match self {
            Op::Copy => "copy",
            Op::Load => "load",
            Op::Store => "store",
            Op::Branch => "branch",
            Op::CBranch => "cbranch",
            Op::BranchInd => "branchind",
            Op::Call => "call",
            Op::CallInd => "callind",
            Op::Return => "return",
            Op::IntAdd => "+",
            Op::IntSub => "-",
            Op::IntMul => "*",
            Op::IntDiv => "/u",
            Op::IntSDiv => "/s",
            Op::IntRem => "%u",
            Op::IntSRem => "%s",
            Op::IntAnd => "&",
            Op::IntOr => "|",
            Op::IntXor => "^",
            Op::IntNot => "~",
            Op::IntNegate => "neg",
            Op::IntLeft => "<<",
            Op::IntRight => ">>u",
            Op::IntSRight => ">>s",
            Op::IntEqual => "==",
            Op::IntNotEqual => "!=",
            Op::IntLess => "<u",
            Op::IntSLess => "<s",
            Op::IntLessEqual => "<=u",
            Op::IntSLessEqual => "<=s",
            Op::IntCarry => "carry",
            Op::IntSCarry => "scarry",
            Op::IntSBorrow => "sborrow",
            Op::IntZExt => "zext",
            Op::IntSExt => "sext",
            Op::PopCount => "popcount",
            Op::LzCount => "lzcount",
            Op::BoolAnd => "&&",
            Op::BoolOr => "||",
            Op::BoolXor => "^^",
            Op::BoolNot => "!",
            Op::Piece => "piece",
            Op::SubPiece => "subpiece",
            Op::Unimplemented => "unimplemented",
        }
    }
}

impl fmt::Display for Op {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.as_str())
    }
}

/// The most inputs any operation takes.
pub const MAX_INPUTS: usize = 3;

/// One IR operation.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct IrOp {
    /// Which operation.
    pub op: Op,
    /// Where the result goes, if anywhere.
    pub out: Option<Varnode>,
    inputs: [Varnode; MAX_INPUTS],
    n: u8,
    /// The machine instruction this came from, so a result can be traced back.
    pub addr: r12e_core::Addr,
}

impl IrOp {
    /// Build an operation with no inputs yet.
    pub fn new(addr: r12e_core::Addr, op: Op, out: Option<Varnode>) -> IrOp {
        IrOp {
            op,
            out,
            inputs: [Varnode::constant(0, 1); MAX_INPUTS],
            n: 0,
            addr,
        }
    }

    /// Add an input.
    pub fn with(mut self, v: Varnode) -> IrOp {
        if (self.n as usize) < MAX_INPUTS {
            self.inputs[self.n as usize] = v;
            self.n += 1;
        }
        self
    }

    /// The inputs.
    pub fn inputs(&self) -> &[Varnode] {
        &self.inputs[..self.n as usize]
    }

    /// One input, or `None` if there are fewer.
    pub fn input(&self, n: usize) -> Option<Varnode> {
        self.inputs().get(n).copied()
    }
}

impl fmt::Display for IrOp {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if let Some(out) = self.out {
            write!(f, "{out} = ")?;
        }
        write!(f, "{}", self.op)?;
        for (n, i) in self.inputs().iter().enumerate() {
            write!(f, "{}{i}", if n == 0 { " " } else { ", " })?;
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn overlapping_registers_are_detected() {
        // eax and rax share storage; that is the whole reason the register
        // space is byte-addressed rather than a list of names.
        let rax = Varnode::register(0, 8);
        let eax = Varnode::register(0, 4);
        let rcx = Varnode::register(8, 8);
        assert!(rax.overlaps(eax));
        assert!(eax.overlaps(rax));
        assert!(!rax.overlaps(rcx));
    }

    #[test]
    fn constants_never_overlap() {
        let a = Varnode::constant(5, 8);
        assert!(!a.overlaps(a));
    }

    #[test]
    fn masks_match_the_size() {
        assert_eq!(Varnode::constant(0, 1).mask(), 0xff);
        assert_eq!(Varnode::constant(0, 4).mask(), 0xffff_ffff);
        assert_eq!(Varnode::constant(0, 8).mask(), u64::MAX);
    }

    #[test]
    fn arity_matches_what_the_interpreter_reads() {
        assert_eq!(Op::IntAdd.arity(), 2);
        assert_eq!(Op::Copy.arity(), 1);
        assert_eq!(Op::Unimplemented.arity(), 0);
    }
}
