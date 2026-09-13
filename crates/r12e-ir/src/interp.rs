//! An interpreter for the IR.
//!
//! This exists to test the lifters, and that is not a secondary use. A lifter
//! is a translation between two semantics and there is no way to check one by
//! reading it: the only honest test is to run the original and the translation
//! and compare. Ghidra's PCodeTest works exactly this way, and it is why its
//! forty processor specifications are trustworthy.
//!
//! It is a plain interpreter, not a symbolic one. Unknown memory reads as zero
//! and are reported, so a test can tell a real answer from one the model
//! invented.

use std::collections::BTreeMap;

use r12e_core::{Addr, MemoryMap};

use crate::op::{IrOp, Op, Space, Varnode};

/// Why execution stopped.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Stop {
    /// The program returned.
    Returned,
    /// The step budget ran out, which is how a loop that does not terminate
    /// is reported rather than hung on.
    Budget,
    /// An operation the lifter did not model was reached.
    Unimplemented(Addr),
    /// A branch went somewhere with no code.
    NoCode(Addr),
    /// A call was reached and calls are not being followed.
    Call(Addr),
    /// Division by zero.
    DivideByZero(Addr),
}

/// The machine the IR runs on.
pub struct Machine<'a> {
    /// The register file, by byte offset. Sparse, because most of it is never
    /// touched and a dense array would be mostly zeros.
    registers: BTreeMap<u64, u8>,
    /// Writable memory, overlaying the image.
    memory: BTreeMap<u64, u8>,
    /// The image, read when `memory` has nothing at an address.
    image: Option<&'a MemoryMap>,
    /// Lifting temporaries, cleared between machine instructions.
    temps: BTreeMap<u64, u64>,
    /// Addresses read that nothing had written.
    pub unknown_reads: Vec<Addr>,
    /// How many operations may run before [`Stop::Budget`].
    pub budget: u64,
}

impl<'a> Machine<'a> {
    /// A machine with nothing in it.
    pub fn new() -> Machine<'a> {
        Machine {
            registers: BTreeMap::new(),
            memory: BTreeMap::new(),
            image: None,
            temps: BTreeMap::new(),
            unknown_reads: Vec::new(),
            budget: 1 << 22,
        }
    }

    /// A machine that can read the program's own bytes.
    pub fn over(image: &'a MemoryMap) -> Machine<'a> {
        Machine {
            image: Some(image),
            ..Machine::new()
        }
    }

    /// Read a register as an integer.
    pub fn reg(&self, offset: u64, size: u8) -> u64 {
        let mut v = 0u64;
        for i in 0..size as u64 {
            let b = self.registers.get(&(offset + i)).copied().unwrap_or(0);
            v |= (b as u64) << (i * 8);
        }
        v
    }

    /// Write a register.
    pub fn set_reg(&mut self, offset: u64, size: u8, value: u64) {
        for i in 0..size as u64 {
            self.registers.insert(offset + i, (value >> (i * 8)) as u8);
        }
    }

    /// Put bytes in memory.
    pub fn write_mem(&mut self, at: u64, bytes: &[u8]) {
        for (i, b) in bytes.iter().enumerate() {
            self.memory.insert(at + i as u64, *b);
        }
    }

    /// Read bytes from memory, falling back to the image.
    pub fn read_mem(&mut self, at: u64, size: u8) -> u64 {
        let mut v = 0u64;
        for i in 0..size as u64 {
            let addr = at.wrapping_add(i);
            let b = match self.memory.get(&addr) {
                Some(b) => *b,
                None => match self.image.and_then(|m| m.slice(Addr(addr), 1)) {
                    Some(s) => s[0],
                    None => {
                        self.unknown_reads.push(Addr(addr));
                        0
                    }
                },
            };
            v |= (b as u64) << (i * 8);
        }
        v
    }

    fn read(&mut self, v: Varnode) -> u64 {
        let raw = match v.space {
            Space::Const => v.offset,
            Space::Register => self.reg(v.offset, v.size),
            // A promoted slot is storage of its own; the interpreter runs
            // unpromoted code, so this exists for completeness.
            Space::Unique | Space::Stack => self.temps.get(&v.offset).copied().unwrap_or(0),
            Space::Ram => self.read_mem(v.offset, v.size),
        };
        raw & v.mask()
    }

    fn write(&mut self, v: Varnode, value: u64) {
        let value = value & v.mask();
        match v.space {
            Space::Const => {}
            Space::Register => self.set_reg(v.offset, v.size, value),
            Space::Unique | Space::Stack => {
                self.temps.insert(v.offset, value);
            }
            Space::Ram => {
                for i in 0..v.size as u64 {
                    self.memory.insert(v.offset + i, (value >> (i * 8)) as u8);
                }
            }
        }
    }

    /// Clear the lifting temporaries, which do not live across a machine
    /// instruction.
    pub fn end_instruction(&mut self) {
        self.temps.clear();
    }
}

impl Default for Machine<'_> {
    fn default() -> Self {
        Machine::new()
    }
}

/// The sign bit of the low `size` bytes of `v`.
fn sign_bit(v: u64, size: u8) -> bool {
    if size == 0 || size > 8 {
        return false;
    }
    v >> (size as u32 * 8 - 1) & 1 == 1
}

/// Sign-extend the low `size` bytes of `v`.
fn sext(v: u64, size: u8) -> i64 {
    match size {
        0 => 0,
        1..=7 => {
            let bits = size as u32 * 8;
            let shift = 64 - bits;
            ((v << shift) as i64) >> shift
        }
        _ => v as i64,
    }
}

/// What one operation did.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Step {
    /// Carry on with the next operation.
    Next,
    /// Continue at this machine address.
    Jump(Addr),
    /// Enter a call at this address.
    Call(Addr),
    /// Return to this address.
    Leave(Addr),
    /// Stop.
    Halt(Stop),
}

/// Run one operation.
pub fn step(m: &mut Machine<'_>, ir: &IrOp) -> Step {
    let a = |m: &mut Machine<'_>| ir.input(0).map(|v| m.read(v)).unwrap_or(0);

    match ir.op {
        Op::Unimplemented => return Step::Halt(Stop::Unimplemented(ir.addr)),
        Op::Branch => {
            let Some(t) = ir.input(0).and_then(|v| v.value()) else {
                return Step::Halt(Stop::Unimplemented(ir.addr));
            };
            return Step::Jump(Addr(t));
        }
        Op::CBranch => {
            let cond = ir.input(1).map(|v| m.read(v)).unwrap_or(0);
            if cond != 0 {
                let Some(t) = ir.input(0).and_then(|v| v.value()) else {
                    return Step::Halt(Stop::Unimplemented(ir.addr));
                };
                return Step::Jump(Addr(t));
            }
            return Step::Next;
        }
        Op::BranchInd | Op::Return => {
            let t = a(m);
            return if ir.op == Op::Return {
                Step::Leave(Addr(t))
            } else {
                Step::Jump(Addr(t))
            };
        }
        Op::Call | Op::CallInd => {
            let t = a(m);
            return Step::Call(Addr(t));
        }
        _ => {}
    }

    let out = match ir.out {
        Some(o) => o,
        // An operation with no output and no branch is a store or nothing.
        None => {
            if ir.op == Op::Store {
                let (Some(addr), Some(value)) = (ir.input(0), ir.input(1)) else {
                    return Step::Next;
                };
                let at = m.read(addr);
                let v = m.read(value);
                for i in 0..value.size as u64 {
                    m.memory.insert(at.wrapping_add(i), (v >> (i * 8)) as u8);
                }
            }
            return Step::Next;
        }
    };

    let x = ir.input(0).map(|v| m.read(v)).unwrap_or(0);
    let xs = ir.input(0).map(|v| sext(m.read(v), v.size)).unwrap_or(0);
    let y = ir.input(1).map(|v| m.read(v)).unwrap_or(0);
    let ys = ir.input(1).map(|v| sext(m.read(v), v.size)).unwrap_or(0);

    let value = match ir.op {
        Op::Copy => x,
        Op::Load => {
            let size = out.size;
            m.read_mem(x, size)
        }
        Op::IntAdd => x.wrapping_add(y),
        Op::IntSub => x.wrapping_sub(y),
        Op::IntMul => x.wrapping_mul(y),
        Op::IntDiv
        | Op::IntRem
        | Op::IntSDiv
        | Op::IntSRem
        | Op::IntDiv128
        | Op::IntRem128
        | Op::IntSDiv128
        | Op::IntSRem128
            if divisor(ir, m) == 0 =>
        {
            return Step::Halt(Stop::DivideByZero(ir.addr));
        }
        Op::IntDiv => x / y,
        Op::IntRem => x % y,
        Op::IntSDiv => xs.wrapping_div(ys) as u64,
        Op::IntSRem => xs.wrapping_rem(ys) as u64,
        Op::IntAnd => x & y,
        Op::IntOr => x | y,
        Op::IntXor => x ^ y,
        Op::IntNot => !x,
        Op::IntNegate => x.wrapping_neg(),
        // A shift past the operand's width produces zero, not the wrap a Rust
        // shift would give.
        Op::IntLeft => {
            let bits = ir.input(0).map(|v| v.size as u64 * 8).unwrap_or(64);
            if y >= bits { 0 } else { x << y }
        }
        Op::IntRight => {
            let bits = ir.input(0).map(|v| v.size as u64 * 8).unwrap_or(64);
            if y >= bits { 0 } else { x >> y }
        }
        Op::IntSRight => {
            let bits = ir.input(0).map(|v| v.size as u64 * 8).unwrap_or(64);
            if y >= bits {
                if xs < 0 { u64::MAX } else { 0 }
            } else {
                (xs >> y) as u64
            }
        }
        Op::IntEqual => (x == y) as u64,
        Op::IntNotEqual => (x != y) as u64,
        Op::IntLess => (x < y) as u64,
        Op::IntSLess => (xs < ys) as u64,
        Op::IntLessEqual => (x <= y) as u64,
        Op::IntSLessEqual => (xs <= ys) as u64,
        // A carry out happened when the truncated sum came out below either
        // addend, which is the only test that works at every width.
        Op::IntCarry => {
            let mask = mask_of(ir, 0);
            ((x.wrapping_add(y) & mask) < x) as u64
        }
        // Signed overflow from the sign bits. Comparing a sign-extended result
        // against the true one only works below 64 bits, where the true result
        // still fits; at 64 bits it can never differ and the flag was always
        // false.
        Op::IntSCarry => {
            let size = ir.input(0).map(|v| v.size).unwrap_or(8);
            let sum = x.wrapping_add(y);
            (sign_bit(x, size) == sign_bit(y, size) && sign_bit(sum, size) != sign_bit(x, size))
                as u64
        }
        Op::IntSBorrow => {
            let size = ir.input(0).map(|v| v.size).unwrap_or(8);
            let d = x.wrapping_sub(y);
            (sign_bit(x, size) != sign_bit(y, size) && sign_bit(d, size) != sign_bit(x, size))
                as u64
        }
        // The half of a product that does not fit. x86's `mul` writes it and
        // AArch64's `umulh` reads it, so it is an operation rather than
        // something a lifter can approximate.
        Op::IntMulHigh => {
            let bits = ir.input(0).map(|v| v.size as u32 * 8).unwrap_or(64);
            ((x as u128 * y as u128) >> bits) as u64
        }
        Op::IntSMulHigh => {
            let bits = ir.input(0).map(|v| v.size as u32 * 8).unwrap_or(64);
            ((xs as i128 * ys as i128) >> bits) as u64
        }
        // A double-width dividend, which x86's one-operand divide needs. The
        // third input is the divisor; the first two are the halves.
        Op::IntDiv128 | Op::IntRem128 | Op::IntSDiv128 | Op::IntSRem128 => {
            let bits = ir.input(1).map(|v| v.size as u32 * 8).unwrap_or(64);
            let d = ir.input(2).map(|v| m.read(v)).unwrap_or(0);
            let size = ir.input(1).map(|v| v.size).unwrap_or(8);
            match ir.op {
                Op::IntDiv128 => {
                    let n = ((x as u128) << bits) | y as u128;
                    (n / d as u128) as u64
                }
                Op::IntRem128 => {
                    let n = ((x as u128) << bits) | y as u128;
                    (n % d as u128) as u64
                }
                Op::IntSDiv128 => {
                    let n = sext128((x as u128) << bits | y as u128, bits * 2);
                    (n.wrapping_div(sext(d, size) as i128)) as u64
                }
                _ => {
                    let n = sext128((x as u128) << bits | y as u128, bits * 2);
                    (n.wrapping_rem(sext(d, size) as i128)) as u64
                }
            }
        }
        // Floating point, at the width of the operands. The bits are the
        // value; nothing here reinterprets a pattern it was not given.
        Op::FloatAdd
        | Op::FloatSub
        | Op::FloatMul
        | Op::FloatDiv
        | Op::FloatMax
        | Op::FloatMin
        | Op::FloatNeg
        | Op::FloatAbs
        | Op::FloatSqrt
        | Op::FloatTrunc
        | Op::FloatRound
        | Op::FloatCeil
        | Op::FloatFloor => {
            // A single precision result is computed in single precision, so
            // the rounding happens where the machine does it.
            if out.size == 4 {
                let a = as_f32(x);
                let c = as_f32(y);
                let r = match ir.op {
                    Op::FloatAdd => a + c,
                    Op::FloatSub => a - c,
                    Op::FloatMul => a * c,
                    Op::FloatDiv => a / c,
                    Op::FloatMax => a.max(c),
                    Op::FloatMin => a.min(c),
                    Op::FloatNeg => -a,
                    Op::FloatAbs => a.abs(),
                    Op::FloatSqrt => a.sqrt(),
                    Op::FloatTrunc => a.trunc(),
                    Op::FloatRound => round_ties_even(a as f64) as f32,
                    Op::FloatCeil => a.ceil(),
                    _ => a.floor(),
                };
                r.to_bits() as u64
            } else {
                let size = ir.input(0).map(|v| v.size).unwrap_or(8);
                let a = as_f64(x, size);
                let c = as_f64(y, ir.input(1).map(|v| v.size).unwrap_or(size));
                let r = match ir.op {
                    Op::FloatAdd => a + c,
                    Op::FloatSub => a - c,
                    Op::FloatMul => a * c,
                    Op::FloatDiv => a / c,
                    Op::FloatMax => a.max(c),
                    Op::FloatMin => a.min(c),
                    Op::FloatNeg => -a,
                    Op::FloatAbs => a.abs(),
                    Op::FloatSqrt => a.sqrt(),
                    Op::FloatTrunc => a.trunc(),
                    Op::FloatRound => round_ties_even(a),
                    Op::FloatCeil => a.ceil(),
                    _ => a.floor(),
                };
                r.to_bits()
            }
        }
        // Fused: one rounding, which is why it is an operation rather than a
        // multiply followed by an add.
        Op::FloatMulAdd => {
            let z = ir.input(2).map(|v| m.read(v)).unwrap_or(0);
            if out.size == 4 {
                as_f32(x).mul_add(as_f32(y), as_f32(z)).to_bits() as u64
            } else {
                f64::from_bits(x).mul_add(f64::from_bits(y), f64::from_bits(z)).to_bits()
            }
        }
        Op::FloatEqual | Op::FloatNotEqual | Op::FloatLess | Op::FloatLessEqual | Op::FloatNan => {
            let size = ir.input(0).map(|v| v.size).unwrap_or(8);
            let a = as_f64(x, size);
            let c = as_f64(y, ir.input(1).map(|v| v.size).unwrap_or(size));
            match ir.op {
                Op::FloatEqual => (a == c) as u64,
                Op::FloatNotEqual => (a != c) as u64,
                Op::FloatLess => (a < c) as u64,
                Op::FloatLessEqual => (a <= c) as u64,
                _ => a.is_nan() as u64,
            }
        }
        Op::IntToFloat | Op::UIntToFloat => {
            let size = ir.input(0).map(|v| v.size).unwrap_or(8);
            if out.size == 4 {
                let v = if ir.op == Op::IntToFloat {
                    sext(x, size) as f32
                } else {
                    (x & mask_of(ir, 0)) as f32
                };
                v.to_bits() as u64
            } else {
                let v = if ir.op == Op::IntToFloat {
                    sext(x, size) as f64
                } else {
                    (x & mask_of(ir, 0)) as f64
                };
                v.to_bits()
            }
        }
        // Saturating, which is what both architectures do with a value the
        // integer cannot hold.
        Op::FloatToInt | Op::FloatToUInt => {
            let size = ir.input(0).map(|v| v.size).unwrap_or(8);
            let v = as_f64(x, size).trunc();
            if ir.op == Op::FloatToInt {
                match out.size {
                    1 => v as i8 as u64,
                    2 => v as i16 as u64,
                    4 => v as i32 as u64,
                    _ => v as i64 as u64,
                }
            } else {
                match out.size {
                    1 => v as u8 as u64,
                    2 => v as u16 as u64,
                    4 => v as u32 as u64,
                    _ => v as u64,
                }
            }
        }
        Op::FloatConvert => {
            let size = ir.input(0).map(|v| v.size).unwrap_or(8);
            let v = as_f64(x, size);
            if out.size == 4 {
                (v as f32).to_bits() as u64
            } else {
                v.to_bits()
            }
        }
        Op::IntZExt => x,
        Op::IntSExt => xs as u64,
        Op::PopCount => x.count_ones() as u64,
        Op::LzCount => {
            let bits = ir.input(0).map(|v| v.size as u32 * 8).unwrap_or(64);
            (x << (64 - bits)).leading_zeros() as u64
        }
        Op::BoolAnd => ((x != 0) && (y != 0)) as u64,
        Op::BoolOr => ((x != 0) || (y != 0)) as u64,
        Op::BoolXor => ((x != 0) ^ (y != 0)) as u64,
        Op::BoolNot => (x == 0) as u64,
        Op::Piece => {
            let low_bits = ir.input(1).map(|v| v.size as u32 * 8).unwrap_or(0);
            (x << low_bits) | y
        }
        Op::SubPiece => x >> (y * 8),
        _ => return Step::Next,
    };

    m.write(out, value);
    Step::Next
}

/// Read a double-width value as signed. The halves compose into 128 bits but
/// the value occupies only twice the operand width, so the sign lives there.
fn sext128(v: u128, bits: u32) -> i128 {
    if bits >= 128 {
        return v as i128;
    }
    ((v << (128 - bits)) as i128) >> (128 - bits)
}

/// Read a bit pattern as a floating point number of the given width.
fn as_f64(bits: u64, size: u8) -> f64 {
    if size == 4 {
        f32::from_bits(bits as u32) as f64
    } else {
        f64::from_bits(bits)
    }
}

/// Read a bit pattern as single precision.
fn as_f32(bits: u64) -> f32 {
    f32::from_bits(bits as u32)
}

/// Round to nearest with ties to even, the mode both architectures start in.
fn round_ties_even(v: f64) -> f64 {
    let r = v.round();
    if (v - v.trunc()).abs() == 0.5 && r % 2.0 != 0.0 {
        r - v.signum()
    } else {
        r
    }
}

/// The divisor of a divide, which the double-width forms take third.
fn divisor(ir: &IrOp, m: &mut Machine) -> u64 {
    let n = match ir.op {
        Op::IntDiv128 | Op::IntRem128 | Op::IntSDiv128 | Op::IntSRem128 => 2,
        _ => 1,
    };
    ir.input(n).map(|v| m.read(v)).unwrap_or(0)
}

/// The mask of the operation's first input, for the carry computation.
fn mask_of(ir: &IrOp, n: usize) -> u64 {
    ir.input(n).map(|v| v.mask()).unwrap_or(u64::MAX)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn op(o: Op, out: Option<Varnode>, ins: &[Varnode]) -> IrOp {
        let mut ir = IrOp::new(Addr(0x1000), o, out);
        for i in ins {
            ir = ir.with(*i);
        }
        ir
    }

    #[test]
    fn arithmetic_truncates_to_the_output_size() {
        let mut m = Machine::new();
        let out = Varnode::register(0, 4);
        step(
            &mut m,
            &op(
                Op::IntAdd,
                Some(out),
                &[Varnode::constant(0xffff_ffff, 4), Varnode::constant(1, 4)],
            ),
        );
        // Four bytes, so the carry out is dropped rather than kept.
        assert_eq!(m.reg(0, 4), 0);
        assert_eq!(m.reg(0, 8), 0);
    }

    #[test]
    fn signed_and_unsigned_comparison_differ() {
        let mut m = Machine::new();
        let out = Varnode::register(0, 1);
        let neg = Varnode::constant(0xffff_ffff_ffff_ffff, 8);
        let one = Varnode::constant(1, 8);
        step(&mut m, &op(Op::IntSLess, Some(out), &[neg, one]));
        assert_eq!(m.reg(0, 1), 1, "-1 < 1 signed");
        step(&mut m, &op(Op::IntLess, Some(out), &[neg, one]));
        assert_eq!(m.reg(0, 1), 0, "0xffff... < 1 unsigned is false");
    }

    #[test]
    fn a_shift_past_the_width_is_zero_not_a_wrap() {
        // Rust's shift operators panic or wrap; the machine produces zero.
        let mut m = Machine::new();
        let out = Varnode::register(0, 4);
        step(
            &mut m,
            &op(
                Op::IntLeft,
                Some(out),
                &[Varnode::constant(1, 4), Varnode::constant(64, 1)],
            ),
        );
        assert_eq!(m.reg(0, 4), 0);
    }

    #[test]
    fn an_arithmetic_shift_of_a_negative_keeps_the_sign() {
        let mut m = Machine::new();
        let out = Varnode::register(0, 4);
        step(
            &mut m,
            &op(
                Op::IntSRight,
                Some(out),
                &[Varnode::constant(0xffff_fff0, 4), Varnode::constant(4, 1)],
            ),
        );
        assert_eq!(m.reg(0, 4), 0xffff_ffff);
    }

    #[test]
    fn sign_extension_widens_correctly() {
        let mut m = Machine::new();
        let out = Varnode::register(0, 8);
        step(
            &mut m,
            &op(Op::IntSExt, Some(out), &[Varnode::constant(0xff, 1)]),
        );
        assert_eq!(m.reg(0, 8), u64::MAX);
        step(
            &mut m,
            &op(Op::IntZExt, Some(out), &[Varnode::constant(0xff, 1)]),
        );
        assert_eq!(m.reg(0, 8), 0xff);
    }

    #[test]
    fn overlapping_registers_really_overlap() {
        // The reason the register space is byte-addressed: writing the low
        // four bytes has to be visible through the eight-byte view.
        let mut m = Machine::new();
        m.set_reg(0, 8, 0xdead_beef_cafe_babe);
        m.set_reg(0, 4, 0x1111_2222);
        assert_eq!(m.reg(0, 4), 0x1111_2222);
        assert_eq!(m.reg(0, 8), 0xdead_beef_1111_2222);
    }

    #[test]
    fn division_by_zero_stops_rather_than_panicking() {
        let mut m = Machine::new();
        let out = Varnode::register(0, 8);
        let r = step(
            &mut m,
            &op(
                Op::IntDiv,
                Some(out),
                &[Varnode::constant(1, 8), Varnode::constant(0, 8)],
            ),
        );
        assert!(matches!(r, Step::Halt(Stop::DivideByZero(_))));
    }

    #[test]
    fn an_unknown_read_is_recorded_rather_than_invented() {
        let mut m = Machine::new();
        assert_eq!(m.read_mem(0x4000, 4), 0);
        assert_eq!(m.unknown_reads.len(), 4);
    }

    #[test]
    fn memory_round_trips() {
        let mut m = Machine::new();
        m.write_mem(0x1000, &[0x78, 0x56, 0x34, 0x12]);
        assert_eq!(m.read_mem(0x1000, 4), 0x1234_5678);
        assert!(m.unknown_reads.is_empty());
    }
}
