//! What the pointers a function takes appear to point at.

use std::collections::BTreeMap;

use e5r_analysis::{Function, Program};
use e5r_core::Addr;
use e5r_ir::shape::Shape;

/// One pointer and what was seen through it.
#[derive(Debug, Clone)]
pub struct Pointer {
    /// Which argument it is, when it is one.
    pub argument: Option<usize>,
    /// The register it arrived in, as a byte offset in the register file.
    pub register: u64,
    /// The fields the accesses imply: offset and width.
    pub fields: Vec<(i64, u8)>,
    /// The element size, when an index said what it was.
    pub size: Option<u64>,
    /// True when anything wrote through it.
    pub written: bool,
}

/// What each incoming pointer of a function appears to point at.
pub fn shapes_of(p: &Program, f: &Function) -> Vec<Pointer> {
    let blocks: BTreeMap<Addr, (Addr, Vec<Addr>)> = f
        .cfg
        .blocks
        .iter()
        .map(|(a, b)| (*a, (b.range.end(), b.successors.clone())))
        .collect();
    let mut ir = e5r_ir::func::build(&p.object.memory, &p.object.arch, f.entry, &blocks);
    e5r_ir::stack::promote(&mut ir);
    let mut ssa = e5r_ir::ssa::build(&ir);
    e5r_ir::opt::optimize(&mut ssa);

    let abi = e5r_ir::abi::of(&p.object.arch);
    let mut out = Vec::new();
    for (location, shape) in e5r_ir::shape::shapes(&ssa) {
        // The stack pointer points at the frame, which promotion already
        // described; reporting it again as a structure says nothing.
        if location.offset == abi.stack_pointer {
            continue;
        }
        out.push(describe(&abi, location.offset, &shape));
    }
    out.sort_by_key(|p| (p.argument.unwrap_or(usize::MAX), p.register));
    out
}

fn describe(abi: &e5r_ir::abi::Abi, register: u64, shape: &Shape) -> Pointer {
    Pointer {
        argument: abi.integer_arguments.iter().position(|o| *o == register),
        register,
        fields: shape.fields(),
        size: shape.size(),
        written: shape.accesses.iter().any(|a| a.write),
    }
}
