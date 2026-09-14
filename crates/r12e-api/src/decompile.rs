//! Decompiling a program, from analysis to C.
//!
//! The whole pipeline in one place: lift, promote the stack, build SSA,
//! optimize, structure, emit. What the debug information says is used where it
//! says anything, and the functions of a program come out as one translation
//! unit with everything declared before it is used.

use std::collections::{BTreeMap, BTreeSet};

use r12e_analysis::{Function, Program};
use r12e_core::{Addr, Evidence};
use r12e_decomp::{Callee, Output, Param, Prototype};
use r12e_ir::proto::Asserted;
use r12e_ir::ssa::SsaFunction;
use r12e_types::ctype::{Type, TypeId, Types};

pub use r12e_decomp::expr::{Home, Role, Variable};

/// One decompiled function.
#[derive(Debug, Clone)]
pub struct Decompiled {
    /// Where it starts.
    pub addr: Addr,
    /// What it is called.
    pub name: String,
    /// Its declaration, without a body.
    pub signature: String,
    /// The C text.
    pub text: String,
    /// Gotos the structuring needed.
    pub gotos: usize,
    /// Reachable blocks the structuring never placed, so their code is missing
    /// from the text. Zero unless the structurer has a defect.
    pub lost: usize,
    /// Named locals declared.
    pub locals: usize,
    /// Every variable the text declares, with its name, its type and where the
    /// machine kept it.
    ///
    /// A count of locals is not a fact anything can be checked against. This
    /// is what a benchmark matching recovered variables against the ones the
    /// source declared has to read, and what an analyst renames one by.
    pub variables: Vec<Variable>,
    /// Where an asserted declaration and the code disagreed, in the analyst's
    /// favour. Empty unless something was asserted about this function.
    pub conflicts: Vec<String>,
    /// True when a declaration somebody wrote down decided this signature.
    pub asserted: bool,
    /// Operations no expression covered, including instructions the lifter did
    /// not model.
    pub unmodelled: usize,
}

/// A set of functions decompiled together.
#[derive(Debug, Clone, Default)]
pub struct Unit {
    /// Declarations the text needs, in an order C accepts.
    pub declarations: Vec<String>,
    /// The functions, in address order.
    pub functions: Vec<Decompiled>,
}

impl Unit {
    /// The whole unit as one translation unit.
    pub fn text(&self) -> String {
        let mut out = String::new();
        if !self.declarations.is_empty() {
            out.push_str("#include <stdint.h>\n");
            for d in &self.declarations {
                out.push_str(d);
                out.push('\n');
            }
            out.push('\n');
        }
        for (n, f) in self.functions.iter().enumerate() {
            if n > 0 {
                out.push('\n');
            }
            out.push_str(&f.text);
        }
        out
    }

    /// How many gotos the structuring needed across the unit.
    pub fn gotos(&self) -> usize {
        self.functions.iter().map(|f| f.gotos).sum()
    }
}

/// Decompile one function, with whatever the program knows about it.
pub fn decompile_function(p: &Program, f: &Function) -> Decompiled {
    decompile_function_with(p, f, &BTreeMap::new())
}

/// The same, with the declarations an analyst asserted about the program.
///
/// Keyed by the address each declaration resolved to, which is the shape the
/// annotation log folds to and the same one comments reach the disassembler in.
pub fn decompile_function_with(
    p: &Program,
    f: &Function,
    declarations: &BTreeMap<Addr, String>,
) -> Decompiled {
    let mut unit = decompile_program_with(p, std::slice::from_ref(&f), declarations);
    unit.functions.pop().unwrap_or(Decompiled {
        addr: f.entry,
        name: f.display_name(),
        signature: String::new(),
        text: String::new(),
        gotos: 0,
        lost: 0,
        locals: 0,
        variables: Vec::new(),
        conflicts: Vec::new(),
        asserted: false,
        unmodelled: 0,
    })
}

/// Decompile a set of functions as one unit.
pub fn decompile_program(p: &Program, targets: &[&Function]) -> Unit {
    decompile_program_with(p, targets, &BTreeMap::new())
}

/// Decompile a set of functions as one unit, honouring what an analyst
/// declared about them.
///
/// Two passes: the first works out how many parameters each function declares,
/// and the second uses that so every call passes the number its callee expects.
/// Nothing knows the count until the parameters have been worked out.
pub fn decompile_program_with(
    p: &Program,
    targets: &[&Function],
    declarations: &BTreeMap<Addr, String>,
) -> Unit {
    let mut callees: BTreeMap<u64, Callee> = BTreeMap::new();
    let mut outputs: Vec<(Addr, String, One)> = Vec::new();

    // Everything the targets call, so that asking for one function gives the
    // same body as asking for all of them. Without this the callee table holds
    // only the targets, and a call to anything else renders as an anonymous
    // name with no arguments: two different answers for one function,
    // depending on how it was asked for.
    let wanted: BTreeSet<Addr> = targets.iter().map(|f| f.entry).collect();
    let mut around: Vec<&Function> = Vec::new();
    for f in targets {
        for site in &f.cfg.calls {
            if wanted.contains(site) {
                continue;
            }
            if let Some(callee) = p.function(*site)
                && !around.iter().any(|c| c.entry == callee.entry)
            {
                around.push(callee);
            }
        }
    }

    for pass in 0..2 {
        outputs.clear();
        // The neighbours are prototyped but never emitted: they are here to
        // fill the table, and on the last pass their bodies would be thrown
        // away anyway.
        for (n, f) in targets.iter().chain(around.iter()).enumerate() {
            let Some(one) = one(p, f, &callees, declarations) else {
                continue;
            };
            let out = &one.output;
            let name = f.display_name();
            callees.insert(
                f.entry.get(),
                Callee {
                    name: r12e_decomp::identifier(&name),
                    arity: out.arity,
                    pointer_parameters: out.pointer_parameters.clone(),
                    parameter_widths: out.parameter_widths.clone(),
                    returns_value: !out.signature.starts_with("void "),
                    signature: out.signature.clone(),
                },
            );
            if n < targets.len() {
                outputs.push((f.entry, name, one));
            }
        }
        let _ = pass;
    }

    // Deduplicated but not sorted: a type definition has to come after the
    // ones it mentions, and alphabetical order is not that.
    let mut declared: Vec<String> = Vec::new();
    for (_, _, one) in &outputs {
        for d in &one.output.declarations {
            if !declared.contains(d) {
                declared.push(d.clone());
            }
        }
    }
    // Every function declared before any is defined, so a call to one defined
    // later still type-checks. The callee table is declared too, not just the
    // targets: a call to a function nobody asked to see is still written by
    // name, and a call to an undeclared name is not C a compiler will accept.
    for (_, _, one) in &outputs {
        let declaration = format!("{};", one.output.signature);
        if !declared.contains(&declaration) {
            declared.push(declaration);
        }
    }
    for callee in callees.values() {
        if callee.signature.is_empty() {
            continue;
        }
        let declaration = format!("{};", callee.signature);
        if !declared.contains(&declaration) {
            declared.push(declaration);
        }
    }

    Unit {
        declarations: declared,
        functions: outputs
            .into_iter()
            .map(|(addr, name, one)| Decompiled {
                addr,
                name,
                signature: one.output.signature,
                text: one.output.text,
                gotos: one.output.gotos,
                lost: one.output.lost,
                locals: one.output.locals,
                variables: one.variables,
                conflicts: one.conflicts,
                asserted: one.asserted,
                unmodelled: one.output.unmodelled + one.unlifted,
            })
            .collect(),
    }
}

/// One function's way through the pipeline, and what was learned on the way.
struct One {
    output: Output,
    /// Instructions the lifter did not model, which the emitter never saw.
    unlifted: usize,
    variables: Vec<Variable>,
    conflicts: Vec<String>,
    asserted: bool,
}

/// One function through the whole pipeline.
fn one(
    p: &Program,
    f: &Function,
    callees: &BTreeMap<u64, Callee>,
    declarations: &BTreeMap<Addr, String>,
) -> Option<One> {
    // What each jump table means: the index the branch used and where that
    // index goes, which is what turns a many-successor block into a switch.
    //
    // Keyed by the block the branch ends, not by the branch's own address. The
    // structurer knows blocks by where they start, and an indirect branch is
    // the last instruction of its block rather than the first, so keying by
    // `JumpTable::at` makes every lookup miss and no switch is ever built.
    let switches: r12e_decomp::Switches = f
        .cfg
        .tables
        .iter()
        .filter_map(|t| {
            let (start, _) = f.cfg.blocks.iter().find(|(_, b)| b.range.contains(t.at))?;
            Some((
                *start,
                t.targets
                    .iter()
                    .enumerate()
                    .map(|(n, target)| (n as u64, *target))
                    .collect(),
            ))
        })
        .collect();
    let blocks: BTreeMap<Addr, (Addr, Vec<Addr>)> = f
        .cfg
        .blocks
        .iter()
        .map(|(a, b)| (*a, (b.range.end(), b.successors.clone())))
        .collect();
    let mut ir = r12e_ir::func::build(&p.object.memory, &p.object.arch, f.entry, &blocks);
    r12e_ir::stack::promote(&mut ir);
    let mut ssa = r12e_ir::ssa::build(&ir);
    r12e_ir::opt::optimize(&mut ssa);
    // The SSA the emitter runs on is the SSA prototype recovery reads, rather
    // than a second build of the same thing: lifting a function twice is not
    // free and the two could drift apart.
    let shape = prototype(p, f, &ssa, declarations);
    let name = f.display_name();
    let output =
        r12e_decomp::decompile_full(&name, &ssa, shape.prototype.as_ref(), callees, &switches);
    Some(One {
        variables: r12e_decomp::expr::variables(&ssa, shape.prototype.as_ref(), &output.text),
        output,
        unlifted: ir.unlifted.len(),
        conflicts: shape.conflicts,
        asserted: shape.asserted,
    })
}

/// What is known about a function's shape, in the form the emitter wants, and
/// what had to be overruled to get there.
struct Shape {
    prototype: Option<Prototype>,
    conflicts: Vec<String>,
    asserted: bool,
}

/// What is known about a function's shape, in the form the emitter wants.
///
/// In order: what an analyst wrote down, then the debug information, then what
/// the code itself says, which is how many argument registers arrive with
/// values and whether anything is left for the caller. The last is weakest and
/// it is all a stripped binary has.
///
/// An assertion outranks the other two because writing one down is the only
/// way an analyst has of telling the engine it was wrong, and an assertion
/// that changed nothing would make the whole loop pointless. What the machine
/// found is not thrown away: it is kept beside the declaration and the
/// disagreements come back as conflicts.
fn prototype(
    p: &Program,
    f: &Function,
    ssa: &SsaFunction,
    declarations: &BTreeMap<Addr, String>,
) -> Shape {
    if let Some(a) = asserted(p, f, declarations) {
        let abi = r12e_ir::abi::of(&p.object.arch);
        let recovered = r12e_ir::proto::recover_with(ssa, &abi, Some(&a));
        return Shape {
            conflicts: recovered.conflicts.iter().map(|c| c.to_string()).collect(),
            prototype: Some(asserted_prototype(&a, &recovered)),
            asserted: true,
        };
    }
    Shape {
        prototype: declared(p, f)
            .or_else(|| import_thunk(f))
            .or_else(|| recovered(p, f, ssa)),
        conflicts: Vec::new(),
        asserted: false,
    }
}

/// The declaration an analyst wrote down for this function, parsed.
///
/// Parsed against the program's own types, so a declaration may name a
/// structure the debug information already described rather than having to
/// restate it. A declaration that does not parse is not a reason to refuse to
/// decompile: the engine's own answer is still there and the annotation
/// commands are where a person is told their C is malformed.
fn asserted(p: &Program, f: &Function, declarations: &BTreeMap<Addr, String>) -> Option<Asserted> {
    let text = declarations.get(&f.entry)?;
    let mut types = match p.object.debug.as_ref() {
        Some(d) => d.types.clone(),
        None => Types::new(),
    };
    // The store carries the types and the architecture carries how wide they
    // are, and a declaration mentioning `long` needs both.
    types.set_model(r12e_ir::proto::model_of(&p.object.arch));
    Asserted::parse_into(types, text).ok()
}

/// The emitter's form of an asserted declaration, laid over the convention.
fn asserted_prototype(a: &Asserted, recovered: &r12e_ir::proto::Prototype) -> Prototype {
    let types = &a.types;
    let mut parameters: Vec<Param> = Vec::new();
    let mut mentioned: Vec<TypeId> = Vec::new();

    // A result too large for the result registers is written through a pointer
    // the caller passes in the first argument register, so every declared
    // parameter sits one register further along than it looks. Declaring the
    // pointer is what keeps the body's names on the right registers, and it is
    // also what the machine code actually does.
    if recovered.returns_via_memory {
        if let Some(ty) = a.signature.returns {
            let mut with_pointer = types.clone();
            let ptr = with_pointer.pointer(ty);
            parameters.push(Param {
                decl: with_pointer.declare(ptr, RESULT),
                name: RESULT.to_string(),
                floating: false,
                pointer: true,
                size: with_pointer.size_of(ptr).unwrap_or(0).min(255) as u8,
                fields: Vec::new(),
                stride: None,
            });
            mentioned.push(ty);
        }
    }

    for (n, param) in recovered.parameters.iter().enumerate() {
        let name = param.name.clone().unwrap_or_else(|| format!("arg{n}"));
        let resolved = types.get(types.resolve(param.ty));
        parameters.push(Param {
            decl: types.declare(param.ty, &name),
            name,
            floating: matches!(resolved, Some(Type::Float { size: 4 | 8 })),
            pointer: matches!(resolved, Some(Type::Pointer(_))),
            size: param.size.min(255) as u8,
            // A declared type names its own fields. Inventing `field_8` for a
            // parameter whose structure is written down would contradict the
            // declaration the same output prints.
            fields: Vec::new(),
            stride: None,
        });
        mentioned.push(param.ty);
    }

    let returns = match a.signature.returns {
        // The result does not come back in a register at all; it is already a
        // parameter, and a function that returns nothing returns nothing.
        Some(_) if recovered.returns_via_memory => "void".to_string(),
        Some(ty) => types.name_of(ty),
        None => "void".to_string(),
    };

    let mut definitions: Vec<String> = Vec::new();
    for t in mentioned {
        for d in types.dependencies(t) {
            if let Some(text) = types.definition(d) {
                if !definitions.contains(&text) {
                    definitions.push(text);
                }
            }
        }
    }

    Prototype {
        parameters,
        returns: Some(returns),
        definitions,
        locals: BTreeMap::new(),
    }
}

/// What the hidden pointer to a memory-returned result is called.
const RESULT: &str = "__result";

/// The shape of a jump into another image.
///
/// A PLT or IAT thunk's body is one indirect jump. It reads no argument
/// register and writes no result, so recovering its shape from its own code
/// says it takes nothing and returns nothing, and neither is a claim the
/// binary supports: both belong to the imported function, which is not here.
/// Saying `void` is the damaging half. Every caller that uses the result then
/// has a local it reads and never assigns, which is undefined behaviour in the
/// emitted C, so the result is kept and the parameter list is left empty, the
/// same as for any callee nothing is known about.
fn import_thunk(f: &Function) -> Option<Prototype> {
    let thunk = f.provenance.best == Evidence::ImportThunk
        || f.provenance.corroborating.contains(&Evidence::ImportThunk);
    thunk.then(|| Prototype {
        parameters: Vec::new(),
        returns: Some("uint64_t".to_string()),
        definitions: Vec::new(),
        locals: BTreeMap::new(),
    })
}

/// The shape the code implies, for a function nothing declared.
fn recovered(p: &Program, f: &Function, ssa: &SsaFunction) -> Option<Prototype> {
    if f.cfg.blocks.is_empty() {
        return None;
    }
    let abi = r12e_ir::abi::of(&p.object.arch);
    let recovered = r12e_ir::proto::recover(ssa, &abi);

    // What each incoming pointer was used as, so an access at a known offset
    // reads as a field rather than as arithmetic.
    let shapes: BTreeMap<u64, Layout> = r12e_ir::shape::shapes(ssa)
        .into_iter()
        .filter(|(l, _)| l.offset != abi.stack_pointer)
        .map(|(l, shape)| (l.offset, (shape.fields(), shape.size())))
        .collect();

    let mut parameters = Vec::new();
    let mut definitions = Vec::new();
    for n in 0..recovered.integer_arguments {
        let name = format!("arg{n}");
        let offset = abi.integer_arguments.get(n).copied().unwrap_or(u64::MAX);
        // Two or more fields is a structure worth naming; one is a pointer to
        // a value, which `*p` already says.
        let (fields, stride) = shapes
            .get(&offset)
            .filter(|(f, _)| f.len() > 1)
            .cloned()
            .unwrap_or_default();
        // The name carries the function, because two functions rarely hand
        // the same structure to the same argument register and a shared name
        // would claim they did.
        let tag = format!("{}_{name}", r12e_decomp::identifier(&f.display_name()));
        // The register is eight bytes; the argument is as wide as the body
        // reads it, which is what stops every parameter being `uint64_t` and
        // what lets a caller's `-512` print as itself rather than as
        // `0xfffffe00`.
        let width = recovered.integer_widths.get(n).copied().unwrap_or(8);
        let (decl, pointer) = if fields.is_empty() {
            (format!("{} {name}", r12e_decomp::c_type(width)), false)
        } else {
            definitions.push(structure(&tag, &fields));
            (format!("struct s_{tag} *{name}"), true)
        };
        parameters.push(Param {
            decl,
            name,
            floating: false,
            pointer,
            size: if pointer { 8 } else { width },
            fields,
            stride,
        });
    }
    for n in 0..recovered.float_arguments {
        let name = format!("farg{n}");
        // A `float` and a `double` arrive in the same register; only what the
        // body reads says which was declared.
        let width = recovered.float_widths.get(n).copied().unwrap_or(8);
        let ty = if width == 4 { "float" } else { "double" };
        parameters.push(Param {
            decl: format!("{ty} {name}"),
            name,
            floating: true,
            pointer: false,
            size: width,
            fields: Vec::new(),
            stride: None,
        });
    }
    Some(Prototype {
        parameters,
        // A function that leaves nothing behind returns nothing, and saying
        // `void` is what makes the output read like the source.
        returns: Some(match recovered.returns {
            None => "void".to_string(),
            Some(offset) if recovered.returns_float => {
                let _ = offset;
                "double".to_string()
            }
            Some(_) => "uint64_t".to_string(),
        }),
        definitions,
        locals: BTreeMap::new(),
    })
}

/// What was seen through one pointer: its fields, and the element size when
/// it walks an array of them.
type Layout = (Vec<(i64, u8)>, Option<u64>);

/// The C definition of a structure the accesses imply.
fn structure(name: &str, fields: &[(i64, u8)]) -> String {
    let mut out = format!("struct s_{name} {{");
    let mut at = 0i64;
    for (offset, size) in fields {
        // Padding, so every field lands where the code put it.
        if *offset > at {
            out.push_str(&format!(" uint8_t pad_{at:x}[{}];", offset - at));
            at = *offset;
        }
        if *offset < at {
            continue;
        }
        let ty = match size {
            1 => "uint8_t",
            2 => "uint16_t",
            4 => "uint32_t",
            _ => "uint64_t",
        };
        out.push_str(&format!(" {ty} {};", r12e_decomp::field_name(*offset)));
        at = offset + *size as i64;
    }
    out.push_str(" };");
    out
}

/// What the debug information said about a function.
fn declared(p: &Program, f: &Function) -> Option<Prototype> {
    let d = p.object.debug.as_ref()?;
    let df = d.functions.get(&f.entry)?;
    let parameters = df
        .signature
        .parameters
        .iter()
        .enumerate()
        .map(|(n, (name, ty))| {
            let name = name.clone().unwrap_or_else(|| format!("arg{n}"));
            let resolved = d.types.get(d.types.resolve(*ty));
            Param {
                decl: d.types.declare(*ty, &name),
                name,
                floating: matches!(resolved, Some(Type::Float { .. })),
                pointer: matches!(resolved, Some(Type::Pointer(_))),
                size: d.types.size_of(*ty).unwrap_or(0) as u8,
                // The declared type already names the fields.
                fields: Vec::new(),
                stride: None,
            }
        })
        .collect();
    Some(Prototype {
        parameters,
        returns: df.signature.returns.map(|t| d.types.name_of(t)),
        // The named types the signature mentions, defined before they are used
        // so the output is a translation unit and not a fragment.
        definitions: df
            .signature
            .returns
            .into_iter()
            .chain(df.signature.parameters.iter().map(|(_, t)| *t))
            .flat_map(|t| d.types.dependencies(t))
            .filter_map(|t| d.types.definition(t))
            .collect(),
        locals: df
            .locals
            .iter()
            .filter_map(|l| Some((l.frame_offset?, (l.name.clone(), d.types.name_of(l.ty)))))
            .collect(),
    })
}
