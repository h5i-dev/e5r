//! Decompiling a program, from analysis to C.
//!
//! The whole pipeline in one place: lift, promote the stack, build SSA,
//! optimize, structure, emit. What the debug information says is used where it
//! says anything, and the functions of a program come out as one translation
//! unit with everything declared before it is used.

use std::collections::BTreeMap;

use r12e_analysis::{Function, Program};
use r12e_core::Addr;
use r12e_decomp::{Callee, Output, Param, Prototype};

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
    /// Named locals declared.
    pub locals: usize,
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
    let mut unit = decompile_program(p, std::slice::from_ref(&f));
    unit.functions.pop().unwrap_or(Decompiled {
        addr: f.entry,
        name: f.display_name(),
        signature: String::new(),
        text: String::new(),
        gotos: 0,
        locals: 0,
        unmodelled: 0,
    })
}

/// Decompile a set of functions as one unit.
///
/// Two passes: the first works out how many parameters each function declares,
/// and the second uses that so every call passes the number its callee expects.
/// Nothing knows the count until the parameters have been worked out.
pub fn decompile_program(p: &Program, targets: &[&Function]) -> Unit {
    let mut callees: BTreeMap<u64, Callee> = BTreeMap::new();
    let mut outputs: Vec<(Addr, String, Output, usize)> = Vec::new();

    for _ in 0..2 {
        outputs.clear();
        for f in targets {
            let Some((out, unlifted)) = one(p, f, &callees) else {
                continue;
            };
            let name = f.display_name();
            callees.insert(
                f.entry.get(),
                Callee {
                    name: r12e_decomp::identifier(&name),
                    arity: out.arity,
                    pointer_parameters: out.pointer_parameters.clone(),
                    returns_value: !out.signature.starts_with("void "),
                },
            );
            outputs.push((f.entry, name, out, unlifted));
        }
    }

    // Deduplicated but not sorted: a type definition has to come after the
    // ones it mentions, and alphabetical order is not that.
    let mut declarations: Vec<String> = Vec::new();
    for (_, _, out, _) in &outputs {
        for d in &out.declarations {
            if !declarations.contains(d) {
                declarations.push(d.clone());
            }
        }
    }
    // Every function declared before any is defined, so a call to one defined
    // later still type-checks.
    for (_, _, out, _) in &outputs {
        let declaration = format!("{};", out.signature);
        if !declarations.contains(&declaration) {
            declarations.push(declaration);
        }
    }

    Unit {
        declarations,
        functions: outputs
            .into_iter()
            .map(|(addr, name, out, unlifted)| Decompiled {
                addr,
                name,
                signature: out.signature,
                text: out.text,
                gotos: out.gotos,
                locals: out.locals,
                unmodelled: out.unmodelled + unlifted,
            })
            .collect(),
    }
}

/// One function through the whole pipeline.
fn one(p: &Program, f: &Function, callees: &BTreeMap<u64, Callee>) -> Option<(Output, usize)> {
    // What each jump table means: the index the branch used and where that
    // index goes, which is what turns a many-successor block into a switch.
    let switches: r12e_decomp::Switches = f
        .cfg
        .tables
        .iter()
        .map(|t| {
            (
                t.at,
                t.targets
                    .iter()
                    .enumerate()
                    .map(|(n, target)| (n as u64, *target))
                    .collect(),
            )
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
    let prototype = prototype(p, f);
    let name = f.display_name();
    Some((
        r12e_decomp::decompile_full(&name, &ssa, prototype.as_ref(), callees, &switches),
        ir.unlifted.len(),
    ))
}

/// What is known about a function's shape, in the form the emitter wants.
///
/// The debug information where there is any, and otherwise what the code
/// itself says: how many argument registers arrive with values and whether
/// anything is left for the caller. The second is weaker but it is what a
/// stripped binary has.
fn prototype(p: &Program, f: &Function) -> Option<Prototype> {
    declared(p, f).or_else(|| recovered(p, f))
}

/// The shape the code implies, for a function nothing declared.
fn recovered(p: &Program, f: &Function) -> Option<Prototype> {
    let blocks: BTreeMap<Addr, (Addr, Vec<Addr>)> = f
        .cfg
        .blocks
        .iter()
        .map(|(a, b)| (*a, (b.range.end(), b.successors.clone())))
        .collect();
    if blocks.is_empty() {
        return None;
    }
    let mut ir = r12e_ir::func::build(&p.object.memory, &p.object.arch, f.entry, &blocks);
    r12e_ir::stack::promote(&mut ir);
    let mut ssa = r12e_ir::ssa::build(&ir);
    r12e_ir::opt::optimize(&mut ssa);
    let abi = r12e_ir::abi::of(&p.object.arch);
    let recovered = r12e_ir::proto::recover(&ssa, &abi);

    // What each incoming pointer was used as, so an access at a known offset
    // reads as a field rather than as arithmetic.
    let shapes: BTreeMap<u64, Layout> = r12e_ir::shape::shapes(&ssa)
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
        let (decl, pointer) = if fields.is_empty() {
            (format!("uint64_t {name}"), false)
        } else {
            definitions.push(structure(&tag, &fields));
            (format!("struct s_{tag} *{name}"), true)
        };
        parameters.push(Param {
            decl,
            name,
            floating: false,
            pointer,
            size: 8,
            fields,
            stride,
        });
    }
    for n in 0..recovered.float_arguments {
        let name = format!("farg{n}");
        parameters.push(Param {
            decl: format!("double {name}"),
            name,
            floating: true,
            pointer: false,
            size: 8,
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
    use r12e_types::ctype::Type;

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
