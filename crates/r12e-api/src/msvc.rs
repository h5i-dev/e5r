//! Microsoft C++ run-time type information.
//!
//! A different layout for the same facts, and also published. The word before
//! a vftable's first slot points at a `RTTICompleteObjectLocator`, which names
//! the `TypeDescriptor` holding the class's decorated name and the
//! `ClassHierarchyDescriptor` holding its bases. Everything inside is a
//! relative virtual address: an offset from the image base, not a pointer, so
//! a PE keeps its type information without a single relocation.
//!
//! The base array is not a list of direct bases. It is a preorder walk of the
//! whole lattice with the class itself first, and each entry says how many
//! entries after it are underneath it. Walking it with those counts is what
//! turns it back into the direct bases the source declared, and it is the only
//! reason `Join : ViaA, ViaB` does not come back with a `Root` it never
//! declared.

use std::collections::BTreeMap;

use r12e_core::{Addr, Evidence};

use r12e_analysis::Program;

use crate::classes::{BaseClass, Basis, TypeInfo, is_code, read_int, word, word_size};
use crate::vtables::VTable;

/// What the Microsoft type information in an image says.
pub(crate) struct Found {
    /// The virtual function tables, each with the type information it names.
    pub tables: Vec<VTable>,
    /// One entry per `TypeDescriptor`, which is one per class.
    pub infos: BTreeMap<Addr, TypeInfo>,
}

/// Read every virtual table and every class the image's type information names.
pub(crate) fn read(p: &Program) -> Found {
    let ws = word_size(p) as i64;
    let mut tables = Vec::new();
    let mut infos: BTreeMap<Addr, TypeInfo> = BTreeMap::new();

    for section in &p.object.sections {
        // Where a compiler puts tables. `.text` is excluded: a code byte
        // sequence that reads as a pointer to a locator is a coincidence, and
        // one that does is not a table.
        if section.exec || section.range.is_empty() {
            continue;
        }
        let mut at = section.range.start();
        while at.get() + 2 * ws as u64 <= section.range.end().get() {
            let step = at;
            at = at.wrapping_offset(ws);
            let Some(pointer) = word(p, step) else {
                continue;
            };
            let Some(locator) = locator(p, Addr(pointer)) else {
                continue;
            };
            let entry = step.wrapping_offset(ws);
            let mut methods = Vec::new();
            let mut slot = entry;
            while let Some(target) = word(p, slot) {
                if !is_code(p, Addr(target)) {
                    break;
                }
                methods.push(Addr(target));
                slot = slot.wrapping_offset(ws);
            }
            if methods.is_empty() {
                continue;
            }
            at = slot;

            if let Some(info) = describe(p, &locator)
                && !infos.contains_key(&locator.descriptor)
            {
                infos.insert(locator.descriptor, info);
            }
            tables.push(VTable {
                addr: step,
                entry,
                class: None,
                // The locator says how far into the complete object this
                // table's subobject starts, which is the negative of what the
                // Itanium ABI writes down in the same place.
                offset_to_top: -(locator.offset as i64),
                typeinfo: Some(locator.descriptor),
                methods,
                evidence: Evidence::DataPointer,
            });
        }
    }
    Found { tables, infos }
}

/// A complete object locator, read.
struct Locator {
    /// How far into the complete object this table's subobject starts.
    offset: u32,
    /// The type descriptor, which holds the class's decorated name.
    descriptor: Addr,
    /// The class hierarchy descriptor, which holds its bases.
    hierarchy: Addr,
}

/// Read the locator at an address, if that is what is there.
fn locator(p: &Program, at: Addr) -> Option<Locator> {
    // Signature zero on 32-bit and one on 64-bit, where the structure carries
    // its own address so a relative address inside it can be resolved.
    let signature = read_int(p, at, 4)? as u32;
    if signature > 1 {
        return None;
    }
    let offset = read_int(p, at.wrapping_offset(4), 4)? as u32;
    let descriptor = rva(p, read_int(p, at.wrapping_offset(12), 4)? as u32)?;
    let hierarchy = rva(p, read_int(p, at.wrapping_offset(16), 4)? as u32)?;
    // The descriptor has to hold a decorated type name, which is what makes
    // this a locator rather than five words that read like one.
    decorated_name(p, descriptor)?;
    Some(Locator {
        offset,
        descriptor,
        hierarchy,
    })
}

/// The class a locator names, and the bases the hierarchy descriptor lists.
fn describe(p: &Program, locator: &Locator) -> Option<TypeInfo> {
    let mangled = decorated_name(p, locator.descriptor)?;
    let name = class_name(&mangled);

    let count = read_int(p, locator.hierarchy.wrapping_offset(8), 4)? as u32;
    // The class itself is the first entry, so one is the least a real
    // descriptor has; a count that cannot be an array is not a count.
    if count == 0 || count > 4096 {
        return None;
    }
    let array = rva(
        p,
        read_int(p, locator.hierarchy.wrapping_offset(12), 4)? as u32,
    )?;

    // The direct bases: walk the preorder, and after each one skip the bases
    // it contains, because those are its and not this class's.
    let mut bases = Vec::new();
    let mut i = 1u32;
    while i < count {
        let at = rva(
            p,
            read_int(p, array.wrapping_offset(i as i64 * 4), 4)? as u32,
        )?;
        let descriptor = rva(p, read_int(p, at, 4)? as u32)?;
        let contained = read_int(p, at.wrapping_offset(4), 4)? as u32;
        // The member displacement structure: where the base sits, and through
        // which virtual base table when it is a virtual base.
        let mdisp = read_int(p, at.wrapping_offset(8), 4)? as u32 as i32 as i64;
        let pdisp = read_int(p, at.wrapping_offset(12), 4)? as u32 as i32 as i64;
        let attributes = read_int(p, at.wrapping_offset(20), 4)? as u32;
        // A displacement of -1 to the virtual base table means there is none,
        // so the base sits at a fixed place in the object.
        let is_virtual = pdisp >= 0;
        bases.push(BaseClass {
            name: class_name(&decorated_name(p, descriptor)?),
            typeinfo: descriptor,
            offset: if is_virtual { pdisp } else { mdisp },
            is_virtual,
            // Bit two says the base is private or protected. Nothing else in
            // the attributes bears on what the source declared.
            is_public: attributes & 4 == 0,
            basis: Basis::Rtti,
        });
        i += 1 + contained;
    }

    Some(TypeInfo {
        name,
        mangled,
        // The three type-information classes are an Itanium notion; the
        // Microsoft layout is one shape for every class.
        kind: None,
        bases,
        basis: Basis::Rtti,
    })
}

/// The decorated type name a type descriptor holds.
fn decorated_name(p: &Program, at: Addr) -> Option<String> {
    let name = at.wrapping_offset(2 * word_size(p) as i64);
    let window = p.object.memory.decode_window(name, 512)?;
    let end = window.iter().position(|b| *b == 0)?;
    let text = std::str::from_utf8(window.get(..end)?).ok()?;
    // Every type descriptor's name starts with the encoding of a type at no
    // qualification, which is what separates one from any other string.
    text.starts_with(".?A").then(|| text.to_string())
}

/// The class a decorated type name names.
///
/// `.?AVFoo@Bar@@` is `Bar::Foo`: the components are innermost first and the
/// leading letter says class or struct. Anything with a template argument list
/// in it is handed back as it is written, because guessing at the argument
/// grammar would put a name in the output that is not the class's.
fn class_name(decorated: &str) -> String {
    let plain = || decorated.to_string();
    let Some(body) = decorated.strip_prefix(".?A") else {
        return plain();
    };
    let body = body.strip_prefix(['V', 'U', 'T', 'W']).unwrap_or(body);
    let Some(body) = body.strip_suffix("@@") else {
        return plain();
    };
    let parts: Vec<&str> = body.split('@').collect();
    if parts.is_empty()
        || parts.iter().any(|s| {
            s.is_empty()
                || !s
                    .chars()
                    .all(|c| c.is_ascii_alphanumeric() || c == '_' || c == '$')
        })
    {
        return plain();
    }
    parts
        .iter()
        .rev()
        .copied()
        .collect::<Vec<&str>>()
        .join("::")
}

/// The address a relative virtual address names.
fn rva(p: &Program, rva: u32) -> Option<Addr> {
    if rva == 0 {
        return None;
    }
    let at = Addr(p.object.image_base.get().wrapping_add(rva as u64));
    p.object.memory.is_mapped(at).then_some(at)
}
