//! Building and applying function signatures.

use e5r_analysis::{Function, Program};
use e5r_db::anchor::Anchor;
use e5r_db::signature::{Library, Signature};

/// Anchor one function by its content.
pub fn anchor_of(p: &Program, f: &Function) -> Anchor {
    let insns = p.instructions(f);
    // The body is the bytes the blocks cover, not the hull, so a split
    // function does not fold in whatever sits between its parts.
    let mut body = Vec::with_capacity(f.cfg.covered_bytes() as usize);
    for b in f.cfg.blocks.values() {
        if let Some(bytes) = p.object.memory.slice(b.range.start(), b.range.len()) {
            body.extend_from_slice(bytes);
        }
    }
    Anchor::function(f.entry, &insns, &body)
}

/// A signature for every function the program names.
///
/// Only the named ones: a signature whose name is `sub_401000` identifies
/// nothing, and a library of them would match everything.
pub fn collect_signatures(p: &Program, source: &str) -> Library {
    Library::build(
        p.functions_by_address()
            // An import thunk is four instructions that differ only in the
            // offset they load, and that offset means something different in
            // every binary. Two of them matching across builds is a
            // coincidence, and the loader names them from the relocations
            // anyway, so they are left out.
            .filter(|f| f.name.is_some() && !is_thunk(f))
            .map(|f| {
                let anchor = anchor_of(p, f);
                Signature::new(&anchor, f.name.as_deref().unwrap_or_default(), source)
            })
            .collect(),
    )
}

/// True when a function is a stub that stands in for an imported one.
fn is_thunk(f: &Function) -> bool {
    f.provenance.has(e5r_core::Evidence::ImportThunk)
        || f.name.as_deref().is_some_and(|n| n.ends_with("@plt"))
}

/// One function a library recognized.
#[derive(Debug, Clone)]
pub struct Identified {
    /// Where it is.
    pub addr: e5r_core::Addr,
    /// What it was called before.
    pub was: String,
    /// What the library says it is.
    pub name: String,
    /// How the match was made.
    pub resolution: e5r_db::anchor::Resolution,
    /// Which library it came from.
    pub source: String,
}

/// Everything in a program a library recognizes.
pub fn identify(p: &Program, library: &Library) -> Vec<Identified> {
    let mut out = Vec::new();
    for f in p.functions_by_address() {
        let anchor = anchor_of(p, f);
        let Some(found) = library.identify(&anchor) else {
            continue;
        };
        out.push(Identified {
            addr: f.entry,
            was: f.display_name(),
            name: found.signature.name.clone(),
            resolution: found.resolution,
            source: found.signature.source.clone(),
        });
    }
    out
}
