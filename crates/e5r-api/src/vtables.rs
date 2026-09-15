//! Virtual tables, and what they say about a binary's classes.
//!
//! Under the Itanium ABI a virtual table is an array of pointers preceded by
//! two words: how far the object's start is from this subobject, and a pointer
//! to the type information. The address a class's objects carry points past
//! those two, at the first function.
//!
//! Two ways to find them, and both are reported with what they rest on. A
//! `_ZTV` symbol names a table outright, which is a fact. Otherwise a run of
//! pointers into executable memory that something takes the address of is a
//! table by inference, and the inference is weaker the shorter the run.

use e5r_analysis::Program;
use e5r_core::{Addr, Evidence};

/// One virtual table.
#[derive(Debug, Clone)]
pub struct VTable {
    /// Where the table starts, which is the offset-to-top word.
    pub addr: Addr,
    /// The address objects of this class carry: the first function slot.
    pub entry: Addr,
    /// The class, demangled, when a symbol named it.
    pub class: Option<String>,
    /// How far the complete object's start is from this subobject.
    pub offset_to_top: i64,
    /// Where the type information lives, when there is any.
    pub typeinfo: Option<Addr>,
    /// The virtual functions, in slot order.
    pub methods: Vec<Addr>,
    /// What the table rests on.
    pub evidence: Evidence,
}

/// The smallest run of code pointers that counts as a table without a symbol.
const MIN_INFERRED_SLOTS: usize = 3;

/// Every virtual table the program appears to contain.
pub fn vtables(p: &Program) -> Vec<VTable> {
    let mut out: Vec<VTable> = Vec::new();
    // The extent of every table already found, so the scan does not report a
    // second table one word into the first.
    let mut claimed: Vec<(u64, u64)> = Vec::new();

    // Named tables first: a symbol is a fact and takes precedence over
    // anything the scan would have guessed about the same address.
    for symbol in &p.object.symbols {
        if !symbol.name.starts_with("_ZTV") || symbol.addr == Addr::ZERO {
            continue;
        }
        // A `_ZTV` symbol names the start of the table, which is the
        // offset-to-top word; the address objects carry is two words later.
        // The symbol's declared size says exactly how many slots there are,
        // which matters for a class with pure virtual functions: those slots
        // hold a stub the object file has not resolved, and a scan that stops
        // at the first one would cut the table short.
        let slots = (symbol.size >= 24).then(|| (symbol.size as usize - 16) / 8);
        let table = read(
            p,
            symbol.addr.wrapping_offset(16),
            Evidence::SymbolTable,
            slots,
        )
        // A class with virtual bases has its virtual base offsets in front of
        // the offset-to-top word, so the address its objects carry is further
        // in than two words and the straight read finds no functions there.
        .or_else(|| {
            let entry = address_point(p, symbol.addr, symbol.size)?;
            // The size is the file's to choose, so one large enough to wrap
            // would put the end of the table before its start.
            let past = symbol.addr.get().checked_add(symbol.size)?;
            let slots = past.checked_sub(entry.get()).map(|n| n as usize / 8);
            read(p, entry, Evidence::SymbolTable, slots)
        });
        let Some(table) = table else {
            continue;
        };
        claimed.push((table.addr.get(), extent(&table)));
        out.push(VTable {
            class: class_of(&symbol.name),
            ..table
        });
    }

    // Then the scan, over the sections a compiler puts tables in.
    for section in &p.object.sections {
        let relocated = section.name.starts_with(".data.rel.ro")
            || section.name == ".rodata"
            || section.name == ".data.rel.ro";
        if !relocated || section.range.is_empty() {
            continue;
        }
        let mut at = section.range.start();
        while at.get() + 24 <= section.range.end().get() {
            if claimed
                .iter()
                .any(|(lo, hi)| at.get() >= *lo && at.get() < *hi)
            {
                at = at.wrapping_offset(8);
                continue;
            }
            match read(p, at.wrapping_offset(16), Evidence::DataPointer, None) {
                Some(table) if table.methods.len() >= MIN_INFERRED_SLOTS => {
                    let next = extent(&table);
                    claimed.push((table.addr.get(), next));
                    out.push(table);
                    at = Addr(next);
                }
                _ => at = at.wrapping_offset(8),
            }
        }
    }

    out.sort_by_key(|t| t.addr);
    out.dedup_by_key(|t| t.addr);
    out
}

/// One past the last byte a table occupies.
fn extent(t: &VTable) -> u64 {
    t.entry.get() + t.methods.len() as u64 * 8
}

/// Read a table whose first function slot is at `entry`.
///
/// `slots` is how many there are when something said; otherwise the run of
/// code pointers decides where it ends.
fn read(p: &Program, entry: Addr, evidence: Evidence, slots: Option<usize>) -> Option<VTable> {
    // The two words before the slots: the offset to the top of the object and
    // the type information.
    let addr = Addr(entry.get().checked_sub(16)?);
    let offset_to_top = word(p, addr)? as i64;
    let typeinfo = word(p, addr.wrapping_offset(8))?;
    // A table has a small offset-to-top: a large one is not a table, it is two
    // pointers that happen to sit next to each other.
    if offset_to_top.unsigned_abs() > 1 << 20 {
        return None;
    }

    let mut methods = Vec::new();
    let mut slot = entry;
    let limit = slots.unwrap_or(4096);
    let mut code_slots = 0;
    while methods.len() < limit {
        let Some(target) = word(p, slot) else { break };
        if is_code(p, Addr(target)) {
            code_slots += 1;
        } else if target == 0 && slots.is_some() {
            // A pure virtual function, or an entry whose symbol this file does
            // not define. The declared size says it is still a slot.
        } else {
            break;
        }
        methods.push(Addr(target));
        slot = slot.wrapping_offset(8);
    }
    // At least one real function: a run of zeroes is not a table.
    if code_slots == 0 {
        return None;
    }
    Some(VTable {
        addr,
        entry,
        class: None,
        offset_to_top,
        typeinfo: (typeinfo != 0).then_some(Addr(typeinfo)),
        methods,
        evidence,
    })
}

fn word(p: &Program, at: Addr) -> Option<u64> {
    let bytes = p.object.memory.slice(at, 8)?;
    Some(u64::from_le_bytes(bytes.try_into().ok()?))
}

/// True when an address is inside something the container marked executable.
fn is_code(p: &Program, at: Addr) -> bool {
    at != Addr::ZERO
        && p.object
            .sections
            .iter()
            .any(|s| s.exec && s.range.contains(at))
}

/// Where a virtual table group's address point is.
///
/// The group a `_ZTV` symbol names is a run of sub-tables, and each is some
/// number of virtual call and virtual base offsets followed by the
/// offset-to-top word, the type information and the functions. Only a class
/// with virtual bases has anything in front, so this walks forward a word at a
/// time to the first place where two words are followed by a function.
fn address_point(p: &Program, start: Addr, size: u64) -> Option<Addr> {
    // A prefix of more than a few words would mean a class with dozens of
    // virtual bases, and walking further than the symbol says is not walking
    // inside this table any more.
    let words = (size / 8).min(64);
    for i in 1..words.saturating_sub(2) {
        let at = start.wrapping_offset(i as i64 * 8);
        if is_code(p, Addr(word(p, at.wrapping_offset(16))?)) {
            return Some(at.wrapping_offset(16));
        }
    }
    None
}

/// The class a vtable symbol names, demangled.
fn class_of(symbol: &str) -> Option<String> {
    // The mangled name of the class follows `_ZTV`, so putting a prefix the
    // demangler recognizes back on it gives the class name. `_ZTI` rather
    // than a wrapped nested name, because a class that is already nested
    // carries its own `N...E` and wrapping that in another one is not a name.
    let inner = symbol.strip_prefix("_ZTV")?;
    let (_, demangled) = e5r_types::demangle(&format!("_ZTI{inner}"))?;
    Some(demangled.strip_prefix("typeinfo for ")?.to_string())
}
