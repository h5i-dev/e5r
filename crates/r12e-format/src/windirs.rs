//! The Windows data directories that say where code is and where addresses are.
//!
//! Three of them, none of which the entry point reaches:
//!
//! - The TLS directory. Its callback array runs before the entry point, once
//!   per thread. A packer that does its work there and never returns to the
//!   declared entry point is a shape common enough that missing the array is
//!   missing the program.
//! - The base relocation table. Every absolute address the image embeds is
//!   listed here, which is a map of the image's own pointers whether or not it
//!   is ever rebased.
//! - The load config. Its control-flow-guard function table is the linker's own
//!   list of every address-taken function, and on 32-bit its SafeSEH table is
//!   the list of legal exception handlers.
//!
//! Every pointer these directories hold is an absolute address relative to the
//! image base the file declares, not an RVA, so all of them go through
//! [`Image::addr_of_va`].

use r12e_core::{Addr, AddrRange, Caps, Evidence, Provenance};

use crate::pe::Image;
use crate::{FunctionHint, Object};

/// Pointers accepted in one TLS callback array. The array is NUL-terminated
/// with no count, so something has to stop the walk on a file that never
/// terminates it.
const MAX_TLS_CALLBACKS: u64 = 4096;

/// `IMAGE_TLS_DIRECTORY`, with the callback array already walked.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TlsDirectory {
    /// The template the loader copies into each thread's TLS block. Absent when
    /// the declared bounds are not a range inside the image.
    pub raw_data: Option<AddrRange>,
    /// Where the loader writes the TLS slot index.
    pub index: Option<Addr>,
    /// Address of the callback array itself.
    pub callback_array: Option<Addr>,
    /// Bytes zeroed past the end of the template.
    pub zero_fill: u32,
    /// Alignment and reserved bits.
    pub characteristics: u32,
    /// The callbacks, in the order the loader calls them.
    pub callbacks: Vec<Addr>,
}

/// One base relocation.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct BaseReloc {
    /// The address holding the value to fix up.
    pub addr: Addr,
    /// `IMAGE_REL_BASED_*` type, as [`reloc_kind`] names it.
    pub kind: u8,
}

/// The name of a base relocation type, or `"unknown"`.
pub fn reloc_kind(kind: u8) -> &'static str {
    match kind {
        0 => "absolute",
        1 => "high",
        2 => "low",
        3 => "highlow",
        4 => "highadj",
        5 => "mips jmpaddr / arm mov32 / riscv high20",
        7 => "thumb mov32 / riscv low12i",
        8 => "riscv low12s / loongarch mark la",
        9 => "mips jmpaddr16 / loongarch stack",
        10 => "dir64",
        _ => "unknown",
    }
}

/// `IMAGE_LOAD_CONFIG_DIRECTORY`, the fields that name code or a cookie.
///
/// The directory has grown for twenty years and a given image implements only
/// as much of it as its `Size` says. Everything past that size is absent, not
/// zero, and is reported as absent.
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct LoadConfig {
    /// The `Size` field, which is how much of the structure exists.
    pub size: u32,
    /// The stack cookie's storage.
    pub security_cookie: Option<Addr>,
    /// SafeSEH's table of legal handlers, 32-bit images only.
    pub se_handler_table: Option<Addr>,
    /// Entries the SafeSEH table claims.
    pub se_handler_count: u64,
    /// The handlers themselves, when the table was readable.
    pub se_handlers: Vec<Addr>,
    /// Where the guard check function's pointer lives.
    pub guard_cf_check: Option<Addr>,
    /// Where the guard dispatch function's pointer lives.
    pub guard_cf_dispatch: Option<Addr>,
    /// The guard function table.
    pub guard_cf_function_table: Option<Addr>,
    /// Entries the guard function table claims.
    pub guard_cf_function_count: u64,
    /// `IMAGE_GUARD_*` flags. The top four bits give the extra bytes each guard
    /// table entry carries past its four-byte RVA.
    pub guard_flags: u32,
    /// Every address-taken function the guard table lists.
    pub guard_functions: Vec<Addr>,
}

/// Read the TLS directory and walk its callback array.
pub fn read_tls(
    img: &Image<'_>,
    dir_rva: u32,
    dir_size: u32,
    caps: &Caps,
    obj: &mut Object,
) -> Option<TlsDirectory> {
    if dir_rva == 0 {
        return None;
    }
    let ptr = if img.wide() { 8 } else { 4 };
    let want = ptr * 4 + 8;
    if (dir_size as u64) < want && dir_size != 0 {
        obj.warnings.push(format!(
            "TLS directory is {dir_size} bytes, short of the {want} an IMAGE_TLS_DIRECTORY needs"
        ));
    }
    let at = match img.offset_of(dir_rva) {
        Some(at) => at,
        None => {
            obj.warnings
                .push("TLS directory RVA is not inside any section".into());
            return None;
        }
    };
    let mut d = img
        .reader()
        .slice_at("IMAGE_TLS_DIRECTORY", at, want)
        .ok()?;
    let start = d.uword("StartAddressOfRawData", img.wide()).ok()?;
    let end = d.uword("EndAddressOfRawData", img.wide()).ok()?;
    let index = d.uword("AddressOfIndex", img.wide()).ok()?;
    let callbacks = d.uword("AddressOfCallBacks", img.wide()).ok()?;
    let zero_fill = d.u32("SizeOfZeroFill").ok()?;
    let characteristics = d.u32("Characteristics").ok()?;

    let mut tls = TlsDirectory {
        raw_data: match (img.addr_of_va(start), img.addr_of_va(end)) {
            (Some(s), Some(e)) => AddrRange::new(s, e),
            _ => None,
        },
        index: img.addr_of_va(index),
        callback_array: img.addr_of_va(callbacks),
        zero_fill,
        characteristics,
        callbacks: Vec::new(),
    };

    let Some(array) = tls.callback_array else {
        return Some(tls);
    };
    let Some(mut off) = img.offset_of_addr(array) else {
        obj.warnings.push(format!(
            "TLS callback array is at {array}, which no section maps; no callbacks were read"
        ));
        return Some(tls);
    };
    // The array has no count, so the walk is bounded three ways: by the bytes
    // left in the section that holds it, by the cap, and by the terminator.
    let room = img
        .section_bytes_after(off)
        .unwrap_or_else(|| img.len().saturating_sub(off));
    let limit = (room / ptr).min(MAX_TLS_CALLBACKS).min(caps.symbols);
    for i in 0..limit {
        let Ok(mut slot) = img.reader().slice_at("TLS callback", off, ptr) else {
            break;
        };
        let Ok(va) = slot.uword("callback", img.wide()) else {
            break;
        };
        off += ptr;
        if va == 0 {
            break;
        }
        let Some(addr) = img.addr_of_va(va) else {
            obj.warnings.push(format!(
                "TLS callback {i} is {va:#x}, which is below the image base"
            ));
            continue;
        };
        if !img.is_code(addr) {
            obj.warnings.push(format!(
                "TLS callback {i} points at {addr}, which is not executable; not treated as a \
                 function"
            ));
            continue;
        }
        tls.callbacks.push(addr);
        obj.function_hints.push(FunctionHint {
            addr,
            size: None,
            name: Some(format!("tls_callback_{i}")),
            provenance: Provenance::new(Evidence::InitArray),
        });
    }
    if tls.callbacks.len() as u64 == limit && limit != 0 {
        obj.warnings.push(format!(
            "TLS callback array reached {limit} entries without a terminator; the walk stopped \
             there"
        ));
    }
    Some(tls)
}

/// Walk the base relocation table.
///
/// Each block states its own size, so the one thing this must never do is trust
/// it: a block claiming fewer than its own eight header bytes would leave the
/// cursor where it was and the walk would not end.
pub fn read_relocations(
    img: &Image<'_>,
    dir_rva: u32,
    dir_size: u32,
    caps: &Caps,
    obj: &mut Object,
) -> Vec<BaseReloc> {
    let mut out = Vec::new();
    if dir_rva == 0 || dir_size == 0 {
        return out;
    }
    let Some(start) = img.offset_of(dir_rva) else {
        obj.warnings
            .push("base relocation directory RVA is not inside any section".into());
        return out;
    };
    // The table ends where the directory says, where the file ends, or where
    // the section holding it ends, whichever comes first.
    let room = img
        .section_bytes_after(start)
        .unwrap_or_else(|| img.len().saturating_sub(start));
    let end = start.saturating_add((dir_size as u64).min(room));
    let mut at = start;
    while at + 8 <= end {
        let Ok(mut h) = img.reader().slice_at("base relocation block", at, 8) else {
            break;
        };
        let (Ok(page), Ok(size)) = (h.u32("PageRVA"), h.u32("BlockSize")) else {
            break;
        };
        if size == 0 {
            break;
        }
        if (size as u64) < 8 {
            obj.warnings.push(format!(
                "base relocation block at file offset {at:#x} claims {size} bytes, fewer than its \
                 own header; the walk stopped"
            ));
            break;
        }
        let body = (size as u64 - 8).min(end - at - 8);
        let entries = body / 2;
        let mut i = 0u64;
        while i < entries {
            let Ok(mut e) = img.reader().slice_at("base relocation", at + 8 + i * 2, 2) else {
                break;
            };
            let Ok(word) = e.u16("entry") else { break };
            i += 1;
            let kind = (word >> 12) as u8;
            // Type 0 is padding to a four-byte boundary, not a fixup.
            if kind == 0 {
                continue;
            }
            // HIGHADJ carries its addend in the next halfword, which is data
            // rather than another entry.
            if kind == 4 {
                i += 1;
            }
            if out.len() as u64 >= caps.relocations {
                obj.warnings.push(format!(
                    "base relocation table passed the cap of {} entries; the rest was not read",
                    caps.relocations
                ));
                return out;
            }
            out.push(BaseReloc {
                addr: img.addr_of(page.wrapping_add((word & 0xfff) as u32)),
                kind,
            });
        }
        // size is at least 8, so the cursor always moves.
        at += size as u64;
    }
    out
}

// Field offsets, which differ between the two widths because the pointers do.
// Named rather than computed so each one can be checked against winnt.h.
const LC32: LoadConfigLayout = LoadConfigLayout {
    ptr: 4,
    security_cookie: 0x3c,
    se_handler_table: 0x40,
    guard_cf_check: 0x48,
    guard_cf_function_table: 0x50,
    guard_flags: 0x58,
};
const LC64: LoadConfigLayout = LoadConfigLayout {
    ptr: 8,
    security_cookie: 0x58,
    se_handler_table: 0x60,
    guard_cf_check: 0x70,
    guard_cf_function_table: 0x80,
    guard_flags: 0x90,
};

struct LoadConfigLayout {
    ptr: u64,
    security_cookie: u64,
    se_handler_table: u64,
    guard_cf_check: u64,
    guard_cf_function_table: u64,
    guard_flags: u64,
}

/// Read the load config, the SafeSEH handler table and the guard function
/// table.
///
/// The addresses these tables hold are function entries, and the linker put
/// them there. They are returned rather than turned into hints: `Evidence` has
/// no variant for "a table the loader validates calls against", and labelling
/// them as something else would make the strength a lie. See the module
/// documentation in `pe.rs` for the one-line change that would fix it.
pub fn read_load_config(
    img: &Image<'_>,
    dir_rva: u32,
    dir_size: u32,
    caps: &Caps,
    obj: &mut Object,
) -> Option<LoadConfig> {
    if dir_rva == 0 {
        return None;
    }
    let l = if img.wide() { &LC64 } else { &LC32 };
    let at = match img.offset_of(dir_rva) {
        Some(at) => at,
        None => {
            obj.warnings
                .push("load config directory RVA is not inside any section".into());
            return None;
        }
    };
    let mut head = img.reader().slice_at("load config Size", at, 4).ok()?;
    let declared = head.u32("Size").ok()?;
    // The structure is only as long as it says, and the directory entry is a
    // second opinion on that. Take the smaller, and never read past it.
    let size = (declared as u64)
        .min(if dir_size == 0 {
            u64::MAX
        } else {
            dir_size as u64
        })
        .min(img.len().saturating_sub(at));
    if declared as u64 > size {
        obj.warnings.push(format!(
            "load config claims {declared} bytes, of which {size} are present"
        ));
    }

    let field = |off: u64| -> Option<u64> {
        if off + l.ptr > size {
            return None;
        }
        img.reader()
            .slice_at("load config field", at + off, l.ptr)
            .ok()?
            .uword("field", l.ptr == 8)
            .ok()
    };
    let mut cfg = LoadConfig {
        size: declared,
        security_cookie: field(l.security_cookie).and_then(|v| img.addr_of_va(v)),
        se_handler_table: field(l.se_handler_table).and_then(|v| img.addr_of_va(v)),
        se_handler_count: field(l.se_handler_table + l.ptr).unwrap_or(0),
        se_handlers: Vec::new(),
        guard_cf_check: field(l.guard_cf_check).and_then(|v| img.addr_of_va(v)),
        guard_cf_dispatch: field(l.guard_cf_check + l.ptr).and_then(|v| img.addr_of_va(v)),
        guard_cf_function_table: field(l.guard_cf_function_table).and_then(|v| img.addr_of_va(v)),
        guard_cf_function_count: field(l.guard_cf_function_table + l.ptr).unwrap_or(0),
        guard_flags: if l.guard_flags + 4 <= size {
            img.reader()
                .slice_at("GuardFlags", at + l.guard_flags, 4)
                .ok()
                .and_then(|mut r| r.u32("GuardFlags").ok())
                .unwrap_or(0)
        } else {
            0
        },
        guard_functions: Vec::new(),
    };

    // SafeSEH: a sorted array of RVAs, 32-bit images only.
    if let Some(table) = cfg.se_handler_table {
        cfg.se_handlers = read_rva_table(
            img,
            table,
            cfg.se_handler_count,
            4,
            "SafeSEH handler table",
            caps,
            obj,
        );
    }
    // Control Flow Guard: an RVA plus however many metadata bytes the top of
    // GuardFlags says each entry carries.
    if let Some(table) = cfg.guard_cf_function_table {
        let stride = 4 + ((cfg.guard_flags >> 28) & 0xf) as u64;
        cfg.guard_functions = read_rva_table(
            img,
            table,
            cfg.guard_cf_function_count,
            stride,
            "control flow guard function table",
            caps,
            obj,
        );
    }
    // Both tables were built by the linker out of real function entries, and
    // the loader enforces them at run time, so an address in one is a function
    // whatever else the image says. Anything not executable is a warning, not
    // a hint: it would mean the table disagrees with the section flags, which
    // is worth saying and not worth believing.
    for (what, addrs) in [
        ("safeseh_handler", &cfg.se_handlers),
        ("guard_function", &cfg.guard_functions),
    ] {
        for a in addrs {
            if !img.is_code(*a) {
                obj.warnings
                    .push(format!("{what} at {a} is not in executable memory"));
                continue;
            }
            obj.function_hints.push(FunctionHint {
                addr: *a,
                size: None,
                name: None,
                provenance: Provenance::new(Evidence::GuardTable),
            });
        }
    }
    Some(cfg)
}

/// An array of RVAs at an absolute address, bounded by the file before the
/// claimed count is believed.
fn read_rva_table(
    img: &Image<'_>,
    table: Addr,
    count: u64,
    stride: u64,
    what: &str,
    caps: &Caps,
    obj: &mut Object,
) -> Vec<Addr> {
    let mut out = Vec::new();
    if count == 0 || stride < 4 {
        return out;
    }
    let Some(at) = img.offset_of_addr(table) else {
        obj.warnings
            .push(format!("{what} is at {table}, which no section maps"));
        return out;
    };
    let room = img
        .section_bytes_after(at)
        .unwrap_or_else(|| img.len().saturating_sub(at));
    let fits = room / stride;
    let n = count.min(fits).min(caps.symbols);
    if n < count {
        obj.warnings.push(format!(
            "{what} claims {count} entries, of which {n} fit in the file"
        ));
    }
    for i in 0..n {
        let Ok(mut e) = img.reader().slice_at("table entry", at + i * stride, 4) else {
            break;
        };
        let Ok(rva) = e.u32("function RVA") else {
            break;
        };
        if rva == 0 {
            continue;
        }
        let addr = img.addr_of(rva);
        if img.is_code(addr) {
            out.push(addr);
        } else {
            obj.warnings.push(format!(
                "{what} entry {i} points at {addr}, which is not executable"
            ));
        }
    }
    out
}
