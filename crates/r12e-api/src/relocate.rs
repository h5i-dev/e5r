//! Dynamic relocations, applied so a shared library's data reads the way the
//! loader will see it.
//!
//! A position independent library writes zero wherever a pointer goes and
//! leaves a relocation saying what belongs there. Every virtual table in
//! `/usr/lib/*/libstdc++.so.6` is zeroes in the file for that reason, and so is
//! every type-information pointer in one: 2,766 of its relocations name a
//! symbol and 1,056 are self-relative. Reading the bytes as they sit gives
//! nothing, and "this library has no classes" would be a wrong answer produced
//! with no warning.
//!
//! This is `r12e-format`'s job and belongs there, next to the relocatable-object
//! path that already does the same thing for `.o` files. It is here because
//! that path does not yet cover `ET_DYN`, and a class recovery that cannot read
//! a shared library is not worth measuring.
//!
//! Two kinds are applied and no more. A relative relocation needs nothing but
//! its addend. An absolute one needs the symbol, and only a symbol this file
//! defines has an address here: an undefined one is filled in by the loader
//! from some other library, and writing a guess would point a virtual table at
//! an address that is not the function. Jump slots are left alone, because the
//! container reader already resolves the PLT.

use r12e_core::{Addr, Arch, Bits, Endian};
use r12e_format::Object;

/// What each architecture calls the relocations that can be applied here.
struct Kinds {
    /// Add the addend to the load address. No symbol.
    relative: u64,
    /// Store a symbol's address plus the addend, pointer width.
    absolute: u64,
    /// A global data slot, computed the same way as an absolute one.
    global: u64,
}

/// Apply every dynamic relocation whose answer is in this file.
///
/// Call it on a freshly loaded object, before `analyze`, so every later pass
/// sees the same bytes. Returns how many were applied, which is zero for a
/// non-relocatable executable, and zero for an architecture whose relocation
/// numbers are not listed here.
pub fn apply_relative_relocations(obj: &mut Object) -> usize {
    let Some(kinds) = kinds_of(&obj.arch) else {
        return 0;
    };
    let wide = obj.bits == Bits::Bits64;
    let little = obj.endian == Endian::Little;
    let base = obj.image_base.get();
    let w = if wide { 8 } else { 4 };
    let symbols = dynamic_symbol_values(obj, wide, little);

    // `.rela.dyn` carries the addend in the entry; `.rel.dyn` leaves it in the
    // word being relocated.
    let mut applied = 0;
    for (name, explicit_addend) in [(".rela.dyn", true), (".rel.dyn", false)] {
        let Some(section) = obj.section(name) else {
            continue;
        };
        let step = match (wide, explicit_addend) {
            (true, true) => 24,
            (true, false) => 16,
            (false, true) => 12,
            (false, false) => 8,
        };
        let start = section.range.start();
        let len = section.range.end().get().saturating_sub(start.get());
        let Some(bytes) = obj.memory.slice(start, len).map(<[u8]>::to_vec) else {
            continue;
        };

        for entry in bytes.chunks_exact(step) {
            let offset = int(&entry[..w], little);
            let info = int(&entry[w..2 * w], little);
            // The low part of `r_info` is the type and the high part is the
            // symbol index, at different widths on the two pointer sizes.
            let (ty, symbol) = if wide {
                (info & 0xffff_ffff, info >> 32)
            } else {
                (info & 0xff, info >> 8)
            };
            let at = Addr(base.wrapping_add(offset));
            let addend = if explicit_addend {
                int(&entry[2 * w..3 * w], little)
            } else {
                match obj.memory.read_ptr(at, w as u64, little) {
                    Ok(v) => v,
                    Err(_) => continue,
                }
            };
            let value = if ty == kinds.relative {
                base.wrapping_add(addend)
            } else if ty == kinds.absolute || ty == kinds.global {
                // Only a symbol this file defines. Zero means undefined, and
                // the loader will fill it from somewhere this file cannot see.
                match symbols.get(symbol as usize) {
                    Some(0) | None => continue,
                    Some(v) => base.wrapping_add(*v).wrapping_add(addend),
                }
            } else {
                continue;
            };
            let le = value.to_le_bytes();
            let be = value.to_be_bytes();
            let patch = if little { &le[..w] } else { &be[8 - w..] };
            if obj.memory.patch(at, patch) {
                applied += 1;
            }
        }
    }
    applied
}

/// The address of each dynamic symbol, by its index in `.dynsym`.
///
/// A relocation names its symbol by index, and the loaded object's symbol list
/// is sorted by address, so the table has to be read again to get the order
/// back. Zero means the symbol is not defined here.
fn dynamic_symbol_values(obj: &Object, wide: bool, little: bool) -> Vec<u64> {
    let Some(section) = obj.section(".dynsym") else {
        return Vec::new();
    };
    let step = if wide { 24 } else { 16 };
    let start = section.range.start();
    let len = section.range.end().get().saturating_sub(start.get());
    let Some(bytes) = obj.memory.slice(start, len) else {
        return Vec::new();
    };
    bytes
        .chunks_exact(step)
        .map(|e| {
            // `st_shndx` of zero is an undefined symbol whatever `st_value`
            // says, and on 64-bit the value sits after the index while on
            // 32-bit it sits before it.
            let (shndx, value) = if wide {
                (int(&e[6..8], little), int(&e[8..16], little))
            } else {
                (int(&e[14..16], little), int(&e[4..8], little))
            };
            if shndx == 0 { 0 } else { value }
        })
        .collect()
}

/// The relocation numbers an architecture's ABI publishes.
fn kinds_of(arch: &Arch) -> Option<Kinds> {
    match arch {
        Arch::X86_64 => Some(Kinds {
            relative: 8,
            absolute: 1,
            global: 6,
        }),
        Arch::X86 => Some(Kinds {
            relative: 8,
            absolute: 1,
            global: 6,
        }),
        Arch::AArch64 => Some(Kinds {
            relative: 1027,
            absolute: 257,
            global: 1025,
        }),
        Arch::Arm | Arch::Thumb => Some(Kinds {
            relative: 23,
            absolute: 2,
            global: 21,
        }),
        _ => None,
    }
}

fn int(bytes: &[u8], little: bool) -> u64 {
    let mut value = 0u64;
    if little {
        for (i, b) in bytes.iter().enumerate() {
            value |= (*b as u64) << (8 * i);
        }
    } else {
        for b in bytes {
            value = (value << 8) | *b as u64;
        }
    }
    value
}
