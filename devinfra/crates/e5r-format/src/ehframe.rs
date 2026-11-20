//! `.eh_frame` walking, for function starts and sizes.
//!
//! Unwind tables are emitted for exception handling, not for us, which is what
//! makes them good evidence: they are generated from the compiler's own idea of
//! where each function begins and ends, and they survive stripping. One FDE per
//! function, each naming a start address and a length.
//!
//! Only the header of each entry is read. The CFI program that follows says how
//! to restore registers and is not needed to answer "where are the functions".

use e5r_core::{Addr, Bits, Error, Reader, Result};

// DW_EH_PE format, low nibble.
const PE_ABSPTR: u8 = 0x00;
const PE_ULEB128: u8 = 0x01;
const PE_UDATA2: u8 = 0x02;
const PE_UDATA4: u8 = 0x03;
const PE_UDATA8: u8 = 0x04;
const PE_SLEB128: u8 = 0x09;
const PE_SDATA2: u8 = 0x0a;
const PE_SDATA4: u8 = 0x0b;
const PE_SDATA8: u8 = 0x0c;
// DW_EH_PE application, high nibble.
const PE_PCREL: u8 = 0x10;
const PE_DATAREL: u8 = 0x30;
const PE_OMIT: u8 = 0xff;

/// What one CIE says about the FDEs that point at it.
#[derive(Clone, Copy, Default)]
struct Cie {
    /// Encoding of an FDE's `pc_begin`.
    fde_encoding: u8,
    /// True when the augmentation string starts with `z`, so entries carry a
    /// length-prefixed augmentation block.
    has_augmentation_data: bool,
}

/// Every `(start, length)` an `.eh_frame` section declares.
///
/// `section_addr` is where the section is mapped, needed because most encodings
/// are relative to the field's own address.
pub fn function_starts(body: &[u8], section_addr: Addr, bits: Bits) -> Result<Vec<(Addr, u64)>> {
    let ptr_size = bits.bytes();
    let r = Reader::le(body);
    let mut out = Vec::new();
    let mut cies: Vec<(u64, Cie)> = Vec::new();
    let mut pos: u64 = 0;

    while pos + 4 <= body.len() as u64 {
        let entry_start = pos;
        let mut e = r.slice_at("eh_frame entry", pos, (body.len() as u64) - pos)?;
        let len32 = e.u32("length")?;
        // Zero length terminates the section.
        if len32 == 0 {
            break;
        }
        let (len, header) = if len32 == 0xffff_ffff {
            (e.u64("extended length")?, 12u64)
        } else {
            (len32 as u64, 4u64)
        };
        let next = entry_start
            .checked_add(header)
            .and_then(|v| v.checked_add(len))
            .ok_or(Error::BadField {
                field: "eh_frame entry length",
                value: len,
                reason: "carries past the end of the address space",
            })?;
        if next > body.len() as u64 {
            // A truncated last entry is common in a damaged file; stop rather
            // than fail, since everything before it is still good.
            break;
        }

        let id = e.u32("CIE id")?;
        if id == 0 {
            let cie = parse_cie(&mut e, ptr_size)?;
            cies.push((entry_start, cie));
        } else {
            // CIE_pointer is a backward distance from the field's own position.
            let id_pos = entry_start + header;
            let cie_at = id_pos.checked_sub(id as u64);
            let cie = cie_at
                .and_then(|a| cies.iter().rev().find(|(at, _)| *at == a).map(|(_, c)| *c))
                .unwrap_or_default();

            let pc_begin_at = section_addr.get().wrapping_add(e.pos() + entry_start);
            let Some(start) = read_encoded(
                &mut e,
                cie.fde_encoding,
                pc_begin_at,
                section_addr,
                ptr_size,
            )?
            else {
                pos = next;
                continue;
            };
            // pc_range uses the same format with no application applied.
            let range = read_encoded(&mut e, cie.fde_encoding & 0x0f, 0, section_addr, ptr_size)?
                .unwrap_or(0);
            if start != 0 {
                out.push((Addr(start), range));
            }
        }
        pos = next;
    }

    out.sort_unstable();
    out.dedup();
    Ok(out)
}

fn parse_cie(e: &mut Reader<'_>, ptr_size: u64) -> Result<Cie> {
    let version = e.u8("CIE version")?;
    let aug_start = e.pos();
    let aug = e
        .data()
        .get(aug_start as usize..)
        .and_then(|s| s.iter().position(|&b| b == 0).map(|n| &s[..n]))
        .unwrap_or(b"");
    e.skip("augmentation string", aug.len() as u64 + 1)?;

    let _code_align = e.uleb128("code alignment")?;
    let _data_align = e.sleb128("data alignment")?;
    if version == 1 {
        e.u8("return address register")?;
    } else {
        e.uleb128("return address register")?;
    }

    let mut cie = Cie {
        fde_encoding: PE_ABSPTR,
        has_augmentation_data: aug.first() == Some(&b'z'),
    };
    if !cie.has_augmentation_data {
        return Ok(cie);
    }

    let aug_len = e.uleb128("augmentation length")?;
    let aug_end = e.pos() + aug_len;
    for c in aug.iter().skip(1) {
        match c {
            b'R' => cie.fde_encoding = e.u8("FDE pointer encoding")?,
            b'L' => {
                e.u8("LSDA encoding")?;
            }
            b'P' => {
                let enc = e.u8("personality encoding")?;
                read_encoded(e, enc, 0, Addr::ZERO, ptr_size)?;
            }
            b'S' | b'B' | b'G' => {}
            _ => break,
        }
    }
    // Trust the declared length over the augmentation string, which is what
    // makes an unknown augmentation character survivable.
    if aug_end <= e.len() as u64 {
        e.seek("augmentation end", aug_end)?;
    }
    Ok(cie)
}

/// Read one DW_EH_PE-encoded pointer. `None` when the encoding says omit.
fn read_encoded(
    e: &mut Reader<'_>,
    enc: u8,
    field_addr: u64,
    section_addr: Addr,
    ptr_size: u64,
) -> Result<Option<u64>> {
    if enc == PE_OMIT {
        return Ok(None);
    }
    let raw: i64 = match enc & 0x0f {
        PE_ABSPTR => {
            if ptr_size == 8 {
                e.u64("pointer")? as i64
            } else {
                e.u32("pointer")? as i64
            }
        }
        PE_ULEB128 => e.uleb128("pointer")? as i64,
        PE_UDATA2 => e.u16("pointer")? as i64,
        PE_UDATA4 => e.u32("pointer")? as i64,
        PE_UDATA8 => e.u64("pointer")? as i64,
        PE_SLEB128 => e.sleb128("pointer")?,
        PE_SDATA2 => e.i16("pointer")? as i64,
        PE_SDATA4 => e.i32("pointer")? as i64,
        PE_SDATA8 => e.i64("pointer")?,
        other => {
            return Err(Error::BadField {
                field: "DW_EH_PE format",
                value: other as u64,
                reason: "is not a pointer format DWARF defines",
            });
        }
    };

    let base = match enc & 0x70 {
        PE_PCREL => field_addr,
        PE_DATAREL => section_addr.get(),
        _ => 0,
    };
    Ok(Some(base.wrapping_add(raw as u64)))
}

#[cfg(test)]
mod tests {
    use super::*;

    /// A CIE with `zR`/sdata4-pcrel and one FDE, built by hand so the test does
    /// not depend on a compiler.
    fn one_fde(pc_rel: i32, range: u32) -> Vec<u8> {
        let mut cie = vec![1u8]; // version
        cie.extend_from_slice(b"zR\0");
        cie.push(1); // code alignment
        cie.push(0x7c); // data alignment, sleb -4
        cie.push(16); // return address register
        cie.push(1); // augmentation length
        cie.push(PE_SDATA4 | PE_PCREL);
        while (cie.len() + 8) % 4 != 0 {
            cie.push(0);
        }
        let mut out = Vec::new();
        out.extend_from_slice(&((cie.len() as u32 + 4).to_le_bytes()));
        out.extend_from_slice(&0u32.to_le_bytes()); // CIE id
        out.extend_from_slice(&cie);

        let cie_end = out.len();
        let mut fde = Vec::new();
        fde.extend_from_slice(&pc_rel.to_le_bytes());
        fde.extend_from_slice(&range.to_le_bytes());
        fde.push(0); // augmentation length
        while (fde.len() + 8) % 4 != 0 {
            fde.push(0);
        }
        out.extend_from_slice(&((fde.len() as u32 + 4).to_le_bytes()));
        // CIE_pointer: distance back from this field to the CIE start.
        out.extend_from_slice(&(cie_end as u32 + 4).to_le_bytes());
        out.extend_from_slice(&fde);
        out
    }

    #[test]
    fn one_fde_yields_one_function() {
        let body = one_fde(0x100, 0x40);
        let f = function_starts(&body, Addr(0x2000), Bits::Bits64).unwrap();
        assert_eq!(f.len(), 1);
        assert_eq!(f[0].1, 0x40);
        // pcrel means the start is relative to the pc_begin field's address,
        // which sits at the section address plus its offset in the section.
        assert!(f[0].0.get() > 0x2000);
    }

    #[test]
    fn a_truncated_tail_keeps_what_came_before() {
        let mut body = one_fde(0x100, 0x40);
        body.extend_from_slice(&0x7fff_ffffu32.to_le_bytes());
        body.extend_from_slice(&[0, 0]);
        let f = function_starts(&body, Addr(0x2000), Bits::Bits64).unwrap();
        assert_eq!(f.len(), 1);
    }

    #[test]
    fn zero_length_terminates() {
        let mut body = one_fde(0x100, 0x40);
        body.extend_from_slice(&0u32.to_le_bytes());
        body.extend_from_slice(&[0xff; 32]);
        assert_eq!(
            function_starts(&body, Addr(0x2000), Bits::Bits64)
                .unwrap()
                .len(),
            1
        );
    }

    #[test]
    fn garbage_does_not_panic() {
        for seed in 0u32..256 {
            let body: Vec<u8> = (0..128u32)
                .map(|i| (i.wrapping_mul(2654435761).wrapping_add(seed) >> 13) as u8)
                .collect();
            let _ = function_starts(&body, Addr(0x1000), Bits::Bits64);
            let _ = function_starts(&body, Addr(0x1000), Bits::Bits32);
        }
    }
}
