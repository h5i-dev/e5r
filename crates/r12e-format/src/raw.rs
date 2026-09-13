//! A flat image with no container: firmware, a shellcode blob, a memory dump.
//!
//! The caller supplies the base address and the architecture, since nothing in
//! the bytes says either.

use std::collections::BTreeMap;

use r12e_core::{Addr, AddrRange, Error, MemoryMap, Perms, Result, Segment};

use crate::{Format, LoadOptions, Object, Section};

/// Map the whole buffer read-write-execute at the requested base.
pub fn load(data: &[u8], opts: &LoadOptions) -> Result<Object> {
    let arch = opts
        .arch
        .clone()
        .ok_or_else(|| Error::unsupported("a raw image needs an architecture"))?;
    let base = opts.base.unwrap_or(Addr::ZERO);
    let range = AddrRange::sized(base, data.len() as u64).ok_or(Error::BadField {
        field: "base address",
        value: base.get(),
        reason: "puts the end of the image past the end of the address space",
    })?;

    let mut memory = MemoryMap::new();
    memory.add(Segment::new(range, Perms::RWX, "image", 0, data.to_vec())?);

    let bits = arch.bits();
    Ok(Object {
        format: Format::Raw,
        endian: r12e_core::Endian::Little,
        bits,
        arch,
        entry: Some(base),
        image_base: base,
        pic: false,
        memory,
        sections: vec![Section {
            name: "image".into(),
            range,
            file_offset: 0,
            file_size: data.len() as u64,
            exec: true,
            write: true,
            kind: 0,
        }],
        symbols: Vec::new(),
        imports: Vec::new(),
        exports: Vec::new(),
        function_hints: Vec::new(),
        metadata: BTreeMap::new(),
        warnings: Vec::new(),
    })
}
