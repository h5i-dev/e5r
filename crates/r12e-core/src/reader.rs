//! Bounds-checked cursor. Loaders read through this and never index a slice,
//! which is the whole no-panic story for parsing.
//!
//! Every read names what it is reading; the name travels into the error.
//! Endianness lives on the reader because a container decides it once.

use crate::arch::Endian;
use crate::error::{Error, Result};

/// A cursor over bytes that cannot read past the end.
#[derive(Clone, Copy)]
pub struct Reader<'a> {
    data: &'a [u8],
    pos: usize,
    endian: Endian,
}

impl<'a> Reader<'a> {
    /// A reader positioned at the start of `data`.
    pub fn new(data: &'a [u8], endian: Endian) -> Reader<'a> {
        Reader {
            data,
            pos: 0,
            endian,
        }
    }

    /// A little-endian reader, for the case where the format fixes the order.
    pub fn le(data: &'a [u8]) -> Reader<'a> {
        Reader::new(data, Endian::Little)
    }

    /// The whole buffer, ignoring the cursor.
    pub fn data(&self) -> &'a [u8] {
        self.data
    }

    /// Total bytes available.
    pub fn len(&self) -> usize {
        self.data.len()
    }

    /// True when there are no bytes at all.
    pub fn is_empty(&self) -> bool {
        self.data.is_empty()
    }

    /// The cursor position.
    pub fn pos(&self) -> u64 {
        self.pos as u64
    }

    /// Bytes between the cursor and the end.
    pub fn remaining(&self) -> usize {
        self.data.len() - self.pos
    }

    /// The byte order later reads will use.
    pub fn endian(&self) -> Endian {
        self.endian
    }

    /// Change the byte order for later reads. A container header decides this
    /// once, so this is called once per file.
    pub fn set_endian(&mut self, endian: Endian) {
        self.endian = endian;
    }

    /// Move the cursor to an absolute offset.
    pub fn seek(&mut self, what: &'static str, offset: u64) -> Result<()> {
        let off = usize::try_from(offset).map_err(|_| Error::OutOfBounds {
            what,
            offset,
            len: 0,
            available: self.data.len() as u64,
        })?;
        if off > self.data.len() {
            return Err(Error::OutOfBounds {
                what,
                offset,
                len: 0,
                available: self.data.len() as u64,
            });
        }
        self.pos = off;
        Ok(())
    }

    /// Advance the cursor without reading.
    pub fn skip(&mut self, what: &'static str, n: u64) -> Result<()> {
        let at = self.pos as u64;
        self.seek(
            what,
            at.checked_add(n).ok_or(Error::OutOfBounds {
                what,
                offset: at,
                len: n,
                available: self.data.len() as u64,
            })?,
        )
    }

    /// A reader over a sub-range. A parser handed one cannot read outside it.
    pub fn slice_at(&self, what: &'static str, offset: u64, len: u64) -> Result<Reader<'a>> {
        Ok(Reader {
            data: self.bytes_at(what, offset, len)?,
            pos: 0,
            endian: self.endian,
        })
    }

    /// Borrow `len` bytes at an absolute offset without moving the cursor.
    pub fn bytes_at(&self, what: &'static str, offset: u64, len: u64) -> Result<&'a [u8]> {
        let available = self.data.len() as u64;
        let end = offset.checked_add(len).ok_or(Error::OutOfBounds {
            what,
            offset,
            len,
            available,
        })?;
        if end > available {
            return Err(Error::OutOfBounds {
                what,
                offset,
                len,
                available,
            });
        }
        // Both casts are safe: end <= data.len(), which is a usize.
        Ok(&self.data[offset as usize..end as usize])
    }

    /// Read `len` bytes at the cursor and advance.
    pub fn bytes(&mut self, what: &'static str, len: u64) -> Result<&'a [u8]> {
        let out = self.bytes_at(what, self.pos as u64, len)?;
        self.pos += out.len();
        Ok(out)
    }

    /// Read a fixed-size array at the cursor and advance.
    pub fn array<const N: usize>(&mut self, what: &'static str) -> Result<[u8; N]> {
        let b = self.bytes(what, N as u64)?;
        let mut out = [0u8; N];
        out.copy_from_slice(b);
        Ok(out)
    }

    /// Read one byte.
    pub fn u8(&mut self, what: &'static str) -> Result<u8> {
        Ok(self.array::<1>(what)?[0])
    }

    /// Read one byte as signed.
    pub fn i8(&mut self, what: &'static str) -> Result<i8> {
        Ok(self.u8(what)? as i8)
    }

    /// Read a 16-bit unsigned value in the reader's byte order.
    pub fn u16(&mut self, what: &'static str) -> Result<u16> {
        let b = self.array::<2>(what)?;
        Ok(match self.endian {
            Endian::Little => u16::from_le_bytes(b),
            Endian::Big => u16::from_be_bytes(b),
        })
    }

    /// Read a 32-bit unsigned value in the reader's byte order.
    pub fn u32(&mut self, what: &'static str) -> Result<u32> {
        let b = self.array::<4>(what)?;
        Ok(match self.endian {
            Endian::Little => u32::from_le_bytes(b),
            Endian::Big => u32::from_be_bytes(b),
        })
    }

    /// Read a 64-bit unsigned value in the reader's byte order.
    pub fn u64(&mut self, what: &'static str) -> Result<u64> {
        let b = self.array::<8>(what)?;
        Ok(match self.endian {
            Endian::Little => u64::from_le_bytes(b),
            Endian::Big => u64::from_be_bytes(b),
        })
    }

    /// Read a 16-bit signed value in the reader's byte order.
    pub fn i16(&mut self, what: &'static str) -> Result<i16> {
        Ok(self.u16(what)? as i16)
    }

    /// Read a 32-bit signed value in the reader's byte order.
    pub fn i32(&mut self, what: &'static str) -> Result<i32> {
        Ok(self.u32(what)? as i32)
    }

    /// Read a 64-bit signed value in the reader's byte order.
    pub fn i64(&mut self, what: &'static str) -> Result<i64> {
        Ok(self.u64(what)? as i64)
    }

    /// Read 4 or 8 bytes, widened to `u64`. ELF and Mach-O differ only here,
    /// so one method keeps their parsers from being two copies.
    pub fn uword(&mut self, what: &'static str, wide: bool) -> Result<u64> {
        if wide {
            self.u64(what)
        } else {
            Ok(self.u32(what)? as u64)
        }
    }

    /// A NUL-terminated string at an absolute offset, terminator excluded.
    /// Unterminated is an error, not a silent truncation.
    pub fn cstr_at(&self, what: &'static str, offset: u64, max: u64) -> Result<&'a [u8]> {
        let available = self.data.len() as u64;
        if offset >= available {
            return Err(Error::OutOfBounds {
                what,
                offset,
                len: 1,
                available,
            });
        }
        let start = offset as usize;
        let limit = ((offset + max).min(available)) as usize;
        match self.data[start..limit].iter().position(|&b| b == 0) {
            Some(n) => Ok(&self.data[start..start + n]),
            None => Err(Error::BadField {
                field: what,
                value: offset,
                reason: "starts a string with no NUL terminator before the end of the table",
            }),
        }
    }

    /// An unsigned LEB128 value at the cursor, as DWARF and Mach-O use.
    pub fn uleb128(&mut self, what: &'static str) -> Result<u64> {
        let mut out: u64 = 0;
        let mut shift = 0u32;
        loop {
            let b = self.u8(what)?;
            if shift < 64 {
                out |= ((b & 0x7f) as u64) << shift;
            } else if b & 0x7f != 0 {
                return Err(Error::BadField {
                    field: what,
                    value: b as u64,
                    reason: "continues a LEB128 past 64 bits of significance",
                });
            }
            shift += 7;
            if b & 0x80 == 0 {
                return Ok(out);
            }
            if shift > 70 {
                return Err(Error::BadField {
                    field: what,
                    value: shift as u64,
                    reason: "makes a LEB128 longer than any 64-bit value needs",
                });
            }
        }
    }

    /// A signed LEB128 value at the cursor.
    pub fn sleb128(&mut self, what: &'static str) -> Result<i64> {
        let mut out: i64 = 0;
        let mut shift = 0u32;
        loop {
            let b = self.u8(what)?;
            if shift < 64 {
                out |= ((b & 0x7f) as i64) << shift;
            }
            shift += 7;
            if b & 0x80 == 0 {
                if shift < 64 && b & 0x40 != 0 {
                    out |= -1i64 << shift;
                }
                return Ok(out);
            }
            if shift > 70 {
                return Err(Error::BadField {
                    field: what,
                    value: shift as u64,
                    reason: "makes a LEB128 longer than any 64-bit value needs",
                });
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn truncated_reads_error_rather_than_panic() {
        let mut r = Reader::le(&[1, 2, 3]);
        assert!(r.u32("header").is_err());
        // The cursor did not move, so a caller that recovers is not now
        // misaligned.
        assert_eq!(r.pos(), 0);
        assert_eq!(r.u16("half").unwrap(), 0x0201);
    }

    #[test]
    fn offset_plus_len_cannot_wrap() {
        let r = Reader::le(&[0u8; 16]);
        let e = r.bytes_at("section", u64::MAX - 4, 16).unwrap_err();
        assert!(matches!(e, Error::OutOfBounds { .. }));
    }

    #[test]
    fn endianness_is_a_property_of_the_reader() {
        let bytes = [0x12, 0x34];
        assert_eq!(
            Reader::new(&bytes, Endian::Little).u16("x").unwrap(),
            0x3412
        );
        assert_eq!(Reader::new(&bytes, Endian::Big).u16("x").unwrap(), 0x1234);
    }

    #[test]
    fn slices_cannot_see_outside_themselves() {
        let r = Reader::le(&[0, 1, 2, 3, 4, 5, 6, 7]);
        let mut s = r.slice_at("body", 2, 3).unwrap();
        assert_eq!(s.len(), 3);
        assert_eq!(s.bytes("all", 3).unwrap(), &[2, 3, 4]);
        assert!(s.u8("past the end").is_err());
    }

    #[test]
    fn unterminated_strings_are_an_error() {
        let r = Reader::le(b"name\0tail");
        assert_eq!(r.cstr_at("strtab", 0, 64).unwrap(), b"name");
        assert!(r.cstr_at("strtab", 5, 64).is_err());
        let ok = Reader::le(b"abc\0");
        assert_eq!(ok.cstr_at("strtab", 0, 64).unwrap(), b"abc");
    }

    #[test]
    fn leb128_round_trips_the_dwarf_examples() {
        // Values from the DWARF 5 specification, appendix C.
        assert_eq!(Reader::le(&[0x7f]).uleb128("v").unwrap(), 127);
        assert_eq!(Reader::le(&[0x80, 0x01]).uleb128("v").unwrap(), 128);
        assert_eq!(
            Reader::le(&[0xe5, 0x8e, 0x26]).uleb128("v").unwrap(),
            624485
        );
        assert_eq!(Reader::le(&[0x7f]).sleb128("v").unwrap(), -1);
        assert_eq!(Reader::le(&[0x80, 0x7f]).sleb128("v").unwrap(), -128);
        assert_eq!(Reader::le(&[0x3f]).sleb128("v").unwrap(), 63);
    }

    #[test]
    fn leb128_refuses_to_run_forever() {
        let forever = [0x80u8; 32];
        assert!(Reader::le(&forever).uleb128("v").is_err());
    }
}
