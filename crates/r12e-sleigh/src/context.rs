//! The context register, and the database of changes a `globalset` publishes.
//!
//! A SLEIGH context register is a bit vector the decoder carries alongside the
//! instruction bytes. Two things write to it and they are not the same thing:
//!
//! * a disassembly action writes a field with `ctx = value;`, which changes how
//!   the *rest of this instruction* parses and then evaporates;
//! * `globalset(addr, ctx)` publishes the field's current value at another
//!   address, where it changes how *that* instruction parses.
//!
//! The second is why a single register image is not enough. ARM's `TMode`
//! selects Thumb for every instruction from a `bx` onwards, and AArch64's
//! specification uses the same mechanism, so the decoder needs a map from
//! address to the fields that were published there. That map is
//! [`ContextDb`].
//!
//! Nothing here allocates per instruction: a decode that publishes nothing
//! touches the database not at all, and the common case of a linear sweep over
//! a section that never calls `globalset` costs one hash lookup per
//! instruction.

use std::collections::HashMap;

use crate::model::{ContextField, ContextFieldId, Spec};

/// The largest context register this will build an image for, in bytes.
///
/// Ghidra's widest published context register is eight bytes. The ceiling is
/// here because the size is read from a specification, which is input, and it
/// is a fixed size so a [`Context`] is `Copy` and saving one before a
/// speculative match costs no allocation. A decode tries thousands of
/// constructors and each one may change the context, so this is the
/// difference between an allocation per constructor and none.
pub const MAX_CONTEXT_BYTES: usize = 32;

/// A context register image: the raw bytes the pattern masks are compared
/// against.
///
/// Bit numbering is the specification's own, most significant bit of byte zero
/// first, which is what [`ContextField::bit_position`] implements.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Context {
    bytes: [u8; MAX_CONTEXT_BYTES],
    len: u8,
}

impl Default for Context {
    fn default() -> Context {
        Context {
            bytes: [0; MAX_CONTEXT_BYTES],
            len: 0,
        }
    }
}

impl Context {
    /// An all-zero image wide enough for `spec`'s context register.
    pub fn for_spec(spec: &Spec) -> Context {
        Context::zeroed(spec.context_bytes())
    }

    /// An image of a given width, clamped to [`MAX_CONTEXT_BYTES`].
    pub fn zeroed(bytes: usize) -> Context {
        Context {
            bytes: [0; MAX_CONTEXT_BYTES],
            len: bytes.min(MAX_CONTEXT_BYTES) as u8,
        }
    }

    /// The raw bytes, for [`crate::model::MaskValue::matches`].
    pub fn bytes(&self) -> &[u8] {
        &self.bytes[..self.len as usize]
    }

    /// How wide the image is.
    pub fn len(&self) -> usize {
        self.len as usize
    }

    /// Whether there is no context register at all.
    pub fn is_empty(&self) -> bool {
        self.len == 0
    }

    /// The first eight bytes packed into one integer, byte zero most
    /// significant, so a whole context test is one compare. Bytes past the
    /// image read as zero, which is what a mask that reaches past it should
    /// compare against.
    pub fn word(&self) -> u64 {
        let mut out = 0u64;
        for i in 0..8 {
            out |= (self.bytes.get(i).copied().unwrap_or(0) as u64) << (56 - i * 8);
        }
        out
    }

    /// Read one field. `None` when the field runs past the image, which means
    /// the specification declared a context register narrower than its own
    /// fields.
    pub fn get(&self, field: &ContextField) -> Option<u64> {
        field.extract(self.bytes())
    }

    /// Write one field, keeping the bits around it. Returns false when the
    /// field does not fit in the image.
    pub fn set(&mut self, field: &ContextField, value: u64) -> bool {
        if field.high < field.low {
            return false;
        }
        // The range runs from `low`, the most significant bit, down to `high`,
        // so the output bit for `low` is the field's top bit.
        for (out, bit) in (field.low..=field.high).rev().enumerate() {
            let (byte, offset) = ContextField::bit_position(bit);
            if byte >= self.len as usize {
                return false;
            }
            let slot = &mut self.bytes[byte];
            let one = value >> out & 1 == 1;
            if one {
                *slot |= 1 << offset;
            } else {
                *slot &= !(1u8 << offset);
            }
        }
        true
    }
}

/// One field's value, published at an address.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Commit {
    /// Which field.
    pub field: ContextFieldId,
    /// Its value there.
    pub value: u64,
    /// Whether the specification marked the field `noflow`, so the value
    /// applies at exactly this address and does not follow the flow onwards.
    /// The database is keyed by address either way; the flag is kept because a
    /// caller that propagates context along a control flow graph needs it and
    /// nothing else records it.
    pub noflow: bool,
}

/// Context values published by `globalset`, keyed by the address they apply
/// at.
///
/// Bounded: a sweep over a hostile binary could otherwise publish one entry per
/// byte. When the ceiling is reached new addresses are refused and
/// [`ContextDb::overflowed`] says so, rather than the map growing without
/// limit or entries being silently dropped.
#[derive(Debug, Clone)]
pub struct ContextDb {
    at: HashMap<u64, Vec<Commit>>,
    limit: usize,
    overflowed: bool,
}

impl Default for ContextDb {
    fn default() -> ContextDb {
        ContextDb::with_limit(1 << 20)
    }
}

impl ContextDb {
    /// An empty database holding at most `limit` addresses.
    pub fn with_limit(limit: usize) -> ContextDb {
        ContextDb {
            at: HashMap::new(),
            limit,
            overflowed: false,
        }
    }

    /// Whether the ceiling was reached and something was refused.
    pub fn overflowed(&self) -> bool {
        self.overflowed
    }

    /// How many addresses carry a published value.
    pub fn len(&self) -> usize {
        self.at.len()
    }

    /// Whether nothing has been published.
    pub fn is_empty(&self) -> bool {
        self.at.is_empty()
    }

    /// Publish `commit` at `addr`. A second commit of the same field at the
    /// same address replaces the first, which is what re-decoding the same
    /// instruction must do if decoding is to be idempotent.
    pub fn commit(&mut self, addr: u64, commit: Commit) {
        if let Some(slot) = self.at.get_mut(&addr) {
            if let Some(existing) = slot.iter_mut().find(|c| c.field == commit.field) {
                *existing = commit;
            // Bounded per address as well: a constructor tree can only hold so
            // many distinct fields, and this stops a pathological
            // specification growing one list for ever.
            } else if slot.len() < 64 {
                slot.push(commit);
            } else {
                self.overflowed = true;
            }
            return;
        }
        if self.at.len() >= self.limit {
            self.overflowed = true;
            return;
        }
        self.at.insert(addr, vec![commit]);
    }

    /// What was published at `addr`.
    pub fn at(&self, addr: u64) -> &[Commit] {
        self.at.get(&addr).map_or(&[], |v| v.as_slice())
    }

    /// Fold everything published at `addr` into `image`.
    pub fn apply(&self, spec: &Spec, addr: u64, image: &mut Context) {
        for c in self.at(addr) {
            if let Some(f) = spec.context_fields.get(c.field.index()) {
                image.set(f, c.value);
            }
        }
    }

    /// Forget everything.
    pub fn clear(&mut self) {
        self.at.clear();
        self.overflowed = false;
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::model::{Attach, NumberBase, VarnodeId};

    fn field(low: u32, high: u32) -> ContextField {
        ContextField {
            name: "f".into(),
            register: VarnodeId(0),
            low,
            high,
            signed: false,
            base: NumberBase::Hex,
            noflow: false,
            attach: Attach::None,
        }
    }

    #[test]
    fn a_field_round_trips_through_the_image() {
        let mut c = Context::zeroed(4);
        let f = field(4, 7);
        assert!(c.set(&f, 0xd));
        assert_eq!(c.get(&f), Some(0xd));
        assert_eq!(c.bytes(), &[0x0d, 0, 0, 0]);
    }

    #[test]
    fn writing_a_field_leaves_its_neighbours_alone() {
        let mut c = Context::zeroed(4);
        let low = field(0, 3);
        let high = field(4, 7);
        assert!(c.set(&low, 0xf));
        assert!(c.set(&high, 0x5));
        assert_eq!(c.get(&low), Some(0xf));
        assert_eq!(c.get(&high), Some(0x5));
        // And clearing one really clears it, rather than only ever setting
        // bits.
        assert!(c.set(&low, 0));
        assert_eq!(c.get(&low), Some(0));
        assert_eq!(c.get(&high), Some(0x5));
    }

    #[test]
    fn a_field_past_the_end_of_the_image_fails_rather_than_panicking() {
        let mut c = Context::zeroed(1);
        let f = field(60, 63);
        assert!(!c.set(&f, 1));
        assert_eq!(c.get(&f), None);
    }

    #[test]
    fn the_database_replaces_a_field_at_the_same_address() {
        let mut db = ContextDb::default();
        db.commit(
            0x1000,
            Commit {
                field: ContextFieldId(0),
                value: 1,
                noflow: false,
            },
        );
        db.commit(
            0x1000,
            Commit {
                field: ContextFieldId(0),
                value: 0,
                noflow: false,
            },
        );
        assert_eq!(db.at(0x1000).len(), 1);
        assert_eq!(db.at(0x1000)[0].value, 0);
    }

    #[test]
    fn the_database_refuses_to_grow_past_its_ceiling() {
        let mut db = ContextDb::with_limit(2);
        for addr in 0..8 {
            db.commit(
                addr,
                Commit {
                    field: ContextFieldId(0),
                    value: 1,
                    noflow: false,
                },
            );
        }
        assert_eq!(db.len(), 2);
        assert!(db.overflowed());
    }
}
