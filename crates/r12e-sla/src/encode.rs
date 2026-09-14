//! Writing the tagged element tree back out as `.sla` payload bytes.
//!
//! This is the exact inverse of [`crate::decode`], and it is held to that
//! standard: the corpus test re-encodes every `.sla` Ghidra ships and requires
//! the bytes back. That is what makes the encoding claims in
//! `docs/sla-format.md` testable in the writing direction and not only the
//! reading one, and it is the foundation everything above it stands on, since
//! a writer that emits the right tree but the wrong bytes would look correct
//! to our own reader and to nothing else.
//!
//! Two choices the format leaves open have to be made the same way the
//! reference compiler makes them, or the bytes differ even when the tree does
//! not:
//!
//! * an id below 32 uses the short tag form, and anything else the extended
//!   form with the fewest seven-bit chunks that hold it;
//! * an integer value uses the fewest chunks that hold its magnitude, so zero
//!   is a count of zero and no payload at all.
//!
//! Both were read off the shipped files and both are checked by the re-encode.

use crate::decode::{Node, Value};

/// Tag kinds in the short form, where the id is the low five bits.
const T_ELEMENT_START: u8 = 0b010 << 5;
const T_ELEMENT_END: u8 = 0b100 << 5;
const T_ATTRIBUTE: u8 = 0b110 << 5;
/// The extended form of each, where the low four bits are one less than the
/// number of seven-bit id chunks that follow.
const T_ELEMENT_START_EXT: u8 = 0b011 << 5;
const T_ELEMENT_END_EXT: u8 = 0b101 << 5;
const T_ATTRIBUTE_EXT: u8 = 0b111 << 5;

/// The largest id the extended form can carry: sixteen chunks of seven bits.
/// Ghidra's own ids stop at 84, so anything near this is a caller's bug.
pub const MAX_ID: u32 = u32::MAX;

/// Something that cannot be written. These are all caller errors rather than
/// data errors, but they are returned rather than asserted because the
/// compiler builds trees from a specification, which is input.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum EncodeError {
    /// A string attribute longer than the payload limit allows.
    StringTooLong { len: usize },
    /// A value the tag encoding has no room for.
    ValueTooWide,
    /// Nesting past [`crate::decode::MAX_DEPTH`], which the reader refuses, so
    /// writing it would produce a file we could not read back.
    TooDeep,
}

impl core::fmt::Display for EncodeError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            Self::StringTooLong { len } => write!(f, "string of {len} bytes is too long"),
            Self::ValueTooWide => f.write_str("value does not fit the chunk encoding"),
            Self::TooDeep => write!(f, "nesting past {}", crate::decode::MAX_DEPTH),
        }
    }
}

impl std::error::Error for EncodeError {}

/// How many seven-bit chunks a magnitude needs. Zero needs none: the shipped
/// files encode a zero as a bare type byte with a count of zero.
fn chunk_count(v: u128) -> usize {
    let mut n = 0;
    let mut rest = v;
    while rest != 0 {
        n += 1;
        rest >>= 7;
    }
    n
}

/// Write `v` as `n` seven-bit chunks, most significant first, each with the
/// top bit set. The top bit is not part of the value; it is what keeps a chunk
/// out of the tag ranges.
fn push_chunks(out: &mut Vec<u8>, v: u128, n: usize) {
    for i in (0..n).rev() {
        out.push(0x80 | ((v >> (i * 7)) as u8 & 0x7f));
    }
}

/// Write a tag: the short form when the id fits in five bits, the extended
/// form otherwise.
fn push_tag(out: &mut Vec<u8>, short: u8, ext: u8, id: u32) {
    if id < 32 {
        out.push(short | id as u8);
        return;
    }
    let n = chunk_count(u128::from(id)).max(1);
    // The count nibble holds one less than the real count, so a count of
    // sixteen is the ceiling and 112 bits is far past any id.
    out.push(ext | ((n - 1) as u8 & 0x0f));
    push_chunks(out, u128::from(id), n);
}

/// Value type codes. The reader's names, from `docs/sla-format.md`.
const V_BOOL: u8 = 1;
const V_SIGNED_POS: u8 = 2;
const V_SIGNED_NEG: u8 = 3;
const V_UNSIGNED: u8 = 4;
const V_SPACE: u8 = 5;
const V_STRING: u8 = 7;

fn push_typed(out: &mut Vec<u8>, kind: u8, magnitude: u128) -> Result<(), EncodeError> {
    let n = chunk_count(magnitude);
    if n > 15 {
        return Err(EncodeError::ValueTooWide);
    }
    out.push((kind << 4) | n as u8);
    push_chunks(out, magnitude, n);
    Ok(())
}

/// Write one attribute value.
///
/// # Errors
/// A string too long for the length encoding, or an integer wider than fifteen
/// chunks.
pub fn push_value(out: &mut Vec<u8>, v: &Value) -> Result<(), EncodeError> {
    match v {
        Value::Bool(b) => {
            out.push((V_BOOL << 4) | u8::from(*b));
            Ok(())
        }
        // Type 3 carries the magnitude of a negative number, so the sign is in
        // the type code and never in the chunks.
        Value::Signed(i) if *i < 0 => push_typed(out, V_SIGNED_NEG, i.unsigned_abs()),
        Value::Signed(i) => push_typed(out, V_SIGNED_POS, *i as u128),
        Value::Unsigned(u) => push_typed(out, V_UNSIGNED, *u),
        Value::Space(s) => push_typed(out, V_SPACE, u128::from(*s)),
        Value::Text(s) => {
            let len = s.len();
            let n = chunk_count(len as u128);
            if n > 15 {
                return Err(EncodeError::StringTooLong { len });
            }
            out.push((V_STRING << 4) | n as u8);
            push_chunks(out, len as u128, n);
            out.extend_from_slice(s.as_bytes());
            Ok(())
        }
        Value::Other { kind, value } => push_typed(out, *kind, *value),
    }
}

/// Encode one element and everything under it.
///
/// The walk is iterative rather than recursive: a real language nests about
/// fourteen deep, but the depth comes from data in the compiler's case and a
/// blown stack is not an error a caller can handle.
///
/// # Errors
/// See [`push_value`], plus nesting past the reader's depth cap.
pub fn encode(root: &Node) -> Result<Vec<u8>, EncodeError> {
    let mut out = Vec::new();
    encode_into(&mut out, root)?;
    Ok(out)
}

/// As [`encode`], appending to a buffer the caller owns.
///
/// # Errors
/// See [`encode`].
pub fn encode_into(out: &mut Vec<u8>, root: &Node) -> Result<(), EncodeError> {
    enum Step<'a> {
        Open(&'a Node),
        Close(u32),
    }
    let mut stack = vec![Step::Open(root)];
    let mut depth = 0usize;
    while let Some(step) = stack.pop() {
        match step {
            Step::Open(n) => {
                depth += 1;
                if depth > crate::decode::MAX_DEPTH {
                    return Err(EncodeError::TooDeep);
                }
                push_tag(out, T_ELEMENT_START, T_ELEMENT_START_EXT, n.id);
                for (id, v) in &n.attrs {
                    push_tag(out, T_ATTRIBUTE, T_ATTRIBUTE_EXT, *id);
                    push_value(out, v)?;
                }
                stack.push(Step::Close(n.id));
                for c in n.children.iter().rev() {
                    stack.push(Step::Open(c));
                }
            }
            Step::Close(id) => {
                depth -= 1;
                push_tag(out, T_ELEMENT_END, T_ELEMENT_END_EXT, id);
            }
        }
    }
    Ok(())
}

/// A tree under construction.
///
/// The compiler builds thousands of small elements and the shape of the file
/// is easier to check when the code that writes it reads like the tree in
/// `docs/sla-format.md`. Byte ranges are left at zero: they describe where a
/// node was read from, and a node that was built rather than read has no such
/// place. [`crate::Sla::parse`] fills them in when the result is read back.
#[derive(Debug, Clone)]
pub struct Build {
    node: Node,
}

impl Build {
    /// A new element with no attributes and no children.
    #[must_use]
    pub fn new(id: u32) -> Self {
        Self {
            node: Node {
                id,
                attrs: Vec::new(),
                children: Vec::new(),
                start: 0,
                end: 0,
            },
        }
    }

    /// Add an attribute. Order is preserved, and it matters: the reference
    /// compiler writes each element's attributes in a fixed order and a
    /// byte comparison sees any difference.
    #[must_use]
    pub fn attr(mut self, id: u32, v: Value) -> Self {
        self.node.attrs.push((id, v));
        self
    }

    /// Add a non-negative integer attribute, the common case.
    #[must_use]
    pub fn int(self, id: u32, v: i64) -> Self {
        self.attr(id, Value::Signed(i128::from(v)))
    }

    /// Add an unsigned attribute, used where a field needs all 32 or 64 bits.
    #[must_use]
    pub fn uint(self, id: u32, v: u64) -> Self {
        self.attr(id, Value::Unsigned(u128::from(v)))
    }

    #[must_use]
    pub fn bool(self, id: u32, v: bool) -> Self {
        self.attr(id, Value::Bool(v))
    }

    #[must_use]
    pub fn text(self, id: u32, v: impl Into<String>) -> Self {
        self.attr(id, Value::Text(v.into()))
    }

    /// Add a space reference, value type 5.
    #[must_use]
    pub fn space(self, id: u32, ix: u32) -> Self {
        self.attr(id, Value::Space(ix))
    }

    #[must_use]
    pub fn child(mut self, c: Build) -> Self {
        self.node.children.push(c.node);
        self
    }

    /// Add a child in place, for loops.
    pub fn push(&mut self, c: Build) {
        self.node.children.push(c.node);
    }

    #[must_use]
    pub fn finish(self) -> Node {
        self.node
    }
}

impl From<Build> for Node {
    fn from(b: Build) -> Node {
        b.node
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::decode::decode;

    fn round(bytes: &[u8]) {
        let tree = decode(bytes).expect("decodes");
        assert_eq!(encode(&tree).expect("encodes"), bytes);
    }

    #[test]
    fn short_tags_come_back_the_same() {
        round(&[0x44, 0xc3, 0x11, 0x84]);
    }

    #[test]
    fn extended_ids_come_back_the_same() {
        round(&[0x60, 0xa1, 0xa0, 0xa1]);
    }

    #[test]
    fn strings_come_back_the_same() {
        let mut b = vec![0x44, 0xcc, 0x71, 0x83];
        b.extend_from_slice(b"ram");
        b.push(0x84);
        round(&b);
    }

    #[test]
    fn a_zero_costs_no_chunks() {
        let mut out = Vec::new();
        push_value(&mut out, &Value::Unsigned(0)).unwrap();
        assert_eq!(out, vec![0x40]);
    }

    #[test]
    fn a_negative_uses_the_magnitude_type() {
        let mut out = Vec::new();
        push_value(&mut out, &Value::Signed(-1)).unwrap();
        assert_eq!(out, vec![0x31, 0x81]);
    }

    #[test]
    fn a_wide_unsigned_survives_the_trip() {
        let b = Build::new(33).uint(8, 0x8000_0000).finish();
        let bytes = encode(&b).unwrap();
        let back = decode(&bytes).unwrap();
        assert_eq!(back.attr(8), Some(&Value::Unsigned(0x8000_0000)));
    }

    #[test]
    fn a_built_tree_encodes_and_reads_back() {
        let t = Build::new(33)
            .int(34, 4)
            .bool(35, false)
            .child(Build::new(35).child(Build::new(36).text(12, "data.sinc").int(9, 0)))
            .finish();
        let bytes = encode(&t).unwrap();
        let back = decode(&bytes).unwrap();
        assert_eq!(back.id, 33);
        assert_eq!(
            back.child(35)
                .and_then(|s| s.child(36))
                .and_then(|f| f.attr(12)),
            Some(&crate::Value::Text("data.sinc".into()))
        );
    }

    #[test]
    fn nesting_past_the_readers_cap_is_refused() {
        let mut n = Build::new(1);
        for _ in 0..crate::decode::MAX_DEPTH + 2 {
            n = Build::new(1).child(n);
        }
        assert_eq!(encode(&n.finish()), Err(EncodeError::TooDeep));
    }
}
