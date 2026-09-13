//! The tagged tree the decompressed `.sla` payload holds.
//!
//! The encoding is worked out in `docs/sla-format.md`. In short: a byte stream
//! of element-start, element-end and attribute tags, where the top three bits
//! of a tag byte pick the kind and say whether the id is in the low five bits
//! or in following seven-bit chunks. Every attribute is followed by exactly one
//! self-describing value, so a reader can walk a file whose ids it does not
//! know without losing sync, which is what makes the unknown regions below
//! countable rather than fatal.

/// Tag kinds, from the top three bits of a tag byte.
const ELEMENT_START: u8 = 0b010;
const ELEMENT_START_EXT: u8 = 0b011;
const ELEMENT_END: u8 = 0b100;
const ELEMENT_END_EXT: u8 = 0b101;
const ATTRIBUTE: u8 = 0b110;
const ATTRIBUTE_EXT: u8 = 0b111;

/// Value type codes, from the top four bits of a value byte.
const V_BOOL: u8 = 1;
const V_SIGNED_POS: u8 = 2;
const V_SIGNED_NEG: u8 = 3;
const V_UNSIGNED: u8 = 4;
const V_SPACE: u8 = 5;
const V_STRING: u8 = 7;

/// A nesting cap. Ghidra's own files reach depth 14; anything past this is a
/// crafted file, and the cap is what keeps the recursive drop of a `Node` off
/// the stack limit.
pub const MAX_DEPTH: usize = 128;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum DecodeError {
    /// Input ended in the middle of a tag, an id, or a value.
    Truncated { at: usize },
    /// A tag byte in the range no tag uses.
    BadTag { at: usize, byte: u8 },
    /// An element end whose id is not the element that is open.
    Mismatched { at: usize, open: u32, closed: u32 },
    /// An element end with nothing open, or content after the root closed.
    Unbalanced { at: usize },
    /// The root element never closed.
    Unclosed { open: u32 },
    /// An attribute outside any element.
    StrayAttribute { at: usize },
    /// Nesting past `MAX_DEPTH`.
    TooDeep { at: usize },
    /// A string whose length runs past the end of the payload.
    StringOverruns { at: usize, len: u128 },
    /// A string that is not UTF-8.
    NotUtf8 { at: usize },
    /// An empty payload.
    Empty,
}

impl core::fmt::Display for DecodeError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            Self::Truncated { at } => write!(f, "payload ends mid-token at {at}"),
            Self::BadTag { at, byte } => write!(f, "byte {byte:#04x} at {at} is not a tag"),
            Self::Mismatched { at, open, closed } => {
                write!(f, "element {open} closed as {closed} at {at}")
            }
            Self::Unbalanced { at } => write!(f, "unbalanced element end at {at}"),
            Self::Unclosed { open } => write!(f, "element {open} never closed"),
            Self::StrayAttribute { at } => write!(f, "attribute outside an element at {at}"),
            Self::TooDeep { at } => write!(f, "nesting past {MAX_DEPTH} at {at}"),
            Self::StringOverruns { at, len } => write!(f, "string of {len} bytes at {at} overruns"),
            Self::NotUtf8 { at } => write!(f, "string at {at} is not utf-8"),
            Self::Empty => f.write_str("empty payload"),
        }
    }
}

impl std::error::Error for DecodeError {}

/// An attribute value. The four integer codes are kept apart rather than
/// folded together, because which one the writer chose is itself evidence
/// about the field and a reader that flattens them cannot report it.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Value {
    Bool(bool),
    /// Value type 2 or 3. Type 3 carries the magnitude of a negative number.
    Signed(i128),
    /// Value type 4.
    Unsigned(u128),
    /// Value type 5: an index into the space table.
    Space(u32),
    /// Value type 7.
    Text(String),
    /// Value types 0 and 6, which no observed file uses. Kept rather than
    /// rejected so an unknown type does not make a file unreadable.
    Other {
        kind: u8,
        value: u128,
    },
}

impl Value {
    /// The value as an unsigned integer, if it is one and it fits.
    #[must_use]
    pub fn as_u64(&self) -> Option<u64> {
        match self {
            Self::Signed(v) if *v >= 0 => u64::try_from(*v).ok(),
            Self::Unsigned(v) => u64::try_from(*v).ok(),
            Self::Space(v) => Some(u64::from(*v)),
            Self::Bool(b) => Some(u64::from(*b)),
            _ => None,
        }
    }

    /// The value as a signed integer, if it is one and it fits.
    #[must_use]
    pub fn as_i64(&self) -> Option<i64> {
        match self {
            Self::Signed(v) => i64::try_from(*v).ok(),
            Self::Unsigned(v) => i64::try_from(*v).ok(),
            Self::Space(v) => Some(i64::from(*v)),
            _ => None,
        }
    }

    #[must_use]
    pub fn as_bool(&self) -> Option<bool> {
        match self {
            Self::Bool(b) => Some(*b),
            _ => None,
        }
    }

    #[must_use]
    pub fn as_str(&self) -> Option<&str> {
        match self {
            Self::Text(s) => Some(s),
            _ => None,
        }
    }

    #[must_use]
    pub fn as_space(&self) -> Option<u32> {
        match self {
            Self::Space(v) => Some(*v),
            _ => None,
        }
    }
}

/// One element of the tree, with the byte range it occupies in the
/// decompressed payload so coverage can be measured against the file.
#[derive(Debug, Clone)]
pub struct Node {
    pub id: u32,
    pub attrs: Vec<(u32, Value)>,
    pub children: Vec<Node>,
    /// Offset of the element-start tag in the decompressed payload.
    pub start: usize,
    /// Offset one past the element-end tag.
    pub end: usize,
}

impl Node {
    #[must_use]
    pub fn len(&self) -> usize {
        self.end - self.start
    }

    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.end == self.start
    }

    /// Bytes this element occupies that its children do not: its own tags,
    /// its ids and its attribute values. Summing this over every node in the
    /// tree gives the payload length exactly, which is what makes a coverage
    /// figure computed from it honest.
    #[must_use]
    pub fn own_len(&self) -> usize {
        self.len() - self.children.iter().map(Node::len).sum::<usize>()
    }

    #[must_use]
    pub fn attr(&self, id: u32) -> Option<&Value> {
        self.attrs.iter().find(|(a, _)| *a == id).map(|(_, v)| v)
    }

    #[must_use]
    pub fn child(&self, id: u32) -> Option<&Node> {
        self.children.iter().find(|c| c.id == id)
    }

    /// Depth-first visit, this element first.
    pub fn visit(&self, f: &mut impl FnMut(&Node)) {
        f(self);
        for c in &self.children {
            c.visit(f);
        }
    }
}

struct Cursor<'a> {
    data: &'a [u8],
    pos: usize,
}

impl Cursor<'_> {
    fn byte(&mut self) -> Result<u8, DecodeError> {
        let b = *self
            .data
            .get(self.pos)
            .ok_or(DecodeError::Truncated { at: self.pos })?;
        self.pos += 1;
        Ok(b)
    }

    /// `n` seven-bit chunks, most significant first. `n` is at most 16, which
    /// is 112 bits, so the accumulator is 128 bits wide and cannot wrap.
    fn chunks(&mut self, n: usize) -> Result<u128, DecodeError> {
        if self.pos + n > self.data.len() {
            return Err(DecodeError::Truncated { at: self.pos });
        }
        let mut v: u128 = 0;
        for _ in 0..n {
            let b = self.data[self.pos];
            self.pos += 1;
            v = (v << 7) | u128::from(b & 0x7f);
        }
        Ok(v)
    }

    fn value(&mut self) -> Result<Value, DecodeError> {
        let at = self.pos;
        let head = self.byte()?;
        let kind = head >> 4;
        let count = (head & 0x0f) as usize;
        if kind == V_BOOL {
            return Ok(Value::Bool(count != 0));
        }
        let raw = self.chunks(count)?;
        Ok(match kind {
            V_SIGNED_POS => Value::Signed(i128::try_from(raw).unwrap_or(i128::MAX)),
            V_SIGNED_NEG => Value::Signed(i128::try_from(raw).map_or(i128::MIN, |v| -v)),
            V_UNSIGNED => Value::Unsigned(raw),
            V_SPACE => Value::Space(u32::try_from(raw).unwrap_or(u32::MAX)),
            V_STRING => {
                // Bounded against the payload before the allocation, so a
                // crafted length cannot reserve gigabytes.
                let len = usize::try_from(raw)
                    .map_err(|_| DecodeError::StringOverruns { at, len: raw })?;
                if self.pos + len > self.data.len() {
                    return Err(DecodeError::StringOverruns { at, len: raw });
                }
                let bytes = &self.data[self.pos..self.pos + len];
                self.pos += len;
                Value::Text(
                    core::str::from_utf8(bytes)
                        .map_err(|_| DecodeError::NotUtf8 { at })?
                        .to_owned(),
                )
            }
            _ => Value::Other { kind, value: raw },
        })
    }
}

/// Decode the tagged tree. The payload is exactly one root element; trailing
/// bytes are an error rather than something to ignore.
pub fn decode(data: &[u8]) -> Result<Node, DecodeError> {
    if data.is_empty() {
        return Err(DecodeError::Empty);
    }
    let mut cur = Cursor { data, pos: 0 };
    let mut stack: Vec<Node> = Vec::new();
    let mut root: Option<Node> = None;

    while cur.pos < data.len() {
        if root.is_some() {
            return Err(DecodeError::Unbalanced { at: cur.pos });
        }
        let at = cur.pos;
        let head = cur.byte()?;
        let kind = head >> 5;
        // The extended forms spend the low four bits on a chunk count. A count
        // of zero would encode nothing, so the stored count is one less than
        // the real one and the walk always advances.
        let id = match kind {
            ELEMENT_START | ELEMENT_END | ATTRIBUTE => u128::from(head & 0x1f),
            ELEMENT_START_EXT | ELEMENT_END_EXT | ATTRIBUTE_EXT => {
                cur.chunks((head & 0x0f) as usize + 1)?
            }
            _ => return Err(DecodeError::BadTag { at, byte: head }),
        };
        let id = u32::try_from(id).unwrap_or(u32::MAX);

        match kind {
            ELEMENT_START | ELEMENT_START_EXT => {
                if stack.len() >= MAX_DEPTH {
                    return Err(DecodeError::TooDeep { at });
                }
                stack.push(Node {
                    id,
                    attrs: Vec::new(),
                    children: Vec::new(),
                    start: at,
                    end: at,
                });
            }
            ELEMENT_END | ELEMENT_END_EXT => {
                let mut done = stack.pop().ok_or(DecodeError::Unbalanced { at })?;
                if done.id != id {
                    return Err(DecodeError::Mismatched {
                        at,
                        open: done.id,
                        closed: id,
                    });
                }
                done.end = cur.pos;
                match stack.last_mut() {
                    Some(parent) => parent.children.push(done),
                    None => root = Some(done),
                }
            }
            _ => {
                let v = cur.value()?;
                stack
                    .last_mut()
                    .ok_or(DecodeError::StrayAttribute { at })?
                    .attrs
                    .push((id, v));
            }
        }
    }

    match root {
        Some(r) => Ok(r),
        None => Err(DecodeError::Unclosed {
            open: stack.last().map_or(0, |n| n.id),
        }),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn short_tags_round_trip() {
        // element 4 { attribute 3 = true } end 4
        let tree = decode(&[0x44, 0xc3, 0x11, 0x84]).unwrap();
        assert_eq!(tree.id, 4);
        assert_eq!(tree.attrs, vec![(3, Value::Bool(true))]);
        assert_eq!(tree.own_len(), 4);
    }

    #[test]
    fn extended_ids_use_seven_bit_chunks() {
        // 0x60 is an extended element start with one chunk: id 0x21.
        let tree = decode(&[0x60, 0xa1, 0xa0, 0xa1]).unwrap();
        assert_eq!(tree.id, 0x21);
    }

    #[test]
    fn strings_carry_a_chunked_length() {
        let mut b = vec![0x44, 0xcc, 0x71, 0x83];
        b.extend_from_slice(b"ram");
        b.push(0x84);
        let tree = decode(&b).unwrap();
        assert_eq!(tree.attr(12).and_then(Value::as_str), Some("ram"));
    }

    #[test]
    fn mismatched_close_is_an_error() {
        assert!(matches!(
            decode(&[0x44, 0x85]),
            Err(DecodeError::Mismatched { .. })
        ));
    }

    #[test]
    fn trailing_bytes_after_the_root_are_an_error() {
        assert!(matches!(
            decode(&[0x44, 0x84, 0x44, 0x84]),
            Err(DecodeError::Unbalanced { .. })
        ));
    }

    #[test]
    fn a_string_longer_than_the_payload_is_rejected_before_allocating() {
        let b = vec![0x44, 0xcc, 0x72, 0xff, 0xff];
        assert!(matches!(
            decode(&b),
            Err(DecodeError::StringOverruns { .. })
        ));
    }

    #[test]
    fn depth_is_capped() {
        let mut b = vec![0x44; MAX_DEPTH + 4];
        b.extend(std::iter::repeat_n(0x84u8, MAX_DEPTH + 4));
        assert!(matches!(decode(&b), Err(DecodeError::TooDeep { .. })));
    }
}
