//! The order constructors are tried in, and the prefilter that skips most of
//! them.
//!
//! # Why the specification's own order is not the order to try
//!
//! [`crate::model::Table::constructors`] is declaration order, and a decoder
//! that walks it takes the first constructor whose pattern admits the bytes.
//! That is wrong, and the SLEIGH manual says so in the section on tables:
//!
//! > Notice that the first constructor has only the one constraint on
//! > `addrmode`, which is also a constraint for the second constructor. So any
//! > instruction that matches the second must also match the first.
//!
//! The example it is describing puts the general case first and the special
//! case second, and the special case is the one that must win. It then states
//! the invariant that makes the rule decidable:
//!
//! > Any two sets defined by the bit patterns must be either disjoint or one
//! > contained in the other. [...] If the patterns for two constructors
//! > intersect, but one pattern does not properly contain the other, this is
//! > generally an error in the specification.
//!
//! So for any two constructors of a table that can both admit the same bytes,
//! one pattern contains the other, and the contained one, which is the one
//! with more bits constrained, is the answer. Sorting a table by how many bits
//! its constructors pin down, most first, puts the right one first; declaration
//! order breaks ties, which under the invariant are patterns that cannot both
//! match anyway.
//!
//! This is not a detail. AArch64 writes
//!
//! ```text
//! Rd_GPR64xsp: aa_Xd is aa_Xd          { export aa_Xd; }
//! Rd_GPR64xsp: sp    is aa_Xd=31 & sp  { export sp; }
//! ```
//!
//! and in declaration order every `add sp, sp, #imm` in every AArch64 binary
//! ever compiled disassembles as `add xzr, xzr, #imm`, which is not the same
//! instruction.
//!
//! # The prefilter
//!
//! The other half of this module is a cheap rejection test. The index keeps,
//! per constructor, the mask and value its first four instruction bytes must
//! take across every alternative, so one `u32` load and one compare reject
//! most candidates without touching
//! [`crate::model::ResolvedPattern::may_match`], which walks vectors.
//!
//! Four bytes rather than two because two is the wrong number for a little
//! endian thirty-two bit instruction set: AArch64 puts its opcode in bits 24
//! to 31, which is byte three, and its register fields in bytes zero and one,
//! so a two byte filter tests the bits that vary and skips the bits that
//! discriminate. Widening it to four takes random-byte AArch64 decoding from
//! 26k attempts a second to about ten times that.
//!
//! It is only ever a filter. A constructor whose first four bytes are
//! unconstrained has a zero mask and is never rejected by it, and a byte the
//! filter does not require is never read, so a two byte instruction is not
//! rejected for being two bytes long.
//!
//! # The decision byte
//!
//! Filtering is still linear in the size of the table, and the two tables that
//! matter are large: AArch64's `instruction` has 3,604 constructors and
//! x86-64's has 4,645. Measured, a linear scan over AArch64 runs at about
//! 40,000 decode attempts a second, which is three and a half nanoseconds per
//! constructor and about as fast as a linear scan of two vectors gets. The
//! only way past it is to stop looking at most of them.
//!
//! So each table picks one *decision byte*: the instruction byte offset, of
//! the first four, that the most constructors pin down completely. Its 256
//! possible values each get the sub-list of constructors that can still match,
//! in the same specificity order, and a decode indexes straight into that.
//! AArch64's opcode bits are in byte three, x86's in byte zero, and the
//! specification says so rather than the decoder assuming it.
//!
//! Bucketing is refused rather than forced when it would not pay: a table
//! whose constructors mostly leave every byte free would copy itself 256 times
//! for no gain, so the buckets are only built when their total size stays
//! under [`BUCKET_GROWTH`] times the table's own. That is a bound on memory,
//! which matters because the number of tables comes from a file.

use crate::model::{ConstructorId, MaskValue, Spec, TableId};

/// Per-table constructor order, and the first-bytes prefilter.
#[derive(Debug, Clone)]
pub struct Index {
    /// For each table, its constructors most specific first.
    order: Vec<Vec<ConstructorId>>,
    /// For each constructor, the mask and value its first four instruction
    /// bytes must satisfy, agreed across every alternative. Zero mask means no
    /// filter.
    first: Vec<(u32, u32)>,
    /// The same for the context register's first eight bytes, packed by
    /// [`crate::context::Context::word`].
    ///
    /// Without this the context test only happens inside
    /// [`crate::model::ResolvedPattern::may_match`], which is reached after
    /// the instruction filter has already let the constructor through, and
    /// every constructor of a `with : ctx=1 { ... }` block is tried in full
    /// during the pass where that context bit is still zero. AArch64 wraps its
    /// whole instruction set in one such block, so that is the difference
    /// between scanning 3,604 constructors twice and scanning them once.
    context: Vec<(u64, u64)>,
    /// Per table, the decision byte and its 256 buckets, when bucketing this
    /// table was worth it.
    buckets: Vec<Option<Buckets>>,
}

/// How much larger than the table itself its buckets are allowed to be.
///
/// Four is enough for every table in the published corpus that benefits and
/// refuses the ones that do not. It is a memory bound, and the number of
/// tables is read from a file.
pub const BUCKET_GROWTH: usize = 4;

/// One table's constructors, split by the value of a single instruction byte.
#[derive(Debug, Clone)]
struct Buckets {
    /// Which instruction byte, counted from the table's own first byte.
    at: usize,
    /// `256 + 1` offsets into `flat`, so bucket `v` is
    /// `flat[ends[v]..ends[v + 1]]`.
    ends: Vec<u32>,
    /// The buckets, end to end.
    flat: Vec<ConstructorId>,
    /// The constructors that do not constrain the decision byte at all, which
    /// is what a stream too short to reach it falls back to. Kept separately
    /// rather than as a 257th bucket because it is the whole answer in that
    /// case, not part of one.
    free: Vec<ConstructorId>,
}

impl Index {
    /// Build the index for a specification. Linear in the number of
    /// constructors, and done once per specification rather than once per
    /// instruction.
    pub fn build(spec: &Spec) -> Index {
        let mut first = Vec::with_capacity(spec.constructors.len());
        let mut context = Vec::with_capacity(spec.constructors.len());
        for c in &spec.constructors {
            first.push(first_bytes(&c.resolved.alternatives));
            context.push(context_word(&c.resolved.alternatives));
        }

        let mut order = Vec::with_capacity(spec.tables.len());
        for table in &spec.tables {
            let mut ids = table.constructors.clone();
            // Stable, so declaration order survives a tie. Sorting by
            // specificity is what the manual's containment rule requires; see
            // the module comment.
            ids.sort_by_key(|id| {
                std::cmp::Reverse(spec.constructors.get(id.index()).map_or(0, specificity))
            });
            order.push(ids);
        }
        let mut buckets = Vec::with_capacity(order.len());
        for ids in &order {
            buckets.push(Buckets::build(spec, ids));
        }

        Index {
            order,
            first,
            context,
            buckets,
        }
    }

    /// The constructors of `table` worth trying against `stream`, most
    /// specific first.
    ///
    /// This is [`Index::table`] when the table has no decision byte, and a
    /// much shorter list when it has. Either way the order is the same and
    /// every constructor that could match is in it.
    pub fn candidates(&self, table: TableId, stream: &[u8]) -> &[ConstructorId] {
        match self.buckets.get(table.index()).and_then(|b| b.as_ref()) {
            Some(b) => match stream.get(b.at) {
                Some(&byte) => b.bucket(byte),
                None => &b.free,
            },
            None => self.table(table),
        }
    }

    /// The constructors of a table, most specific first.
    pub fn table(&self, id: TableId) -> &[ConstructorId] {
        self.order.get(id.index()).map_or(&[], |v| v.as_slice())
    }

    /// Whether the first four bytes of `stream` can possibly satisfy the
    /// constructor. False is a certain no; true means try properly.
    pub fn may_start(&self, id: ConstructorId, stream: &[u8], context: u64) -> bool {
        if let Some(&(mask, value)) = self.context.get(id.index())
            && context & mask != value
        {
            return false;
        }
        let Some(&(mask, value)) = self.first.get(id.index()) else {
            return true;
        };
        if mask == 0 {
            return true;
        }
        let mut got = 0u32;
        // A byte that is not there cannot satisfy a constrained byte, and the
        // shifts keep it that way: the missing byte reads as zero against a
        // value that, for it to matter, some alternative required.
        for i in 0..4 {
            if mask >> (i * 8) & 0xff != 0 {
                let Some(&b) = stream.get(i) else {
                    return false;
                };
                got |= (b as u32) << (i * 8);
            }
        }
        got & mask == value
    }
}

/// How many bits a constructor pins down, counting the bits every alternative
/// agrees on plus a weight for constraints that are not a bit test.
///
/// The agreement is the right reading: a constructor written `a=1 | a=2` is as
/// general as its most general branch, and it is generality that decides which
/// of two overlapping constructors contains the other.
fn specificity(c: &crate::model::Constructor) -> u32 {
    let alts = &c.resolved.alternatives;
    let Some(head) = alts.first() else {
        // Nothing matches it, so where it sits does not matter.
        return 0;
    };
    let mut agreed_instr = head.instr.clone();
    let mut agreed_context = head.context.clone();
    for a in &alts[1..] {
        agreed_instr = agreed_instr.intersect(&a.instr);
        agreed_context = agreed_context.intersect(&a.context);
    }
    let bits = popcount(&agreed_instr) + popcount(&agreed_context);
    // A residual is a real constraint the masks could not express, so a
    // constructor carrying one is more specific than the same masks without
    // it. One bit each is enough to break the tie without letting a long
    // residual list outweigh a genuinely narrower mask.
    let residual = alts.iter().map(|a| a.residual.len()).min().unwrap_or(0);
    bits + residual as u32
}

fn popcount(mv: &MaskValue) -> u32 {
    mv.mask.iter().map(|b| b.count_ones()).sum()
}

/// The mask and value the first four bytes must take, agreed across every
/// alternative. An empty alternative list yields no filter, because a
/// constructor that matches nothing is rejected by the real test anyway and a
/// filter that rejected everything would hide that.
fn first_bytes(alts: &[crate::model::PatternAlt]) -> (u32, u32) {
    let Some(head) = alts.first() else {
        return (0, 0);
    };
    let mut mask = four(&head.instr.mask);
    let mut value = four(&head.instr.value);
    for a in &alts[1..] {
        let m = four(&a.instr.mask);
        let v = four(&a.instr.value);
        // Keep only the bits that are constrained the same way everywhere.
        let agree = mask & m & !(value ^ v);
        mask = agree;
        value &= agree;
    }
    (mask, value)
}

fn four(bytes: &[u8]) -> u32 {
    let mut out = 0u32;
    for i in 0..4 {
        out |= (bytes.get(i).copied().unwrap_or(0) as u32) << (i * 8);
    }
    out
}

/// The context mask and value every alternative agrees on, packed the way
/// [`crate::context::Context::word`] packs an image.
fn context_word(alts: &[crate::model::PatternAlt]) -> (u64, u64) {
    let Some(head) = alts.first() else {
        return (0, 0);
    };
    let mut mask = eight(&head.context.mask);
    let mut value = eight(&head.context.value);
    for a in &alts[1..] {
        let m = eight(&a.context.mask);
        let v = eight(&a.context.value);
        let agree = mask & m & !(value ^ v);
        mask = agree;
        value &= agree;
    }
    (mask, value)
}

fn eight(bytes: &[u8]) -> u64 {
    let mut out = 0u64;
    for i in 0..8 {
        out |= (bytes.get(i).copied().unwrap_or(0) as u64) << (56 - i * 8);
    }
    out
}

impl Buckets {
    /// Split `ids` by the byte that discriminates them best, or decline.
    fn build(spec: &Spec, ids: &[ConstructorId]) -> Option<Buckets> {
        // Below this a linear scan is already one cache line's worth of work
        // and the indirection costs more than it saves.
        if ids.len() < 32 {
            return None;
        }
        // Score each candidate byte by how much work it would leave: a
        // constructor whose mask over the byte has `n` bits free admits
        // `2^n` of the 256 values, so the sum over the table is the total size
        // of all the buckets, and dividing by 256 is the average bucket. The
        // byte with the smallest total is the one that discriminates best.
        //
        // Counting admitted values rather than counting fully pinned bytes is
        // what makes this work on RISC-V, where the opcode is the low seven
        // bits of byte zero. A mask of `0x7f` pins nothing by the strict
        // reading and admits two values out of 256 by this one.
        let at = (0..4).min_by_key(|&at| spread(spec, ids, at))?;
        let total = spread(spec, ids, at);
        if total >= ids.len().saturating_mul(BUCKET_GROWTH) {
            return None;
        }

        let free: Vec<ConstructorId> = ids
            .iter()
            .copied()
            .filter(|id| byte_test(spec, *id, at).0 == 0)
            .collect();
        let mut ends = Vec::with_capacity(257);
        let mut flat: Vec<ConstructorId> = Vec::with_capacity(ids.len() * 2);
        let cap = ids.len().saturating_mul(BUCKET_GROWTH);
        for value in 0..256u32 {
            ends.push(flat.len() as u32);
            for &id in ids {
                let (mask, want) = byte_test(spec, id, at);
                if value as u8 & mask == want {
                    flat.push(id);
                }
            }
            if flat.len() > cap {
                return None;
            }
        }
        ends.push(flat.len() as u32);
        Some(Buckets {
            at,
            ends,
            flat,
            free,
        })
    }

    fn bucket(&self, byte: u8) -> &[ConstructorId] {
        let i = byte as usize;
        let (Some(&lo), Some(&hi)) = (self.ends.get(i), self.ends.get(i + 1)) else {
            return &self.flat;
        };
        &self.flat[lo as usize..hi as usize]
    }
}

/// The mask and value a constructor requires of instruction byte `at`, agreed
/// across every alternative. A zero mask means it does not care.
fn byte_test(spec: &Spec, id: ConstructorId, at: usize) -> (u8, u8) {
    let Some(c) = spec.constructors.get(id.index()) else {
        return (0, 0);
    };
    let alts = &c.resolved.alternatives;
    let Some(head) = alts.first() else {
        return (0, 0);
    };
    let byte = |a: &crate::model::PatternAlt| {
        (
            a.instr.mask.get(at).copied().unwrap_or(0),
            a.instr.value.get(at).copied().unwrap_or(0),
        )
    };
    let (mut mask, mut value) = byte(head);
    for a in &alts[1..] {
        let (m, v) = byte(a);
        let agree = mask & m & !(value ^ v);
        mask = agree;
        value &= agree;
    }
    (mask, value)
}

/// The total size of the 256 buckets that splitting `ids` on byte `at` would
/// produce, which is the sum over constructors of how many of the 256 values
/// each one admits.
fn spread(spec: &Spec, ids: &[ConstructorId], at: usize) -> usize {
    ids.iter()
        .map(|id| 1usize << (8 - byte_test(spec, *id, at).0.count_ones()))
        .sum()
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The manual's own example: a general constructor first, a special case
    /// second, and the special case has to win.
    #[test]
    fn a_special_case_declared_second_is_tried_first() {
        let spec = crate::parse_str(
            r#"
define endian=little;
define space ram type=ram_space size=4 default;
define space register type=register_space size=4;
define register offset=0 size=4 [ r0 r1 r2 r3 ];
define token instr(8) addrmode=(6,7) rf=(0,1);
attach variables [ rf ] [ r0 r1 r2 r3 ];
zA: rf is addrmode=3 & rf { export rf; }
zA: "0" is addrmode=3 & rf=0 { export 0:4; }
:ld zA is addrmode=3 & zA { }
"#,
        )
        .expect("parses");
        let index = Index::build(&spec);
        let Some(crate::model::Symbol::Table(za)) = spec.lookup("zA") else {
            panic!("zA is a table");
        };
        let order = index.table(za);
        let first = spec.constructor(order[0]);
        assert_eq!(
            first.display.pieces.len(),
            1,
            "the special case, whose display is the literal 0, comes first"
        );
        assert!(matches!(
            first.display.pieces[0],
            crate::model::DisplayPiece::Literal(_)
        ));
    }

    #[test]
    fn the_prefilter_rejects_only_what_no_alternative_admits() {
        let spec = crate::parse_str(
            r#"
define endian=little;
define space ram type=ram_space size=4 default;
define token instr(16) op=(8,15) x=(0,7);
:a x is op=0x90 & x { }
:b x is (op=0x10 | op=0x20) & x { }
"#,
        )
        .expect("parses");
        let index = Index::build(&spec);
        let root = spec.table(spec.root());
        let (a, b) = (root.constructors[0], root.constructors[1]);
        assert!(index.may_start(a, &[0x00, 0x90], 0));
        assert!(!index.may_start(a, &[0x00, 0x91], 0));
        // Two alternatives keep only the bits they agree on, so both of them
        // still pass.
        assert!(index.may_start(b, &[0x00, 0x10], 0));
        assert!(index.may_start(b, &[0x00, 0x20], 0));
        // And the filter stays a filter: 0x30 agrees with both on every bit
        // they agree on, so it is admitted here even though neither
        // alternative really matches it. The real test rejects it.
        assert!(index.may_start(b, &[0x00, 0x30], 0));
        assert!(
            !index.may_start(b, &[0x00, 0x99], 0),
            "no alternative admits it"
        );
    }

    /// Bucketing must not change which constructor a table produces, only how
    /// fast it is found. Every bucket has to hold every constructor that could
    /// match, in the same order the full list has them in.
    #[test]
    fn a_bucket_holds_every_constructor_the_full_list_would_have_tried() {
        let mut text = String::from(
            "define endian=little;\n\
             define space ram type=ram_space size=4 default;\n\
             define token instr(16) op=(8,15) sub=(4,7) x=(0,3);\n",
        );
        for i in 0..40 {
            text.push_str(&format!(":i{i} x is op={i} & x {{ }}\n"));
        }
        // And one that constrains nothing in the decision byte, so it has to
        // appear in every bucket.
        text.push_str(":any x is sub=0 & x { }\n");
        let spec = crate::parse_str(&text).expect("parses");
        let index = Index::build(&spec);
        let root = spec.root();
        for value in 0..256u32 {
            let stream = [0x00u8, value as u8];
            let got = index.candidates(root, &stream);
            let want: Vec<ConstructorId> = index
                .table(root)
                .iter()
                .copied()
                .filter(|id| index.may_start(*id, &stream, 0))
                .collect();
            let got: Vec<ConstructorId> = got
                .iter()
                .copied()
                .filter(|id| index.may_start(*id, &stream, 0))
                .collect();
            assert_eq!(got, want, "bucket for byte {value:#04x}");
        }
        // A stream too short to reach the decision byte still offers the
        // constructors that do not need it.
        assert!(!index.candidates(root, &[0x00]).is_empty());
    }

    #[test]
    fn a_constrained_first_byte_is_not_satisfied_by_a_missing_byte() {
        let spec = crate::parse_str(
            r#"
define endian=little;
define space ram type=ram_space size=4 default;
define token instr(16) op=(8,15) x=(0,7);
:a x is op=0 & x { }
"#,
        )
        .expect("parses");
        let index = Index::build(&spec);
        let a = spec.table(spec.root()).constructors[0];
        assert!(!index.may_start(a, &[], 0), "no bytes cannot satisfy op=0");
        assert!(index.may_start(a, &[0x00, 0x00], 0));
    }
}
