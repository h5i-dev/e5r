//! Metadata v2 (docs/isa/metadata.md): round trips, position independence,
//! concatenated tables, and the reader's refusals.

use nocompiler::isa::Reg;
use nocompiler::meta::{self, Callee};
use nocompiler::profile::{FuncMeta, Kind, Level, Node, Range, RangeSource, Slot, SlotKind};
use std::collections::BTreeMap;

fn node(kind: Kind, start: u64, end: u64, label: Option<&str>, children: Vec<Node>) -> Node {
    Node {
        kind,
        start,
        end,
        label: label.map(String::from),
        children,
    }
}

/// `sum2` of the v1 spec's example, at `entry`, calling `sum` at `callee`.
fn sum2(entry: u64, callee: u64) -> FuncMeta {
    FuncMeta {
        name: "sum2".into(),
        entry,
        size: 84,
        level: Level::L2,
        frame: 32,
        depth: Some(32),
        callees: vec![callee],
        nodes: vec![node(
            Kind::Block,
            entry + 8,
            entry + 40,
            Some("done"),
            vec![node(Kind::Loop, entry + 12, entry + 36, None, vec![])],
        )],
        slots: vec![
            Slot {
                off: 0,
                kind: SlotKind::Save(Reg(18)),
            },
            Slot {
                off: 8,
                kind: SlotKind::Save(Reg(9)),
            },
            Slot {
                off: 16,
                kind: SlotKind::Spill,
            },
            Slot {
                off: 24,
                kind: SlotKind::Save(Reg(1)),
            },
        ],
        ranges: vec![Range {
            off: 32,
            len: 12,
            source: RangeSource::Dwarf,
        }],
        ext: vec![1, 2, 3],
    }
}

fn names(pairs: &[(u64, &str)]) -> BTreeMap<u64, String> {
    pairs.iter().map(|&(a, n)| (a, n.to_string())).collect()
}
fn entries(pairs: &[(u64, &str)]) -> BTreeMap<String, u64> {
    pairs.iter().map(|&(a, n)| (n.to_string(), a)).collect()
}

#[test]
fn a_table_round_trips() {
    let m = sum2(0x11000, 0x10000);
    let syms = [(0x10000, "sum"), (0x11000, "sum2")];
    let enc = meta::encode(std::slice::from_ref(&m), &names(&syms)).unwrap();
    let recs = meta::decode(&enc).unwrap();
    assert_eq!(recs.len(), 1);
    assert_eq!(recs[0].callees, vec![Callee::Sym("sum".into())]);
    assert_eq!(
        recs[0].meta.entry, 0,
        "decoded positions are offsets from the entry"
    );
    assert_eq!(recs[0].meta.nodes[0].start, 8);
    assert_eq!(recs[0].place(0x11000, &entries(&syms)).unwrap(), m);
}

#[test]
fn the_bytes_do_not_depend_on_where_the_functions_are() {
    let a = meta::encode(
        &[sum2(0x11000, 0x10000)],
        &names(&[(0x10000, "sum"), (0x11000, "sum2")]),
    )
    .unwrap();
    let b = meta::encode(
        &[sum2(0x80004000, 0x80000000)],
        &names(&[(0x80000000, "sum"), (0x80004000, "sum2")]),
    )
    .unwrap();
    assert_eq!(a, b);
}

#[test]
fn concatenated_tables_are_one_section() {
    let syms = [(0x10000, "sum"), (0x11000, "sum2")];
    let mut leaf = sum2(0x10000, 0);
    leaf.name = "sum".into();
    leaf.callees.clear();
    leaf.depth = Some(0);
    let mut d = meta::encode(&[leaf], &names(&syms)).unwrap();
    d.extend(meta::encode(&[sum2(0x11000, 0x10000)], &names(&syms)).unwrap());
    let recs = meta::decode(&d).unwrap();
    assert_eq!(
        recs.iter()
            .map(|r| r.meta.name.as_str())
            .collect::<Vec<_>>(),
        ["sum", "sum2"]
    );
}

#[test]
fn the_reader_refuses_what_is_not_a_table() {
    let syms = [(0x10000, "sum"), (0x11000, "sum2")];
    let enc = meta::encode(&[sum2(0x11000, 0x10000)], &names(&syms)).unwrap();
    assert!(meta::decode(&enc[..enc.len() - 1]).is_err(), "truncated");
    let mut x = enc.clone();
    x.push(0);
    assert!(meta::decode(&x).is_err(), "trailing bytes");
    let mut x = enc.clone();
    x[4] = 3;
    assert!(meta::decode(&x).is_err(), "unknown version");
    let mut x = enc.clone();
    x[6] = 1;
    assert!(meta::decode(&x).is_err(), "reserved bytes");
    assert!(meta::decode(&[]).is_err(), "empty");
    // A callee that is not a function of the file cannot be placed.
    let recs = meta::decode(&enc).unwrap();
    assert!(
        recs[0]
            .place(0x11000, &entries(&[(0x11000, "sum2")]))
            .is_err()
    );
    // A callee with no symbol cannot be written.
    assert!(meta::encode(&[sum2(0x11000, 0x10000)], &names(&[(0x11000, "sum2")])).is_err());
}
