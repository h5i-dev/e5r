//! Function-local references and the existing evidence behind their targets.

use e5r_analysis::{Found, Function, Program, Xref};
use e5r_core::Addr;

/// True only for bytes covered by recovered blocks, excluding gaps in a split function.
pub fn contains(function: &Function, addr: Addr) -> bool {
    function
        .cfg
        .blocks
        .values()
        .any(|block| block.range.contains(addr))
}

/// A recovered reference with target context. No new references are inferred.
pub struct Reference<'a> {
    /// The reference recorded by analysis.
    pub xref: Xref,
    /// A function or symbol name, when available.
    pub name: Option<String>,
    /// A recovered function containing the target, for navigation.
    pub function: Option<Addr>,
    /// The containing extracted string, including references into its interior.
    pub string: Option<&'a Found>,
    /// The section containing the target.
    pub section: Option<&'a str>,
    /// Up to 32 mapped bytes beginning at the target.
    pub bytes: Vec<u8>,
}

/// Every outgoing reference from the function's recovered blocks, in address order.
pub fn outgoing<'a>(program: &'a Program, function: &Function) -> Vec<Reference<'a>> {
    let all = program.xrefs.all();
    function
        .cfg
        .blocks
        .values()
        .flat_map(|block| {
            let lo = all.partition_point(|xref| xref.from < block.range.start());
            let hi = all.partition_point(|xref| xref.from < block.range.end());
            all[lo..hi].iter().map(|xref| {
                let string = program
                    .strings
                    .iter()
                    .find(|s| xref.to >= s.addr && xref.to.get() - s.addr.get() < s.len);
                let section = program
                    .object
                    .sections
                    .iter()
                    .find(|section| section.range.contains(xref.to))
                    .map(|section| section.name.as_str());
                let bytes = program
                    .object
                    .memory
                    .segment_at(xref.to)
                    .and_then(|segment| segment.slice_to_end(xref.to))
                    .map(|bytes| bytes.iter().take(32).copied().collect())
                    .unwrap_or_default();
                Reference {
                    xref: *xref,
                    name: program.name_of(xref.to),
                    function: program.function_at(xref.to).map(|f| f.entry),
                    string,
                    section,
                    bytes,
                }
            })
        })
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;
    use e5r_analysis::{Options, XrefIndex, XrefKind, analyze, strings::Encoding};
    use e5r_core::Arch;
    use e5r_format::LoadOptions;

    #[test]
    fn split_functions_exclude_gap_references_and_keep_interior_string_targets() {
        // jmp +6 skips six bytes before ret; the hull contains bytes the CFG does not.
        // Use addresses beyond JavaScript's integer precision as well.
        let base = Addr(0x2000_0000_0000_1000);
        let mut bytes = vec![0x90; 64];
        bytes[..2].copy_from_slice(&[0xeb, 6]);
        bytes[8] = 0xc3;
        bytes[15..20].copy_from_slice(b"hello");
        let mut object = e5r_format::raw::load(
            &bytes,
            &LoadOptions {
                base: Some(base),
                arch: Some(Arch::X86_64),
                ..Default::default()
            },
        )
        .unwrap();
        object.function_hints.push(e5r_format::FunctionHint {
            addr: base,
            size: None,
            name: Some("entry".into()),
            provenance: e5r_core::Provenance::new(e5r_core::Evidence::EntryPoint),
        });
        let mut program = analyze(
            object,
            &Options {
                scan_gaps: false,
                follow_calls: false,
                ..Default::default()
            },
        );
        let target = base.wrapping_offset(16);
        program.xrefs = XrefIndex::build(
            [0, 4, 8]
                .into_iter()
                .map(|offset| Xref {
                    from: base.wrapping_offset(offset),
                    to: target,
                    kind: XrefKind::Data,
                })
                .collect(),
        );
        program.strings = vec![Found {
            addr: base.wrapping_offset(15),
            len: 5,
            encoding: Encoding::Ascii,
            text: "hello".into(),
        }];
        let function = program.function(base).unwrap();
        assert!(contains(function, base.wrapping_offset(8)));
        assert!(!contains(function, base.wrapping_offset(4)));
        let references = outgoing(&program, function);
        assert_eq!(references.len(), 2);
        assert_eq!(references[1].xref.from, base.wrapping_offset(8));
        assert_eq!(references[1].string.unwrap().text, "hello");
        assert_eq!(&references[1].bytes[..4], b"ello");
        assert_eq!(references[1].bytes.len(), 32);
        assert_eq!(references[1].section, Some("image"));
    }
}
