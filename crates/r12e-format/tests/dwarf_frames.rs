//! Inlined frames, call sites and location lists, measured against readelf.
//!
//! The comparison is entry for entry rather than by count: every
//! `DW_TAG_inlined_subroutine` readelf prints has to appear in the right
//! function with the same call line and the same address ranges, every
//! `DW_TAG_call_site` with the same return address and the same number of
//! described arguments, and every variable whose location is a list has to
//! carry exactly the ranges the list section holds.
//!
//! The oracle is a different implementation of the same specification, which
//! is the only kind of agreement worth anything here.

use std::collections::BTreeMap;
use std::path::{Path, PathBuf};
use std::process::Command;

use r12e_format::LoadOptions;
use r12e_format::dwarf::DebugInfo;

/// The fixtures that carry inlining, call sites and location lists. Two
/// producers: gcc writes the ranges as section offsets, clang reaches them by
/// index through a base, and the two paths share no code.
const FIXTURES: [&str; 9] = [
    "hello.a64.O2",
    "wide.a64.O2.o",
    "wide.a64.O3.o",
    "shapes.a64.O2.o",
    "wide.x64.O2.o",
    "shapes.x64.O2.o",
    // DWARF 4: `.debug_ranges` and `.debug_loc`, and the GNU call site tags.
    "hello.a64.dwarf4",
    "wide.a64.dwarf4.o",
    "shapes.a64.dwarf4.o",
];

fn corpus() -> Option<PathBuf> {
    let d = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../fixtures/build");
    d.is_dir().then(|| d.canonicalize().unwrap())
}

fn readelf(path: &Path, what: &str) -> Option<String> {
    let out = Command::new("readelf")
        .arg(format!("--debug-dump={what}"))
        .arg(path)
        .output()
        .ok()?;
    out.status
        .success()
        .then(|| String::from_utf8_lossy(&out.stdout).into_owned())
}

/// One entry of a list section as readelf prints it.
#[derive(Debug, Clone, PartialEq, Eq)]
enum Entry {
    Range(u64, u64),
    /// A base address, which is an entry of the list and therefore a place a
    /// list can start, but not a range.
    Base,
    End,
}

/// The list sections, flattened to entries in file order with the offset each
/// one sits at. A list is then every entry from its own offset to the next
/// end marker, which is how both formats delimit one.
///
/// readelf prints the addresses of a range on a continuation line when the
/// producer emitted GNU location views, so the offset carries over from the
/// last line that started with one.
fn list_entries(text: &str) -> Vec<(u64, Entry)> {
    let mut out = Vec::new();
    let mut offset = None;
    for line in text.lines() {
        let tokens: Vec<&str> = line.split_whitespace().collect();
        let Some(first) = tokens.first() else {
            continue;
        };
        if first.len() == 8 && first.chars().all(|c| c.is_ascii_hexdigit()) {
            offset = u64::from_str_radix(first, 16).ok();
        }
        let Some(at) = offset else { continue };
        if line.contains("<End of list>") {
            out.push((at, Entry::End));
            continue;
        }
        // Exactly sixteen hex digits: a 64-bit address as readelf prints one.
        // Anything shorter is an offset or a view number, which is what makes
        // this safe to run over every line.
        let wide = |t: &&str| t.len() == 16 && t.chars().all(|c| c.is_ascii_hexdigit());
        if line.contains("(base address)") {
            out.push((at, Entry::Base));
            continue;
        }
        if let Some(i) = tokens.windows(2).position(|w| wide(&w[0]) && wide(&w[1])) {
            let begin = u64::from_str_radix(tokens[i], 16).unwrap_or(0);
            let end = u64::from_str_radix(tokens[i + 1], 16).unwrap_or(0);
            out.push((at, Entry::Range(begin, end)));
        }
    }
    out
}

/// The ranges of the list that starts at `at`, empty ones dropped: an entry
/// whose start equals its end covers no address and is not a range.
fn list_at(entries: &[(u64, Entry)], at: u64) -> Vec<(u64, u64)> {
    let Some(start) = entries.iter().position(|(o, _)| *o == at) else {
        return Vec::new();
    };
    let mut out = Vec::new();
    for (_, e) in &entries[start..] {
        match e {
            Entry::End => break,
            Entry::Base => {}
            Entry::Range(b, n) if b != n => out.push((*b, *n)),
            Entry::Range(_, _) => {}
        }
    }
    out
}

/// One debugging information entry, as readelf printed it.
#[derive(Debug, Clone, Default)]
struct Die {
    tag: String,
    /// Offset in `.debug_info`, which is how one entry references another.
    offset: u64,
    parent: Option<usize>,
    attributes: BTreeMap<String, String>,
}

impl Die {
    /// The trailing hex number of an attribute readelf printed, which is where
    /// it puts the value whether or not the form indirected to get there.
    fn hex(&self, name: &str) -> Option<u64> {
        let v = self.attributes.get(name)?;
        let last = v.split_whitespace().next_back()?;
        u64::from_str_radix(last.trim_start_matches("0x").trim_end_matches(':'), 16).ok()
    }

    /// The leading hex number, for an attribute readelf follows with a note
    /// of its own: a location list offset prints as `0x12 (location list)`.
    fn hex_first(&self, name: &str) -> Option<u64> {
        let v = self.attributes.get(name)?;
        let first = v.split_whitespace().next()?;
        u64::from_str_radix(first.trim_start_matches("0x"), 16).ok()
    }

    fn number(&self, name: &str) -> Option<u64> {
        let v = self.attributes.get(name)?;
        v.split_whitespace().next()?.parse().ok()
    }

    fn text(&self, name: &str) -> Option<&str> {
        Some(
            self.attributes
                .get(name)?
                .rsplit(american_colon)
                .next()?
                .trim(),
        )
    }
}

/// readelf separates an attribute's decoration from its value with a colon,
/// and a name never contains one.
fn american_colon(c: char) -> bool {
    c == ':'
}

/// Parse `readelf --debug-dump=info` into a tree.
fn dies(text: &str) -> Vec<Die> {
    let mut out: Vec<Die> = Vec::new();
    let mut stack: Vec<usize> = Vec::new();
    for line in text.lines() {
        if let Some(rest) = line.split("Abbrev Number:").nth(1) {
            // ` <depth><offset>: Abbrev Number: n (DW_TAG_x)`
            let head = line.split_whitespace().next().unwrap_or_default();
            let depth = head
                .trim_start_matches('<')
                .split('>')
                .next()
                .and_then(|d| d.parse::<usize>().ok());
            let Some(depth) = depth else { continue };
            let offset = head
                .rsplit('<')
                .next()
                .and_then(|o| u64::from_str_radix(o.trim_end_matches(">:"), 16).ok())
                .unwrap_or_default();
            let Some(tag) = rest.split('(').nth(1).and_then(|t| t.split(')').next()) else {
                // A zero abbreviation closes a sibling chain and names no tag.
                stack.truncate(depth);
                continue;
            };
            stack.truncate(depth);
            let parent = stack.last().copied();
            out.push(Die {
                tag: tag.to_string(),
                offset,
                parent,
                attributes: BTreeMap::new(),
            });
            stack.push(out.len() - 1);
            continue;
        }
        let Some(at) = line.find("DW_AT_") else {
            continue;
        };
        let rest = &line[at..];
        let Some((name, value)) = rest.split_once(':') else {
            continue;
        };
        if let Some(die) = stack.last().and_then(|i| out.get_mut(*i)) {
            die.attributes
                .insert(name.trim().to_string(), value.trim().to_string());
        }
    }
    out
}

/// The name a DIE carries, following the abstract origin an inlined copy has
/// instead of a name of its own. The reader has to do the same, and a name
/// that only the origin carries is the case that matters.
fn name_of(dies: &[Die], at: usize) -> Option<String> {
    let by_offset: BTreeMap<u64, usize> = dies
        .iter()
        .enumerate()
        .map(|(i, d)| (d.offset, i))
        .collect();
    let mut at = Some(at);
    for _ in 0..8 {
        let die = dies.get(at?)?;
        if let Some(name) = die.text("DW_AT_name") {
            return Some(name.to_string());
        }
        let next = die
            .hex("DW_AT_abstract_origin")
            .or_else(|| die.hex("DW_AT_specification"))?;
        at = by_offset.get(&next).copied();
    }
    None
}

/// The nearest enclosing subprogram of a DIE, and its entry address.
fn enclosing_function(dies: &[Die], mut at: usize) -> Option<u64> {
    for _ in 0..64 {
        let die = dies.get(at)?;
        if die.tag == "DW_TAG_subprogram" {
            return die.hex("DW_AT_low_pc");
        }
        at = die.parent?;
    }
    None
}

/// Address ranges a DIE covers, resolved the way the reader has to resolve
/// them: through the range list section, or from the contiguous pair.
fn die_ranges(die: &Die, ranges: &[(u64, Entry)]) -> Option<Vec<(u64, u64)>> {
    if let Some(at) = die.hex("DW_AT_ranges") {
        return Some(list_at(ranges, at));
    }
    let low = die.hex("DW_AT_low_pc")?;
    let high = die.hex("DW_AT_high_pc")?;
    // DWARF 4 and 5 write the second as a length.
    let end = if high > low { high } else { low + high };
    (end > low).then(|| vec![(low, end)])
}

/// Where the loader put the image relative to the addresses readelf prints.
///
/// A relocatable object has no load address of its own, so the loader gives it
/// one and every address the reader reports moves with it. Recovered by
/// agreeing on the functions both sides name, rather than assumed.
fn rebase(dies: &[Die], debug: &DebugInfo) -> u64 {
    let mut seen: Vec<u64> = Vec::new();
    for die in dies.iter().filter(|d| d.tag == "DW_TAG_subprogram") {
        let (Some(low), Some(name)) = (die.hex("DW_AT_low_pc"), die.text("DW_AT_name")) else {
            continue;
        };
        for (addr, f) in &debug.functions {
            if f.name == name {
                seen.push(addr.get().wrapping_sub(low));
            }
        }
    }
    seen.sort_unstable();
    seen.dedup();
    match seen.as_slice() {
        [one] => *one,
        // Nothing to go on, or two answers: zero is then the honest guess and
        // the comparison below fails loudly rather than quietly passing.
        _ => 0,
    }
}

fn open(dir: &Path, name: &str) -> Option<(PathBuf, DebugInfo)> {
    let path = dir.join(name);
    let data = std::fs::read(&path).ok()?;
    let obj = r12e_format::load(&data, &LoadOptions::default()).ok()?;
    Some((path, obj.debug?))
}

#[test]
fn inlined_frames_match_readelf() {
    let Some(dir) = corpus() else { return };
    let mut checked = 0usize;
    let mut files = 0usize;
    for name in FIXTURES {
        let Some((path, debug)) = open(&dir, name) else {
            continue;
        };
        let (Some(info), Some(ranges)) = (readelf(&path, "info"), readelf(&path, "Ranges")) else {
            return; // no readelf here
        };
        let dies = dies(&info);
        let ranges = list_entries(&ranges);
        let base = rebase(&dies, &debug);
        let mut expected = 0usize;
        for (i, die) in dies.iter().enumerate() {
            if die.tag != "DW_TAG_inlined_subroutine" {
                continue;
            }
            let Some(function) = enclosing_function(&dies, i) else {
                continue;
            };
            let Some(want) = die_ranges(die, &ranges) else {
                continue;
            };
            let want: Vec<(u64, u64)> = want
                .into_iter()
                .map(|(b, e)| (b.wrapping_add(base), e.wrapping_add(base)))
                .collect();
            if want.is_empty() {
                continue;
            }
            expected += 1;
            let function = function.wrapping_add(base);
            let f = debug
                .functions
                .get(&r12e_core::Addr(function))
                .unwrap_or_else(|| panic!("{name}: no function at {function:#x}"));
            let ours: Vec<Vec<(u64, u64)>> = f
                .inlines
                .iter()
                .map(|i| {
                    i.ranges
                        .iter()
                        .map(|r| (r.start().get(), r.end().get()))
                        .collect()
                })
                .collect();
            assert!(
                ours.contains(&want),
                "{name}: the inlined frame at {want:#x?} in the function at {function:#x} \
                 is not among the {} we read: {ours:#x?}",
                ours.len()
            );
            // The call site, which is the whole point of recovering the frame.
            let found = f
                .inlines
                .iter()
                .find(|f| {
                    f.ranges
                        .iter()
                        .map(|r| (r.start().get(), r.end().get()))
                        .eq(want.iter().copied())
                })
                .unwrap();
            assert_eq!(
                found.call_line.map(u64::from),
                die.number("DW_AT_call_line"),
                "{name}: call line of the frame at {want:#x?}"
            );
            assert_eq!(
                found.call_column.map(u64::from),
                die.number("DW_AT_call_column"),
                "{name}: call column of the frame at {want:#x?}"
            );
            checked += 1;
        }
        let ours: usize = debug.functions.values().map(|f| f.inlines.len()).sum();
        assert_eq!(
            ours, expected,
            "{name}: readelf describes {expected} inlined frames and we read {ours}"
        );
        files += 1;
    }
    assert!(checked > 0, "no fixture carried an inlined frame");
    println!("inlined frames: {checked} compared against readelf over {files} files");
}

#[test]
fn call_sites_match_readelf() {
    let Some(dir) = corpus() else { return };
    let mut checked = 0usize;
    for name in FIXTURES {
        let Some((path, debug)) = open(&dir, name) else {
            continue;
        };
        let Some(info) = readelf(&path, "info") else {
            return;
        };
        let dies = dies(&info);
        let base = rebase(&dies, &debug);
        // (function, return pc) -> how many arguments were described.
        let mut expected: BTreeMap<(u64, u64), usize> = BTreeMap::new();
        for (i, die) in dies.iter().enumerate() {
            let gnu = die.tag == "DW_TAG_GNU_call_site";
            if die.tag != "DW_TAG_call_site" && !gnu {
                continue;
            }
            let Some(function) = enclosing_function(&dies, i) else {
                continue;
            };
            let return_pc = if gnu {
                die.hex("DW_AT_low_pc")
            } else {
                die.hex("DW_AT_call_return_pc")
            };
            let Some(return_pc) = return_pc else { continue };
            let parameters = dies
                .iter()
                .filter(|c| {
                    c.parent == Some(i)
                        && (c.tag == "DW_TAG_call_site_parameter"
                            || c.tag == "DW_TAG_GNU_call_site_parameter")
                })
                .count();
            expected.insert(
                (function.wrapping_add(base), return_pc.wrapping_add(base)),
                parameters,
            );
        }
        let mut ours: BTreeMap<(u64, u64), usize> = BTreeMap::new();
        for (addr, f) in &debug.functions {
            for c in &f.call_sites {
                let Some(pc) = c.return_pc else { continue };
                ours.insert((addr.get(), pc.get()), c.parameters.len());
            }
        }
        assert_eq!(
            ours, expected,
            "{name}: the call sites disagree with readelf"
        );
        checked += expected.len();
    }
    assert!(checked > 0, "no fixture carried a call site");
    println!("call sites: {checked} compared against readelf, argument counts included");
}

#[test]
fn location_lists_match_readelf() {
    let Some(dir) = corpus() else { return };
    let mut checked = 0usize;
    for name in FIXTURES {
        let Some((path, debug)) = open(&dir, name) else {
            continue;
        };
        let (Some(info), Some(locations)) = (readelf(&path, "info"), readelf(&path, "loc")) else {
            return;
        };
        let dies = dies(&info);
        let locations = list_entries(&locations);
        let base = rebase(&dies, &debug);
        for (i, die) in dies.iter().enumerate() {
            if die.tag != "DW_TAG_formal_parameter" && die.tag != "DW_TAG_variable" {
                continue;
            }
            // Only the list form: a single expression is a different path.
            let Some(value) = die.attributes.get("DW_AT_location") else {
                continue;
            };
            if !value.contains("location list") {
                continue;
            }
            let Some(at) = die.hex_first("DW_AT_location") else {
                continue;
            };
            // Named, and a direct child of something the reader collects
            // locals from: a variable inside a lexical block is not read.
            let Some(variable) = name_of(&dies, i) else {
                continue;
            };
            let parent = die.parent.and_then(|p| dies.get(p));
            let direct = parent.is_some_and(|p| {
                p.tag == "DW_TAG_subprogram" || p.tag == "DW_TAG_inlined_subroutine"
            });
            if !direct {
                continue;
            }
            let Some(function) = enclosing_function(&dies, i) else {
                continue;
            };
            let Some(f) = debug
                .functions
                .get(&r12e_core::Addr(function.wrapping_add(base)))
            else {
                continue;
            };
            let want: Vec<(u64, u64)> = list_at(&locations, at)
                .into_iter()
                .map(|(b, e)| (b.wrapping_add(base), e.wrapping_add(base)))
                .collect();
            if want.is_empty() {
                continue;
            }
            let candidates: Vec<&r12e_format::dwarf::DebugLocal> = f
                .locals
                .iter()
                .chain(f.inlines.iter().flat_map(|i| i.locals.iter()))
                .filter(|l| l.name == variable)
                .collect();
            let ours: Vec<Vec<(u64, u64)>> = candidates
                .iter()
                .map(|l| {
                    l.locations
                        .iter()
                        .map(|e| (e.range.start().get(), e.range.end().get()))
                        .collect()
                })
                .collect();
            assert!(
                ours.contains(&want),
                "{name}: the location list at {at:#x} for the {} {variable:?} is \
                 {want:#x?}, and we read {ours:#x?}",
                die.tag,
            );
            checked += 1;
        }
    }
    assert!(checked > 0, "no fixture carried a location list");
    println!("location lists: {checked} variables compared against readelf, range for range");
}

#[test]
fn a_variable_that_moves_is_reported_where_it_is() {
    // The property the whole feature exists for: at -O2 a value lives in a
    // register for part of a function and somewhere else for the rest, and a
    // single-location reader is wrong for most of it.
    let Some(dir) = corpus() else { return };
    let mut moved = 0usize;
    for name in FIXTURES {
        let Some((_, debug)) = open(&dir, name) else {
            continue;
        };
        for f in debug.functions.values() {
            for local in &f.locals {
                let mut places: Vec<&r12e_format::dwarf::Location> =
                    local.locations.iter().map(|e| &e.location).collect();
                places.dedup();
                if places.len() < 2 {
                    continue;
                }
                moved += 1;
                // Every range reports the place that range says, and nothing
                // reports a place outside its own range.
                for entry in &local.locations {
                    assert_eq!(
                        local.location_at(entry.range.start()),
                        Some(&entry.location),
                        "{name}: {} at {:#x}",
                        local.name,
                        entry.range.start()
                    );
                }
            }
        }
    }
    assert!(
        moved > 0,
        "no fixture had a variable that changes location, so this proves nothing"
    );
    println!("{moved} variables change storage inside their function");
}
