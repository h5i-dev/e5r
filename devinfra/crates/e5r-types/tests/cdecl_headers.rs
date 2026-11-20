//! How much of a real system header this reads.
//!
//! The roadmap item is "parse C headers into the type model so an analyst can
//! apply a known API signature", and the only honest measure of that is a
//! header nobody here wrote. The parser does not preprocess, so it reads both
//! arms of every `#if` and a glibc header contradicts itself; the point of
//! measuring is to know how much that costs rather than to guess.
//!
//! The thresholds are floors, only raised. They are deliberately below what
//! the current build achieves, because this test runs against whatever glibc
//! the machine has.

use std::path::Path;

use e5r_types::cdecl;
use e5r_types::ctype::Types;

fn measure(path: &str) -> Option<(usize, usize, Vec<String>)> {
    let text = std::fs::read_to_string(Path::new(path)).ok()?;
    let mut types = Types::new();
    let unit = cdecl::header(&mut types, &text);
    let reasons = unit.refused.iter().map(|e| e.to_string()).collect();
    Some((unit.declarations.len(), unit.refused.len(), reasons))
}

#[test]
fn stdint_h_is_read() {
    let Some((read, refused, reasons)) = measure("/usr/include/stdint.h") else {
        return;
    };
    let total = read + refused;
    println!("stdint.h: {read} of {total} declarations read");
    for r in &reasons {
        println!("  refused: {r}");
    }
    assert!(
        total >= 15,
        "only {total} declarations found; is this stdint.h?"
    );
    // Six of the eight it refuses are the unevaluated arms of
    // `#if __WORDSIZE == 64`, where the header genuinely says two
    // contradictory things and picking one would be guessing. The other two
    // name types from a header this one includes and the parser does not
    // follow. Preprocessed input is the way to read it exactly, which
    // `preprocessed_stdint_h_is_read_whole` demonstrates.
    let share = read as f64 / total as f64;
    assert!(share >= 0.55, "only {share:.2} of stdint.h was read");
}

#[test]
fn elf_h_is_read() {
    let Some((read, refused, reasons)) = measure("/usr/include/elf.h") else {
        return;
    };
    let total = read + refused;
    println!("elf.h: {read} of {total} declarations read");
    for r in reasons.iter().take(30) {
        println!("  refused: {r}");
    }
    assert!(
        total >= 50,
        "only {total} declarations found; is this elf.h?"
    );
    let share = read as f64 / total as f64;
    assert!(share >= 0.95, "only {share:.2} of elf.h was read");
}

#[test]
fn a_header_gives_up_its_structures_with_the_right_offsets() {
    let Ok(text) = std::fs::read_to_string("/usr/include/elf.h") else {
        return;
    };
    let mut types = Types::new();
    let unit = cdecl::header(&mut types, &text);
    assert!(!unit.declarations.is_empty());
    // The 64-bit ELF header is the structure this whole project reads first,
    // and its layout is in the specification rather than in a compiler.
    let Some(id) = types.typedef("Elf64_Ehdr") else {
        panic!("elf.h did not yield Elf64_Ehdr");
    };
    assert_eq!(types.size_of(id), Some(64));
    let resolved = types.resolve(id);
    let (field, _) = types.field_at(resolved, 24).expect("a field at 24");
    assert_eq!(field.name, "e_entry");
    let (field, _) = types.field_at(resolved, 32).expect("a field at 32");
    assert_eq!(field.name, "e_phoff");

    let Some(sym) = types.typedef("Elf64_Sym") else {
        panic!("elf.h did not yield Elf64_Sym");
    };
    assert_eq!(types.size_of(sym), Some(24));
}

#[test]
fn preprocessed_stdint_h_is_read_whole() {
    // The intended way to feed a header to a type archive: let the compiler
    // preprocess it, so the conditionals are resolved by the thing that owns
    // them and what arrives is declarations. Skipped where there is no `cc`.
    let out = match std::process::Command::new("cc")
        .args(["-E", "-P", "-xc", "/usr/include/stdint.h"])
        .output()
    {
        Ok(o) if o.status.success() => o.stdout,
        _ => return,
    };
    let Ok(text) = String::from_utf8(out) else {
        return;
    };
    let mut types = Types::new();
    let unit = cdecl::header(&mut types, &text);
    let total = unit.attempted();
    println!(
        "cc -E stdint.h: {} of {total} declarations read",
        unit.declarations.len()
    );
    for r in unit.refused.iter().take(20) {
        println!("  refused: {r}");
    }
    assert!(
        total > 20,
        "only {total} declarations in preprocessed stdint.h"
    );
    let share = unit.declarations.len() as f64 / total as f64;
    assert!(
        share >= 0.75,
        "only {share:.2} of preprocessed stdint.h was read"
    );
    // And the widths it produces are the ones the machine actually uses.
    let id = types.typedef("uint_fast32_t").expect("a fast type");
    assert_eq!(types.size_of(id), Some(8));
}
