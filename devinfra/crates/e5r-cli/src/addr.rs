//! Address expressions on the command line.
//!
//! `main`, `0x4006e8`, `main+0x20`, `sub_4006e8`. Anything a person would type
//! after reading a listing.

use e5r_analysis::Program;
use e5r_core::Addr;

/// Parse a plain number in hex, decimal, octal or binary.
pub fn parse_number(s: &str) -> Option<u64> {
    let s = s.trim().replace('_', "");
    let (radix, digits) = match s.get(..2) {
        Some("0x") | Some("0X") => (16, &s[2..]),
        Some("0b") | Some("0B") => (2, &s[2..]),
        Some("0o") | Some("0O") => (8, &s[2..]),
        _ => (10, &s[..]),
    };
    u64::from_str_radix(digits, radix).ok()
}

/// Resolve an expression against a program.
pub fn resolve(program: &Program, expr: &str) -> Option<Addr> {
    let expr = expr.trim();
    // A trailing offset, as a listing prints it.
    if let Some(i) = expr.rfind(['+', '-']) {
        if i > 0 {
            let (base, rest) = expr.split_at(i);
            let sign = rest.starts_with('-');
            if let (Some(b), Some(off)) =
                (resolve_atom(program, base.trim()), parse_number(&rest[1..]))
            {
                return if sign {
                    b.checked_sub(off)
                } else {
                    b.checked_add(off)
                };
            }
        }
    }
    resolve_atom(program, expr)
}

fn resolve_atom(program: &Program, s: &str) -> Option<Addr> {
    if let Some(n) = parse_number(s) {
        return Some(Addr(n));
    }
    // The synthetic name a function gets when nothing named it.
    if let Some(hex) = s.strip_prefix("sub_") {
        if let Ok(v) = u64::from_str_radix(hex, 16) {
            return Some(Addr(v));
        }
    }
    if let Some(f) = program
        .functions
        .values()
        .find(|f| f.name.as_deref() == Some(s))
    {
        return Some(f.entry);
    }
    program
        .object
        .symbols
        .iter()
        .find(|sym| sym.name == s && sym.addr != Addr::ZERO)
        .map(|sym| sym.addr)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn numbers_in_every_base() {
        assert_eq!(parse_number("0x4006e8"), Some(0x4006e8));
        assert_eq!(parse_number("4198632"), Some(4198632));
        assert_eq!(parse_number("0b1010"), Some(10));
        assert_eq!(parse_number("0o17"), Some(15));
        assert_eq!(parse_number("0x40_06e8"), Some(0x4006e8));
        assert_eq!(parse_number("main"), None);
    }
}
