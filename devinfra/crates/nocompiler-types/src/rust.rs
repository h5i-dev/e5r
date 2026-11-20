//! Rust name demangling, both schemes.
//!
//! The legacy scheme is Itanium with a 17-character hash path component on the
//! end, so it is recognized by that suffix and handed to the Itanium parser
//! with the hash removed. The v0 scheme is its own grammar; what is implemented
//! here is the path structure, which is the part that makes a listing readable.

use crate::itanium;

/// The legacy scheme: `_ZN...17h<16 hex>E`.
pub fn demangle_legacy(name: &str) -> Option<String> {
    let body = name
        .strip_prefix("_ZN")
        .or_else(|| name.strip_prefix("__ZN"))?;
    // The hash is the last component: "17h" then sixteen hex digits.
    let hash_at = body.rfind("17h")?;
    let after = &body[hash_at + 3..];
    if after.len() < 16 || !after[..16].bytes().all(|b| b.is_ascii_hexdigit()) {
        return None;
    }
    let without = format!("_ZN{}E", &body[..hash_at]);
    let out = itanium::demangle(&without)?;
    // Rust paths use `::` the same way, and legacy names never have parameters.
    Some(out)
}

/// The v0 scheme: `_R` then a path.
///
/// Implemented far enough to render a path: crate and module components,
/// nested items, and the impl and trait-impl wrappers. Generic arguments are
/// summarized rather than expanded, because a full expansion needs the type
/// grammar and a half-expanded one reads worse than none.
pub fn demangle_v0(name: &str) -> Option<String> {
    let body = name.strip_prefix("_R")?;
    // An optional instantiating-crate suffix and a leading underscore.
    let body = body.strip_prefix('_').unwrap_or(body);
    let mut p = V0 {
        s: body,
        at: 0,
        depth: 0,
    };
    let out = p.path().ok()?;
    Some(out)
}

struct V0<'a> {
    s: &'a str,
    at: usize,
    depth: u32,
}

type R<T> = Result<T, ()>;

impl<'a> V0<'a> {
    fn rest(&self) -> &'a str {
        &self.s[self.at..]
    }

    fn peek(&self) -> Option<char> {
        self.rest().chars().next()
    }

    fn eat(&mut self, c: char) -> bool {
        if self.peek() == Some(c) {
            self.at += 1;
            true
        } else {
            false
        }
    }

    /// A base-62 index, used for back references and disambiguators.
    fn base62(&mut self) -> R<u64> {
        if self.eat('_') {
            return Ok(0);
        }
        let digits: String = self
            .rest()
            .chars()
            .take_while(|c| c.is_ascii_alphanumeric())
            .collect();
        self.at += digits.len();
        if !self.eat('_') {
            return Err(());
        }
        let mut v: u64 = 0;
        for c in digits.chars() {
            let d = match c {
                '0'..='9' => c as u64 - '0' as u64,
                'a'..='z' => c as u64 - 'a' as u64 + 10,
                _ => c as u64 - 'A' as u64 + 36,
            };
            v = v.checked_mul(62).and_then(|x| x.checked_add(d)).ok_or(())?;
        }
        Ok(v + 1)
    }

    /// `<len> <chars>`, with an optional leading disambiguator.
    fn ident(&mut self) -> R<String> {
        if self.eat('s') {
            // A disambiguator, which is not part of the name.
            self.base62()?;
        }
        let digits: String = self
            .rest()
            .chars()
            .take_while(|c| c.is_ascii_digit())
            .collect();
        if digits.is_empty() {
            return Err(());
        }
        self.at += digits.len();
        // Punycode-encoded identifiers start with an underscore.
        let punycode = self.eat('_');
        let n: usize = digits.parse().map_err(|_| ())?;
        if self.rest().len() < n {
            return Err(());
        }
        let out = self.rest()[..n].to_string();
        self.at += n;
        // Punycode-encoded identifiers are left as they are encoded rather
        // than decoded; a half-decoded name would be worse than an encoded one.
        let _ = punycode;
        Ok(out)
    }

    fn enter(&mut self) -> R<()> {
        self.depth += 1;
        if self.depth > 64 { Err(()) } else { Ok(()) }
    }

    fn path(&mut self) -> R<String> {
        self.enter()?;
        let out = self.path_inner();
        self.depth -= 1;
        out
    }

    fn path_inner(&mut self) -> R<String> {
        match self.peek().ok_or(())? {
            // A crate root: a disambiguator then the crate name.
            'C' => {
                self.at += 1;
                if self.peek() == Some('s') {
                    self.at += 1;
                    self.base62()?;
                }
                self.ident()
            }
            // A named item inside a path.
            'N' => {
                self.at += 1;
                // The namespace letter: `v` value, `t` type, or a capital for
                // a compiler-generated one.
                let _ns = self.peek().ok_or(())?;
                self.at += 1;
                let parent = self.path()?;
                let name = self.ident()?;
                Ok(format!("{parent}::{name}"))
            }
            // An inherent impl.
            'M' => {
                self.at += 1;
                self.impl_path()?;
                let ty = self.ty_summary()?;
                Ok(format!("<{ty}>"))
            }
            // A trait impl.
            'X' => {
                self.at += 1;
                self.impl_path()?;
                let ty = self.ty_summary()?;
                let tr = self.path()?;
                Ok(format!("<{ty} as {tr}>"))
            }
            // A trait definition.
            'Y' => {
                self.at += 1;
                let ty = self.ty_summary()?;
                let tr = self.path()?;
                Ok(format!("<{ty} as {tr}>"))
            }
            // Generic arguments, which are summarized.
            'I' => {
                self.at += 1;
                let base = self.path()?;
                let mut n = 0;
                while !self.eat('E') {
                    if self.rest().is_empty() {
                        return Err(());
                    }
                    self.skip_generic()?;
                    n += 1;
                }
                Ok(if n == 0 {
                    base
                } else {
                    format!("{base}::<...>")
                })
            }
            // A back reference, which this parser does not resolve.
            'B' => {
                self.at += 1;
                self.base62()?;
                Ok("_".into())
            }
            _ => Err(()),
        }
    }

    /// The impl's defining path, which is not shown.
    fn impl_path(&mut self) -> R<()> {
        if self.peek() == Some('s') {
            self.at += 1;
            self.base62()?;
        }
        self.path()?;
        Ok(())
    }

    /// A type, rendered only far enough to be recognizable.
    fn ty_summary(&mut self) -> R<String> {
        self.enter()?;
        let out = self.ty_inner();
        self.depth -= 1;
        out
    }

    fn ty_inner(&mut self) -> R<String> {
        let c = self.peek().ok_or(())?;
        if let Some(name) = basic_type(c) {
            self.at += 1;
            return Ok(name.to_string());
        }
        match c {
            'R' | 'Q' => {
                self.at += 1;
                if self.peek() == Some('L') {
                    self.at += 1;
                    self.base62()?;
                }
                let inner = self.ty_summary()?;
                Ok(format!("&{inner}"))
            }
            'P' | 'O' => {
                self.at += 1;
                let inner = self.ty_summary()?;
                Ok(format!("*{inner}"))
            }
            'A' => {
                self.at += 1;
                let inner = self.ty_summary()?;
                while !self.eat('_') && !self.rest().is_empty() {
                    self.at += 1;
                }
                Ok(format!("[{inner}; _]"))
            }
            'S' => {
                self.at += 1;
                let inner = self.ty_summary()?;
                Ok(format!("[{inner}]"))
            }
            'T' => {
                self.at += 1;
                let mut parts = Vec::new();
                while !self.eat('E') {
                    if self.rest().is_empty() {
                        return Err(());
                    }
                    parts.push(self.ty_summary()?);
                }
                Ok(format!("({})", parts.join(", ")))
            }
            'B' => {
                self.at += 1;
                self.base62()?;
                Ok("_".into())
            }
            _ => self.path(),
        }
    }

    /// Consume one generic argument without rendering it.
    fn skip_generic(&mut self) -> R<()> {
        match self.peek().ok_or(())? {
            'L' => {
                self.at += 1;
                self.ty_summary()?;
                // A constant value, terminated by an underscore.
                while !self.eat('_') && !self.rest().is_empty() {
                    self.at += 1;
                }
                Ok(())
            }
            'K' => {
                self.at += 1;
                self.skip_generic()
            }
            _ => {
                self.ty_summary()?;
                Ok(())
            }
        }
    }
}

fn basic_type(c: char) -> Option<&'static str> {
    Some(match c {
        'a' => "i8",
        'b' => "bool",
        'c' => "char",
        'd' => "f64",
        'e' => "str",
        'f' => "f32",
        'h' => "u8",
        'i' => "isize",
        'j' => "usize",
        'l' => "i32",
        'm' => "u32",
        'n' => "i128",
        'o' => "u128",
        's' => "i16",
        't' => "u16",
        'u' => "()",
        'v' => "...",
        'x' => "i64",
        'y' => "u64",
        'z' => "!",
        'p' => "_",
        _ => return None,
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn the_legacy_scheme_drops_the_hash() {
        assert_eq!(
            demangle_legacy("_ZN4core3fmt9Formatter3pad17h0123456789abcdefE").as_deref(),
            Some("core::fmt::Formatter::pad")
        );
    }

    #[test]
    fn a_name_without_the_hash_is_not_a_rust_name() {
        // Plain C++ must not be claimed by the Rust path.
        assert_eq!(demangle_legacy("_ZN3foo3barEv"), None);
    }

    #[test]
    fn v0_paths_render() {
        // A crate root, then a nested value.
        assert_eq!(demangle_v0("_RNvC4main3foo").as_deref(), Some("main::foo"));
    }

    #[test]
    fn v0_refuses_what_it_cannot_read() {
        assert_eq!(demangle_v0("_R"), None);
        assert_eq!(demangle_v0("not mangled"), None);
    }

    #[test]
    fn nothing_hangs_or_panics() {
        for n in 0..200usize {
            let s: String = std::iter::repeat_n('N', n).collect();
            let _ = demangle_v0(&format!("_R{s}"));
            let t: String = std::iter::repeat_n('I', n).collect();
            let _ = demangle_v0(&format!("_R{t}C4main"));
        }
        let _ = demangle_legacy("_ZN17h0123456789abcdefE");
    }
}
