//! A tokenizer both architectures share.
//!
//! The text this has to accept is whatever `r12e disas` prints, so the rules
//! are set by the two printers in `r12e-arch` rather than by any assembler's
//! grammar: tabs separate the mnemonic from its operands, `#` introduces an
//! AArch64 immediate, and a mnemonic may contain a dot (`b.eq`).

use crate::error::{AsmError, MAX_TEXT, MAX_TOKENS};

/// One token, borrowed from the input.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Tok<'a> {
    /// A bare word: a mnemonic, a register, a condition, a size keyword.
    Ident(&'a str),
    /// An unsigned magnitude. A leading `-` arrives as its own punctuation
    /// token, because `[rax - 0x1]` spells the sign as an operator.
    Num(u64),
    /// A single punctuation character.
    Punct(u8),
}

/// A token and where it started, for the error message.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Spanned<'a> {
    /// The token.
    pub tok: Tok<'a>,
    /// Byte offset of its first character.
    pub at: usize,
}

fn ident_start(b: u8) -> bool {
    b.is_ascii_alphabetic() || b == b'_' || b == b'.' || b == b'%'
}

fn ident_body(b: u8) -> bool {
    b.is_ascii_alphanumeric() || b == b'_' || b == b'.'
}

/// Split `text` into tokens.
///
/// Both bounds are checked before the vector is reserved, so a hostile string
/// cannot make this allocate more than a fixed amount.
pub fn lex(text: &str) -> Result<Vec<Spanned<'_>>, AsmError> {
    if text.len() > MAX_TEXT {
        return Err(AsmError::TooLong {
            what: "instruction text length",
            len: text.len(),
            limit: MAX_TEXT,
        });
    }
    let b = text.as_bytes();
    let mut out: Vec<Spanned<'_>> = Vec::new();
    let mut i = 0usize;
    while i < b.len() {
        let c = b[i];
        if c.is_ascii_whitespace() {
            i += 1;
            continue;
        }
        // A comment runs to the end of the line; both objdumps put the
        // resolved target and the symbol name there, and a user pasting a
        // line should not have to strip them. `#` is the awkward one, since
        // it also introduces every AArch64 immediate: a comment `#` is the
        // one with no digit behind it.
        let comment = c == b';'
            || c == b'<'
            || (c == b'/' && b.get(i + 1) == Some(&b'/'))
            || (c == b'#'
                && !matches!(b.get(i + 1), Some(d) if d.is_ascii_digit() || *d == b'-' || *d == b'+'));
        if comment {
            break;
        }
        if out.len() >= MAX_TOKENS {
            return Err(AsmError::TooLong {
                what: "token count",
                len: out.len() + 1,
                limit: MAX_TOKENS,
            });
        }
        let at = i;
        let tok = if c.is_ascii_digit() {
            let (v, next) = number(b, i)?;
            i = next;
            Tok::Num(v)
        } else if ident_start(c) {
            let start = i;
            i += 1;
            while i < b.len() && ident_body(b[i]) {
                i += 1;
            }
            // A trailing dot belongs to the next token, not to this word.
            let mut end = i;
            while end > start + 1 && b[end - 1] == b'.' {
                end -= 1;
                i = end;
            }
            Tok::Ident(&text[start..end])
        } else {
            i += 1;
            Tok::Punct(c)
        };
        out.push(Spanned { tok, at });
    }
    Ok(out)
}

/// Read one unsigned number. Hex with `0x`, otherwise decimal.
///
/// The digit count is bounded by the field width, so no number in the text can
/// make this loop longer than seventy times.
fn number(b: &[u8], start: usize) -> Result<(u64, usize), AsmError> {
    let mut i = start;
    let (radix, mut i0) = if b[i] == b'0' && matches!(b.get(i + 1), Some(b'x' | b'X')) {
        (16u32, i + 2)
    } else {
        (10u32, i)
    };
    if i0 >= b.len() || !(b[i0] as char).is_digit(radix) {
        return Err(AsmError::Syntax {
            at: start,
            what: "a number with no digits".to_string(),
        });
    }
    let mut v: u64 = 0;
    let mut digits = 0usize;
    while i0 < b.len() {
        let d = match (b[i0] as char).to_digit(radix) {
            Some(d) => d,
            None => break,
        };
        digits += 1;
        // 64 bits of binary is the widest field any operand has; anything
        // longer is a typo, and stopping here keeps the loop bounded.
        if digits > 24 {
            return Err(AsmError::Syntax {
                at: start,
                what: "a number with more digits than a 64-bit field holds".to_string(),
            });
        }
        v = v.wrapping_mul(radix as u64).wrapping_add(d as u64);
        i0 += 1;
    }
    i = i0;
    // A number cannot run straight into a word: `0x10foo` is a typo, and
    // accepting it would quietly assemble something the user did not write.
    if i < b.len() && ident_body(b[i]) {
        return Err(AsmError::Syntax {
            at: start,
            what: "a number followed by a letter".to_string(),
        });
    }
    Ok((v, i))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn tabs_and_commas_separate() {
        let t = lex("mov\trax, rcx").unwrap();
        assert_eq!(t.len(), 4);
        assert_eq!(t[0].tok, Tok::Ident("mov"));
        assert_eq!(t[2].tok, Tok::Punct(b','));
    }

    #[test]
    fn a_dotted_mnemonic_stays_one_word() {
        let t = lex("b.eq\t0x1000").unwrap();
        assert_eq!(t[0].tok, Tok::Ident("b.eq"));
        assert_eq!(t[1].tok, Tok::Num(0x1000));
    }

    #[test]
    fn hex_and_decimal_both_read() {
        assert_eq!(lex("#0x10").unwrap()[1].tok, Tok::Num(16));
        assert_eq!(lex("#16").unwrap()[1].tok, Tok::Num(16));
    }

    #[test]
    fn a_number_running_into_a_word_is_refused() {
        assert!(lex("0x10foo").is_err());
    }

    #[test]
    fn the_text_length_is_bounded() {
        let long = "a".repeat(MAX_TEXT + 1);
        assert!(matches!(lex(&long), Err(AsmError::TooLong { .. })));
    }
}
