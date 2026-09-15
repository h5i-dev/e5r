//! The SLEIGH token scanner.
//!
//! Two things make this more than a loop over an operator table.
//!
//! First, the display section of a constructor is a different sublanguage:
//! between the header `:` and the keyword `is`, punctuation is literal text
//! and `#` does not start a comment. The scanner therefore exposes
//! [`Lexer::display_section`], which the parser calls when it knows it is in
//! one, rather than trying to guess from the token stream.
//!
//! Second, several operators begin with a letter (`s<`, `s>>`, `f+`, `f==`).
//! An identifier scan would swallow them, so a bare `s` or `f` immediately
//! followed by an operator character is re-read as the operator. Adjacency is
//! required, which is the same rule the language itself relies on: `f - 1`
//! subtracts from a register named `f`, `f- 1` is a floating point negation.
//!
//! Reference: the SLEIGH manual, "2. Basic Specification Layout" and
//! "9. P-code Tables".

use crate::error::{Error, Result};

/// One lexical token.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Tok {
    /// A name: letters, digits, `_` and `.`, not starting with a digit.
    Ident(String),
    /// An integer literal, decimal, `0x` hexadecimal or `0b` binary.
    Num(u64),
    /// A double quoted string, with the quotes removed.
    Str(String),
    /// An operator or a delimiter, as one of a fixed set of spellings.
    Op(&'static str),
    /// The end of the input.
    Eof,
}

impl std::fmt::Display for Tok {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Tok::Ident(s) => write!(f, "{s}"),
            Tok::Num(n) => write!(f, "{n}"),
            Tok::Str(s) => write!(f, "{s:?}"),
            Tok::Op(o) => write!(f, "{o}"),
            Tok::Eof => f.write_str("end of file"),
        }
    }
}

/// Every operator spelling, longest first so that a prefix never wins over the
/// operator that contains it (`s>>` before `s>`, `<=` before `<`).
const OPS: &[&str] = &[
    "...", "s>>", "s<=", "s>=", "f<=", "f>=", "f==", "f!=", "$and", "$xor", "$or", "<<", ">>",
    "==", "!=", "<=", ">=", "&&", "||", "^^", "s<", "s>", "s/", "s%", "f<", "f>", "f+", "f-", "f*",
    "f/", "+", "-", "*", "/", "%", "&", "|", "^", "~", "!", "=", "<", ">", "(", ")", "[", "]", "{",
    "}", ",", ";", ":",
];

/// The operator spellings that may follow a bare `s`.
const S_OPS: &[&str] = &["s>>", "s<=", "s>=", "s<", "s>", "s/", "s%"];
/// The operator spellings that may follow a bare `f`.
const F_OPS: &[&str] = &[
    "f<=", "f>=", "f==", "f!=", "f<", "f>", "f+", "f-", "f*", "f/",
];

/// A token together with where it started.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Spanned {
    /// The token.
    pub tok: Tok,
    /// Byte offset of its first character in the preprocessed text.
    pub offset: usize,
}

/// A scanner over preprocessed specification text.
#[derive(Debug, Clone)]
pub struct Lexer<'a> {
    text: &'a str,
    pos: usize,
}

impl<'a> Lexer<'a> {
    /// A scanner positioned at the start of `text`.
    pub fn new(text: &'a str) -> Lexer<'a> {
        Lexer { text, pos: 0 }
    }

    /// The current byte offset.
    pub fn offset(&self) -> usize {
        self.pos
    }

    /// Move back to a previously recorded offset. Used by the parser to undo a
    /// lookahead before switching into display mode.
    pub fn seek(&mut self, offset: usize) {
        self.pos = offset.min(self.text.len());
    }

    /// The next token, consuming it.
    pub fn next_token(&mut self) -> Result<Spanned> {
        self.skip_trivia();
        let offset = self.pos;
        let bytes = self.text.as_bytes();
        if self.pos >= bytes.len() {
            return Ok(Spanned {
                tok: Tok::Eof,
                offset,
            });
        }
        let c = bytes[self.pos];

        if c == b'"' {
            let value = self.string()?;
            return Ok(Spanned {
                tok: Tok::Str(value),
                offset,
            });
        }
        if c.is_ascii_digit() {
            let value = self.number()?;
            return Ok(Spanned {
                tok: Tok::Num(value),
                offset,
            });
        }
        // `...` before identifiers, because a name may start with `.` and
        // the ellipsis would otherwise be read as one.
        if self.text[self.pos..].starts_with("...") {
            self.pos += 3;
            return Ok(Spanned {
                tok: Tok::Op("..."),
                offset,
            });
        }
        if is_ident_start(c) {
            let start = self.pos;
            while self.pos < bytes.len() && is_ident_byte(bytes[self.pos]) {
                self.pos += 1;
            }
            let word = &self.text[start..self.pos];
            // `s` and `f` are operator prefixes when glued to their operand.
            let table = match word {
                "s" => S_OPS,
                "f" => F_OPS,
                _ => &[],
            };
            if let Some(op) = table.iter().find(|op| self.text[start..].starts_with(**op)) {
                self.pos = start + op.len();
                return Ok(Spanned {
                    tok: Tok::Op(op),
                    offset,
                });
            }
            return Ok(Spanned {
                tok: Tok::Ident(word.to_string()),
                offset,
            });
        }
        if let Some(op) = OPS
            .iter()
            .find(|op| self.text[self.pos..].starts_with(**op))
        {
            self.pos += op.len();
            return Ok(Spanned {
                tok: Tok::Op(op),
                offset,
            });
        }
        // Always advance: an unknown byte must not leave the caller looping.
        self.pos += 1;
        Err(Error::new(format!(
            "{:?} does not belong in a specification",
            c as char
        )))
    }

    /// Read the display section of a constructor: every character from here up
    /// to the keyword `is`, which is consumed. The text comes back raw,
    /// quotes included, for [`crate::model::Display`] to interpret.
    pub fn display_section(&mut self) -> Result<String> {
        let bytes = self.text.as_bytes();
        let mut out = String::new();
        while self.pos < bytes.len() {
            let c = bytes[self.pos];
            if c == b'"' {
                let start = self.pos;
                self.pos += 1;
                while self.pos < bytes.len() && bytes[self.pos] != b'"' {
                    if bytes[self.pos] == b'\n' {
                        return Err(Error::new("a string in a display section crosses a line"));
                    }
                    self.pos += 1;
                }
                if self.pos >= bytes.len() {
                    return Err(Error::new("a string in a display section is never closed"));
                }
                self.pos += 1;
                out.push_str(&self.text[start..self.pos]);
                continue;
            }
            if is_ident_start(c) {
                let start = self.pos;
                while self.pos < bytes.len() && is_ident_byte(bytes[self.pos]) {
                    self.pos += 1;
                }
                let word = &self.text[start..self.pos];
                if word == "is" {
                    return Ok(out);
                }
                out.push_str(word);
                continue;
            }
            out.push(c as char);
            self.pos += 1;
        }
        Err(Error::new(
            "a display section runs to the end of the file without an `is`",
        ))
    }

    fn skip_trivia(&mut self) {
        let bytes = self.text.as_bytes();
        loop {
            while self.pos < bytes.len() && bytes[self.pos].is_ascii_whitespace() {
                self.pos += 1;
            }
            if self.pos < bytes.len() && bytes[self.pos] == b'#' {
                while self.pos < bytes.len() && bytes[self.pos] != b'\n' {
                    self.pos += 1;
                }
                continue;
            }
            return;
        }
    }

    fn string(&mut self) -> Result<String> {
        let bytes = self.text.as_bytes();
        self.pos += 1;
        let start = self.pos;
        while self.pos < bytes.len() && bytes[self.pos] != b'"' {
            if bytes[self.pos] == b'\n' {
                return Err(Error::new("a string crosses a line"));
            }
            self.pos += 1;
        }
        if self.pos >= bytes.len() {
            return Err(Error::new("a string is never closed"));
        }
        let value = self.text[start..self.pos].to_string();
        self.pos += 1;
        Ok(value)
    }

    fn number(&mut self) -> Result<u64> {
        let bytes = self.text.as_bytes();
        let start = self.pos;
        let (radix, skip) =
            if self.text[start..].starts_with("0x") || self.text[start..].starts_with("0X") {
                (16, 2)
            } else if self.text[start..].starts_with("0b") || self.text[start..].starts_with("0B") {
                (2, 2)
            } else {
                (10, 0)
            };
        self.pos += skip;
        let digits = self.pos;
        while self.pos < bytes.len() && (bytes[self.pos] as char).is_digit(radix) {
            self.pos += 1;
        }
        if self.pos == digits {
            // `0b` with nothing after it: back off and read the leading zero so
            // the scanner still advances and the parser sees a number.
            self.pos = start + 1;
            return Ok(0);
        }
        // A suffix of identifier characters means this was never a number.
        if self.pos < bytes.len() && is_ident_byte(bytes[self.pos]) && radix != 16 {
            return Err(Error::new(format!(
                "{:?} is not a number",
                &self.text[start..(self.pos + 1).min(bytes.len())]
            )));
        }
        u64::from_str_radix(&self.text[digits..self.pos], radix).map_err(|_| {
            Error::new(format!(
                "{} does not fit in 64 bits",
                &self.text[start..self.pos]
            ))
        })
    }
}

fn is_ident_start(b: u8) -> bool {
    b.is_ascii_alphabetic() || b == b'_' || b == b'.'
}

fn is_ident_byte(b: u8) -> bool {
    b.is_ascii_alphanumeric() || b == b'_' || b == b'.'
}

#[cfg(test)]
mod tests {
    use super::*;

    fn toks(text: &str) -> Vec<Tok> {
        let mut lex = Lexer::new(text);
        let mut out = Vec::new();
        loop {
            let t = lex.next_token().expect("lexes");
            if t.tok == Tok::Eof {
                return out;
            }
            out.push(t.tok);
        }
    }

    #[test]
    fn numbers_come_in_three_bases() {
        assert_eq!(
            toks("1006789 0xF5CC5 0b1011"),
            vec![Tok::Num(1006789), Tok::Num(0xF5CC5), Tok::Num(0b1011)]
        );
    }

    #[test]
    fn an_ellipsis_is_an_operator_not_a_name() {
        assert_eq!(
            toks("(a=1) ... & b"),
            vec![
                Tok::Op("("),
                Tok::Ident("a".into()),
                Tok::Op("="),
                Tok::Num(1),
                Tok::Op(")"),
                Tok::Op("..."),
                Tok::Op("&"),
                Tok::Ident("b".into()),
            ]
        );
    }

    #[test]
    fn identifiers_take_dots_and_underscores() {
        assert_eq!(
            toks("gcr_el1.exclude"),
            vec![Tok::Ident("gcr_el1.exclude".into())]
        );
        // PIC names a register `.STKPTR`, so a leading dot has to be a name
        // even though `...` is an operator.
        assert_eq!(toks(".STKPTR"), vec![Tok::Ident(".STKPTR".into())]);
    }

    #[test]
    fn letter_operators_are_not_identifiers() {
        assert_eq!(
            toks("a s>> b"),
            vec![
                Tok::Ident("a".into()),
                Tok::Op("s>>"),
                Tok::Ident("b".into())
            ]
        );
        assert_eq!(
            toks("x f< y"),
            vec![
                Tok::Ident("x".into()),
                Tok::Op("f<"),
                Tok::Ident("y".into())
            ]
        );
    }

    #[test]
    fn a_register_named_f_still_lexes_when_spaced() {
        assert_eq!(
            toks("f - 1"),
            vec![Tok::Ident("f".into()), Tok::Op("-"), Tok::Num(1)]
        );
    }

    #[test]
    fn comments_run_to_the_end_of_the_line() {
        assert_eq!(
            toks("a # b c\nd"),
            vec![Tok::Ident("a".into()), Tok::Ident("d".into())]
        );
    }

    #[test]
    fn a_display_section_stops_at_is() {
        let mut lex = Lexer::new(" ( op1 ),op2 is opcode=1");
        let d = lex.display_section().expect("reads");
        assert_eq!(d, " ( op1 ),op2 ");
        assert_eq!(
            lex.next_token().expect("lexes").tok,
            Tok::Ident("opcode".into())
        );
    }

    #[test]
    fn a_display_section_keeps_hash_and_quotes() {
        let mut lex = Lexer::new("SHL wreg, \"#\"immed8 is op8=9");
        assert_eq!(
            lex.display_section().expect("reads"),
            "SHL wreg, \"#\"immed8 "
        );
    }

    #[test]
    fn an_unterminated_display_section_is_an_error_not_a_hang() {
        let mut lex = Lexer::new(":no keyword here");
        assert!(lex.display_section().is_err());
    }

    #[test]
    fn an_oversized_number_is_refused() {
        let mut lex = Lexer::new("0xffffffffffffffffff");
        assert!(lex.next_token().is_err());
    }
}
