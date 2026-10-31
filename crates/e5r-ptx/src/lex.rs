//! PTX tokens. Comments and whitespace are dropped; everything else is kept,
//! so two texts with the same token sequence say the same thing to `ptxas`
//! (the round trip relies on this).

/// One token.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Tok {
    /// Identifier, directive, opcode or register: `[A-Za-z_$%.][A-Za-z0-9_$%.]*`.
    Word(String),
    /// An integer literal, by value (`0x10` and `16` are the same token).
    Int(i128),
    /// A numeric literal that is not an integer, as written (`9.2`).
    Num(String),
    /// Punctuation.
    Punct(char),
}

/// A token and its 1-based line.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Token {
    /// The token.
    pub tok: Tok,
    /// Line number in the source.
    pub line: usize,
}

fn word_start(c: char) -> bool {
    c.is_ascii_alphabetic() || matches!(c, '_' | '$' | '%' | '.')
}

fn word_char(c: char) -> bool {
    c.is_ascii_alphanumeric() || matches!(c, '_' | '$' | '%' | '.')
}

/// Integer literal value: decimal, `0x` hex, optional `U` suffix.
pub fn int_value(s: &str) -> Option<i128> {
    let s = s.strip_suffix('U').unwrap_or(s);
    if let Some(h) = s.strip_prefix("0x").or_else(|| s.strip_prefix("0X")) {
        return i128::from_str_radix(h, 16).ok();
    }
    if s.len() > 1 && s.starts_with('0') {
        // Octal in PTX; not part of the subset.
        return None;
    }
    s.parse().ok()
}

/// Split `src` into tokens.
pub fn lex(src: &str) -> Result<Vec<Token>, String> {
    let chars: Vec<char> = src.chars().collect();
    let mut out = Vec::new();
    let mut i = 0;
    let mut line = 1;
    while i < chars.len() {
        let c = chars[i];
        if c == '\n' {
            line += 1;
            i += 1;
        } else if c.is_whitespace() {
            i += 1;
        } else if c == '/' && chars.get(i + 1) == Some(&'/') {
            while i < chars.len() && chars[i] != '\n' {
                i += 1;
            }
        } else if c == '/' && chars.get(i + 1) == Some(&'*') {
            let start = line;
            i += 2;
            loop {
                match chars.get(i) {
                    None => return Err(format!("line {start}: unterminated comment")),
                    Some('*') if chars.get(i + 1) == Some(&'/') => {
                        i += 2;
                        break;
                    }
                    Some('\n') => line += 1,
                    _ => {}
                }
                i += 1;
            }
        } else if word_start(c) {
            let s = i;
            while i < chars.len() && word_char(chars[i]) {
                i += 1;
            }
            out.push(Token {
                tok: Tok::Word(chars[s..i].iter().collect()),
                line,
            });
        } else if c.is_ascii_digit() {
            let s = i;
            while i < chars.len() && (chars[i].is_ascii_alphanumeric() || chars[i] == '.') {
                i += 1;
            }
            let text: String = chars[s..i].iter().collect();
            let tok = match int_value(&text) {
                Some(v) => Tok::Int(v),
                None => Tok::Num(text),
            };
            out.push(Token { tok, line });
        } else if "{}()[]<>,;:@!+-".contains(c) {
            out.push(Token {
                tok: Tok::Punct(c),
                line,
            });
            i += 1;
        } else {
            return Err(format!("line {line}: unexpected character {c:?}"));
        }
    }
    Ok(out)
}
