//! Reading C declarations into the type model.
//!
//! An analyst who can see that a function takes two bytes has to be able to
//! say so, and the only notation everybody already knows is C. This is the
//! other direction of `ctype::Types::declare`: text in, types out, so an
//! assertion is an input to the analysis rather than a note beside it.
//!
//! ```text
//! int arith8(unsigned char a, unsigned char b)
//! struct header { uint32_t magic; uint16_t len; char name[16]; };
//! typedef struct node { struct node *next; int value; } node_t;
//! void *(*handler)(int, char **)
//! union v { uint64_t bits; double d; };
//! enum kind { A = 1, B, C = 10 };
//! ```
//!
//! It is a parser and not a compiler. Two things follow, and both are chosen
//! rather than fallen into:
//!
//! 1. **It does not preprocess.** A conditional is not evaluated, so a
//!    declaration inside a false `#if` is still read and a header that
//!    contradicts itself across the arms of one says so as a refusal. The one
//!    directive it does read is an object-like `#define` with a constant body,
//!    because `char e_ident[EI_NIDENT]` is unreadable without it and the value
//!    is written in the file rather than guessed at. Feeding it `cc -E` output
//!    is the way to get a header read exactly; what it does with a raw header
//!    is a best effort that says what it skipped.
//! 2. **It refuses rather than guesses.** An unknown type name, an attribute
//!    that changes a layout, a construct it does not implement: each one comes
//!    back as an error naming what was not understood. A structure laid out
//!    with the wrong rule is worse than no structure, because the reader will
//!    believe the offsets.
//!
//! Sizes and alignments come from the store's [`Model`], because `long` is
//! four bytes on Windows and eight on Linux and a declaration read for one
//! target must not be laid out with the other's rules.

use std::collections::BTreeMap;
use std::fmt;

use crate::ctype::{
    Composite, Enumeration, Field, Model, Qualifiers, Signature, Type, TypeId, Types,
};

/// How deep declarators, expressions and nested structures may go before the
/// parser gives up. Hostile input is otherwise a stack overflow.
const MAX_DEPTH: u32 = 64;

/// What the parser refused, and where.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ParseError {
    /// What it did not understand, in words that name the construct.
    pub message: String,
    /// Byte offset into the text.
    pub offset: usize,
    /// One-based line.
    pub line: usize,
    /// One-based column, counted in characters.
    pub column: usize,
}

impl ParseError {
    fn at(text: &str, offset: usize, message: impl Into<String>) -> ParseError {
        // An offset can come from a macro body rather than from this text, so
        // it is clamped to a boundary here rather than trusted.
        let mut offset = offset.min(text.len());
        while offset > 0 && !text.is_char_boundary(offset) {
            offset -= 1;
        }
        let before = &text[..offset];
        let line = before.matches('\n').count() + 1;
        let column = before
            .rsplit('\n')
            .next()
            .map_or(1, |l| l.chars().count() + 1);
        ParseError {
            message: message.into(),
            offset,
            line,
            column,
        }
    }
}

impl fmt::Display for ParseError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "line {} column {}: {}",
            self.line, self.column, self.message
        )
    }
}

impl std::error::Error for ParseError {}

/// One declaration a translation unit contained.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Declaration {
    /// The declared name. Absent for a bare `struct s { ... };`, which
    /// declares a type and no object.
    pub name: Option<String>,
    /// The type. For a `typedef` this is the [`Type::Typedef`] itself, so the
    /// name it introduced survives into output.
    pub ty: TypeId,
    /// True when the declaration was a `typedef`.
    pub typedef: bool,
    /// True when it said `extern` or `static`, which the type model has no
    /// room for but a caller deciding whether to emit it wants to know.
    pub storage: Option<Storage>,
}

/// The storage class a declaration named.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Storage {
    /// `typedef`, which C spells as a storage class and is not one.
    Typedef,
    /// `extern`.
    Extern,
    /// `static`.
    Static,
    /// `auto` or `register`, which say nothing a reader needs.
    Automatic,
}

/// What reading a whole header produced, including what it would not read.
#[derive(Debug, Clone, Default)]
pub struct Unit {
    /// The declarations that were understood, in source order.
    pub declarations: Vec<Declaration>,
    /// Every declaration that was refused, with the reason.
    pub refused: Vec<ParseError>,
}

impl Unit {
    /// How many declarations were attempted.
    pub fn attempted(&self) -> usize {
        self.declarations.len() + self.refused.len()
    }
}

/// Parse exactly one declaration.
///
/// The trailing semicolon is optional, because an analyst typing a prototype
/// on a command line does not write one.
pub fn declaration(types: &mut Types, text: &str) -> Result<Declaration, ParseError> {
    let mut p = Parser::new(types, text)?;
    let mut out = p.declaration()?;
    p.eat_punct(";");
    if let Some(t) = p.peek_offset() {
        return Err(p.error(t, "one declaration was expected and the text holds more"));
    }
    if out.len() > 1 {
        return Err(p.error(
            0,
            "this declares more than one name; declare them one at a time",
        ));
    }
    Ok(out
        .pop()
        .expect("a declaration always yields at least one entry"))
}

/// Parse a sequence of declarations, refusing the whole text on the first one
/// that is not understood.
pub fn translation_unit(types: &mut Types, text: &str) -> Result<Vec<Declaration>, ParseError> {
    let mut p = Parser::new(types, text)?;
    let mut out = Vec::new();
    while p.peek_offset().is_some() {
        if p.eat_punct(";") {
            continue;
        }
        p.depth = 0;
        out.append(&mut p.declaration()?);
        if !p.eat_punct(";") && p.peek_offset().is_some() {
            let at = p.peek_offset().unwrap_or_default();
            return Err(p.error(at, "expected `;` after a declaration"));
        }
    }
    Ok(out)
}

/// Read as much of a header as is understood, and say what was not.
///
/// The recovering form of [`translation_unit`]. A real header holds
/// declarations this parser has no business reading, and stopping at the first
/// one would make it useless for the job it exists for: pulling a known API's
/// types out of a header somebody else wrote.
pub fn header(types: &mut Types, text: &str) -> Unit {
    let mut unit = Unit::default();
    let mut p = match Parser::new(types, text) {
        Ok(p) => p,
        Err(e) => {
            unit.refused.push(e);
            return unit;
        }
    };
    while p.peek_offset().is_some() {
        if p.eat_punct(";") {
            continue;
        }
        let start = p.at;
        p.depth = 0;
        match p.declaration() {
            Ok(mut d) => {
                unit.declarations.append(&mut d);
                if !p.eat_punct(";") && p.peek_offset().is_some() {
                    let at = p.peek_offset().unwrap_or_default();
                    unit.refused
                        .push(p.error(at, "expected `;` after a declaration"));
                    p.recover();
                }
            }
            Err(e) => {
                unit.refused.push(e);
                p.recover();
            }
        }
        // A declaration that consumed nothing would spin forever; the recovery
        // above normally moves, this is the guarantee that it always does.
        if p.at == start {
            p.at += 1;
        }
    }
    unit
}

/// Parse a type name: specifiers and an abstract declarator, with no name.
///
/// What a cast is written with, and what an analyst types when the thing being
/// described is a data object rather than a function: `struct header *`,
/// `uint32_t [16]`, `void (*)(int)`.
pub fn type_name(types: &mut Types, text: &str) -> Result<TypeId, ParseError> {
    let mut p = Parser::new(types, text)?;
    let at = p.here();
    let specs = p.specifiers()?;
    let base = p.base_type(&specs, at)?;
    if specs.storage.is_some() {
        return Err(p.error(at, "a type name has no storage class"));
    }
    let d = p.parse_declarator(true)?;
    let (ty, name) = p.apply(&d, base)?;
    if let Some(n) = name {
        return Err(p.error(
            at,
            format!("a type name declares nothing, and this names `{n}`"),
        ));
    }
    p.eat_punct(";");
    if let Some(t) = p.peek_offset() {
        return Err(p.error(t, "one type name was expected and the text holds more"));
    }
    Ok(ty)
}

/// Parse a function declaration, for an asserted prototype.
///
/// Returns the name when the declaration gave one, and the signature. A
/// declaration that is not of a function is refused here rather than silently
/// producing a prototype with no parameters.
pub fn prototype(types: &mut Types, text: &str) -> Result<(Option<String>, Signature), ParseError> {
    let d = declaration(types, text)?;
    let resolved = types.resolve(d.ty);
    // A function pointer is what somebody writes when they mean the function,
    // and reading through one is not a guess about anything.
    let resolved = match types.get(resolved) {
        Some(Type::Pointer(inner)) => types.resolve(*inner),
        _ => resolved,
    };
    match types.get(resolved) {
        Some(Type::Function(sig)) => Ok((d.name, sig.clone())),
        _ => Err(ParseError::at(
            text,
            0,
            format!(
                "this declares {}, not a function; a prototype reads `int f(char *, int)`",
                types.name_of(d.ty)
            ),
        )),
    }
}

/// One piece of a declaration.
#[derive(Debug, Clone, PartialEq, Eq)]
enum Token {
    Word(String),
    Number(i128),
    Text(String),
    Punct(&'static str),
    /// An attribute whose body could change a layout, kept so it is refused
    /// where it appears rather than silently dropped.
    Attribute(String),
}

impl fmt::Display for Token {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Token::Word(w) => write!(f, "`{w}`"),
            Token::Number(n) => write!(f, "`{n}`"),
            Token::Text(t) => write!(f, "a string literal {t:?}"),
            Token::Punct(p) => write!(f, "`{p}`"),
            Token::Attribute(a) => write!(f, "`__attribute__(({a}))`"),
        }
    }
}

/// Punctuators, longest first so `<<` is not two `<`.
const PUNCT: &[&str] = &[
    "...", "<<", ">>", "<=", ">=", "==", "!=", "&&", "||", "(", ")", "[", "]", "{", "}", "*", ",",
    ";", ":", "?", "=", "+", "-", "~", "!", "/", "%", "&", "^", "|", "<", ">", ".",
];

/// Attribute bodies that change a layout or a width. An attribute is otherwise
/// dropped, because most of them say nothing about the type; these are refused
/// because honouring them is not implemented and ignoring them gives wrong
/// offsets.
const LAYOUT_ATTRIBUTES: &[&str] = &[
    "packed",
    "aligned",
    "mode",
    "vector_size",
    "transparent_union",
];

/// The tokens of a text, plus the object-like `#define`s it declared.
struct Lexed {
    tokens: Vec<(Token, usize)>,
    /// `#define NAME body` for the ones with no parameter list. Reading a
    /// header's own constants is not preprocessing: a bound written
    /// `char e_ident[EI_NIDENT]` is unreadable without them, and the value is
    /// in the file rather than guessed.
    macros: BTreeMap<String, String>,
}

fn lex(text: &str) -> Result<Lexed, ParseError> {
    let bytes: Vec<char> = text.chars().collect();
    // Character index to byte offset, so an error points into the real text.
    let mut offsets = Vec::with_capacity(bytes.len() + 1);
    let mut acc = 0;
    for c in &bytes {
        offsets.push(acc);
        acc += c.len_utf8();
    }
    offsets.push(acc);

    let mut out: Vec<(Token, usize)> = Vec::new();
    let mut macros: BTreeMap<String, String> = BTreeMap::new();
    let mut i = 0;
    let mut line_start = true;
    while i < bytes.len() {
        let c = bytes[i];
        if c == '\n' {
            line_start = true;
            i += 1;
            continue;
        }
        if c.is_whitespace() {
            i += 1;
            continue;
        }
        // A backslash at the end of a line joins it to the next one, and the
        // joined line is still the same logical line for `#`.
        if c == '\\' && bytes.get(i + 1) == Some(&'\n') {
            i += 2;
            continue;
        }
        if c == '/' && bytes.get(i + 1) == Some(&'/') {
            while i < bytes.len() && bytes[i] != '\n' {
                i += 1;
            }
            continue;
        }
        if c == '/' && bytes.get(i + 1) == Some(&'*') {
            i += 2;
            while i + 1 < bytes.len() && !(bytes[i] == '*' && bytes[i + 1] == '/') {
                i += 1;
            }
            if i + 1 >= bytes.len() {
                return Err(ParseError::at(
                    text,
                    offsets[i.min(bytes.len())],
                    "a comment was never closed",
                ));
            }
            i += 2;
            continue;
        }
        // Preprocessor directives are skipped, not evaluated. See the module
        // note: this is a parser, and `cc -E` is the preprocessor.
        if c == '#' && line_start {
            // A directive runs to the end of its logical line, and a comment
            // is whitespace that may contain newlines. Skipping to the next
            // newline instead leaves the tail of a two-line comment behind,
            // where it tokenizes as code and takes the next declaration with
            // it.
            let mut line = String::new();
            i += 1;
            while i < bytes.len() {
                if bytes[i] == '\\' && bytes.get(i + 1) == Some(&'\n') {
                    i += 2;
                    line.push(' ');
                    continue;
                }
                if bytes[i] == '/' && bytes.get(i + 1) == Some(&'*') {
                    i += 2;
                    while i + 1 < bytes.len() && !(bytes[i] == '*' && bytes[i + 1] == '/') {
                        i += 1;
                    }
                    i = (i + 2).min(bytes.len());
                    line.push(' ');
                    continue;
                }
                if bytes[i] == '/' && bytes.get(i + 1) == Some(&'/') {
                    while i < bytes.len() && bytes[i] != '\n' {
                        i += 1;
                    }
                    continue;
                }
                if bytes[i] == '\n' {
                    break;
                }
                line.push(bytes[i]);
                i += 1;
            }
            if let Some((name, body)) = object_like_macro(&line) {
                macros.insert(name, body);
            }
            continue;
        }
        line_start = false;
        let start = i;

        if c.is_alphabetic() || c == '_' {
            while i < bytes.len() && (bytes[i].is_alphanumeric() || bytes[i] == '_') {
                i += 1;
            }
            let word: String = bytes[start..i].iter().collect();
            if is_attribute_introducer(&word) {
                // Skip the balanced parentheses that follow, keeping the body
                // only when it is one of the few that change a type.
                let mut j = i;
                while j < bytes.len() && bytes[j].is_whitespace() {
                    j += 1;
                }
                if bytes.get(j) != Some(&'(') {
                    // `asm` or `__inline` without parentheses: nothing to skip.
                    continue;
                }
                let mut depth = 0usize;
                let body_start = j;
                while j < bytes.len() {
                    match bytes[j] {
                        '(' => depth += 1,
                        ')' => {
                            depth -= 1;
                            if depth == 0 {
                                j += 1;
                                break;
                            }
                        }
                        _ => {}
                    }
                    j += 1;
                }
                if depth != 0 {
                    return Err(ParseError::at(
                        text,
                        offsets[start],
                        format!("`{word}` has an unclosed parenthesis"),
                    ));
                }
                let body: String = bytes[body_start..j].iter().collect();
                i = j;
                if LAYOUT_ATTRIBUTES.iter().any(|a| body.contains(a)) {
                    out.push((Token::Attribute(body), offsets[start]));
                }
                continue;
            }
            out.push((Token::Word(word), offsets[start]));
            continue;
        }

        if c.is_ascii_digit() {
            while i < bytes.len()
                && (bytes[i].is_ascii_alphanumeric() || bytes[i] == '_' || bytes[i] == '.')
            {
                i += 1;
            }
            let word: String = bytes[start..i].iter().collect();
            let value = integer(&word).ok_or_else(|| {
                ParseError::at(
                    text,
                    offsets[start],
                    format!("{word:?} is not an integer constant this parser reads"),
                )
            })?;
            out.push((Token::Number(value), offsets[start]));
            continue;
        }

        if c == '\'' {
            let (value, next) = char_literal(&bytes, i).ok_or_else(|| {
                ParseError::at(
                    text,
                    offsets[start],
                    "a character constant was never closed",
                )
            })?;
            i = next;
            out.push((Token::Number(value), offsets[start]));
            continue;
        }

        if c == '"' {
            i += 1;
            let body_start = i;
            while i < bytes.len() && bytes[i] != '"' {
                if bytes[i] == '\\' {
                    i += 1;
                }
                i += 1;
            }
            if i >= bytes.len() {
                return Err(ParseError::at(
                    text,
                    offsets[start],
                    "a string literal was never closed",
                ));
            }
            let body: String = bytes[body_start..i.min(bytes.len())].iter().collect();
            i += 1;
            out.push((Token::Text(body), offsets[start]));
            continue;
        }

        match PUNCT.iter().find(|p| {
            let chars: Vec<char> = p.chars().collect();
            bytes.len() >= i + chars.len() && bytes[i..i + chars.len()] == chars[..]
        }) {
            Some(p) => {
                i += p.chars().count();
                out.push((Token::Punct(p), offsets[start]));
            }
            None => {
                return Err(ParseError::at(
                    text,
                    offsets[start],
                    format!("`{c}` does not belong in a declaration"),
                ));
            }
        }
    }
    Ok(Lexed {
        tokens: out,
        macros,
    })
}

/// `#define NAME body`, where `NAME` takes no parameters and the body is one
/// line. A function-like macro is not a constant and is skipped.
fn object_like_macro(line: &str) -> Option<(String, String)> {
    let rest = line.trim_start().strip_prefix("define")?;
    if !rest.starts_with(char::is_whitespace) {
        return None;
    }
    let rest = rest.trim_start();
    let end = rest
        .find(|c: char| !(c.is_alphanumeric() || c == '_'))
        .unwrap_or(rest.len());
    let (name, body) = rest.split_at(end);
    if name.is_empty() || name.starts_with(|c: char| c.is_ascii_digit()) {
        return None;
    }
    if body.starts_with('(') {
        return None;
    }
    let body = body.replace('\\', " ");
    let body = body.trim();
    (!body.is_empty()).then(|| (name.to_string(), body.to_string()))
}

fn is_attribute_introducer(word: &str) -> bool {
    matches!(
        word,
        "__attribute__" | "__attribute" | "__declspec" | "__asm__" | "__asm" | "asm"
    )
}

/// An integer constant with its C suffixes.
fn integer(word: &str) -> Option<i128> {
    if word.contains('.') {
        return None;
    }
    let cleaned: String = word.chars().filter(|c| *c != '\'').collect();
    let body = cleaned.trim_end_matches(['u', 'U', 'l', 'L', 'z', 'Z']);
    if body.is_empty() {
        return None;
    }
    // An exponent makes it a floating constant, which is not an integer.
    let lower = body.to_ascii_lowercase();
    let (radix, digits) = if let Some(rest) = lower.strip_prefix("0x") {
        (16, rest)
    } else if let Some(rest) = lower.strip_prefix("0b") {
        (2, rest)
    } else if lower.len() > 1 && lower.starts_with('0') {
        (8, &lower[1..])
    } else {
        (10, lower.as_str())
    };
    // Wrapping rather than refusing: `0xffffffffffffffff` is a real constant
    // whose value as written does not fit a signed 64-bit integer.
    u128::from_str_radix(digits, radix)
        .ok()
        .map(|v| v as i128)
        .or_else(|| i128::from_str_radix(digits, radix).ok())
}

/// A character constant, returning its value and the index past it.
fn char_literal(bytes: &[char], mut i: usize) -> Option<(i128, usize)> {
    i += 1;
    let mut value: i128 = 0;
    let mut any = false;
    while i < bytes.len() && bytes[i] != '\'' {
        let c = if bytes[i] == '\\' {
            i += 1;
            let e = *bytes.get(i)?;
            i += 1;
            match e {
                'n' => 10,
                't' => 9,
                'r' => 13,
                '0' => 0,
                'a' => 7,
                'b' => 8,
                'f' => 12,
                'v' => 11,
                '\\' => 92,
                '\'' => 39,
                '"' => 34,
                'x' => {
                    let start = i;
                    while i < bytes.len() && bytes[i].is_ascii_hexdigit() {
                        i += 1;
                    }
                    let hex: String = bytes[start..i].iter().collect();
                    i128::from_str_radix(&hex, 16).ok()?
                }
                other => other as i128,
            }
        } else {
            let c = bytes[i] as i128;
            i += 1;
            c
        };
        // A multi-character constant packs the bytes, which is what the
        // four-letter tags in a file format header are written as.
        value = (value << 8) | (c & 0xff);
        any = true;
    }
    if i >= bytes.len() || !any {
        return None;
    }
    Some((value, i + 1))
}

struct Parser<'a> {
    tokens: Vec<(Token, usize)>,
    at: usize,
    text: &'a str,
    types: &'a mut Types,
    /// Enumerators in scope, so `enum { A, B = A + 1 }` evaluates.
    enumerators: BTreeMap<String, i128>,
    /// Object-like `#define`s the text declared.
    macros: BTreeMap<String, String>,
    /// Macros being expanded, so one that names itself stops.
    expanding: std::collections::BTreeSet<String>,
    depth: u32,
}

impl<'a> Parser<'a> {
    fn new(types: &'a mut Types, text: &'a str) -> Result<Parser<'a>, ParseError> {
        let lexed = lex(text)?;
        Ok(Parser {
            tokens: lexed.tokens,
            at: 0,
            text,
            types,
            enumerators: BTreeMap::new(),
            macros: lexed.macros,
            expanding: std::collections::BTreeSet::new(),
            depth: 0,
        })
    }

    /// The value of an object-like `#define`, when it is an integer constant.
    fn macro_value(&mut self, name: &str) -> Option<i128> {
        if !self.macros.contains_key(name) || !self.expanding.insert(name.to_string()) {
            return None;
        }
        let body = self.macros[name].clone();
        let value = match lex(&body) {
            Ok(lexed) => {
                let saved_tokens = std::mem::replace(&mut self.tokens, lexed.tokens);
                let saved_at = std::mem::replace(&mut self.at, 0);
                let v = self
                    .conditional(0)
                    .ok()
                    .filter(|_| self.at >= self.tokens.len());
                self.tokens = saved_tokens;
                self.at = saved_at;
                v
            }
            Err(_) => None,
        };
        self.expanding.remove(name);
        value
    }

    fn error(&self, offset: usize, message: impl Into<String>) -> ParseError {
        ParseError::at(self.text, offset, message)
    }

    /// The offset an error at the current position should point at.
    fn here(&self) -> usize {
        self.tokens
            .get(self.at)
            .map(|(_, o)| *o)
            .unwrap_or(self.text.len())
    }

    fn peek(&self) -> Option<&Token> {
        self.tokens.get(self.at).map(|(t, _)| t)
    }

    fn peek_at(&self, n: usize) -> Option<&Token> {
        self.tokens.get(self.at + n).map(|(t, _)| t)
    }

    fn peek_offset(&self) -> Option<usize> {
        self.tokens.get(self.at).map(|(_, o)| *o)
    }

    fn bump(&mut self) -> Option<Token> {
        let t = self.tokens.get(self.at).map(|(t, _)| t.clone());
        if t.is_some() {
            self.at += 1;
        }
        t
    }

    fn eat_punct(&mut self, p: &str) -> bool {
        if matches!(self.peek(), Some(Token::Punct(q)) if *q == p) {
            self.at += 1;
            return true;
        }
        false
    }

    fn expect_punct(&mut self, p: &str, why: &str) -> Result<(), ParseError> {
        if self.eat_punct(p) {
            return Ok(());
        }
        let at = self.here();
        let found = match self.peek() {
            Some(t) => format!("{t}"),
            None => "the end of the text".to_string(),
        };
        Err(self.error(at, format!("expected `{p}` {why}, found {found}")))
    }

    fn eat_word(&mut self, w: &str) -> bool {
        if matches!(self.peek(), Some(Token::Word(x)) if x == w) {
            self.at += 1;
            return true;
        }
        false
    }

    /// Skip to just past the next `;` outside braces, so one bad declaration
    /// does not cost the rest of a header.
    fn recover(&mut self) {
        let mut depth = 0i32;
        while let Some(t) = self.peek().cloned() {
            self.at += 1;
            match t {
                Token::Punct("{") => depth += 1,
                Token::Punct("}") => {
                    depth -= 1;
                    if depth <= 0 {
                        // A `}` may be followed by a declarator and a `;`.
                        while let Some(t) = self.peek().cloned() {
                            self.at += 1;
                            if t == Token::Punct(";") {
                                return;
                            }
                            if t == Token::Punct("{") || t == Token::Punct("}") {
                                self.at -= 1;
                                return;
                            }
                        }
                        return;
                    }
                }
                Token::Punct(";") if depth <= 0 => return,
                _ => {}
            }
        }
    }

    fn guard(&mut self) -> Result<(), ParseError> {
        self.depth += 1;
        if self.depth > MAX_DEPTH {
            return Err(self.error(self.here(), "this declaration nests too deeply to read"));
        }
        Ok(())
    }

    // -- declarations ----------------------------------------------------

    fn declaration(&mut self) -> Result<Vec<Declaration>, ParseError> {
        self.guard()?;
        let start = self.here();
        let specs = self.specifiers()?;
        let base = self.base_type(&specs, start)?;
        let storage = specs.storage;

        // `struct s { ... };` declares a type and nothing else.
        if matches!(self.peek(), Some(Token::Punct(";")) | None) {
            self.depth -= 1;
            if storage == Some(Storage::Typedef) {
                return Err(self.error(start, "a `typedef` with no name declares nothing"));
            }
            return Ok(vec![Declaration {
                name: None,
                ty: base,
                typedef: false,
                storage,
            }]);
        }

        let mut out = Vec::new();
        loop {
            let at = self.here();
            let (ty, name) = self.full_declarator(base)?;
            let Some(name) = name else {
                self.depth -= 1;
                return Err(self.error(at, "this declares a type with no name"));
            };
            // An initializer says nothing about the type, and evaluating one
            // is a compiler's job.
            if self.eat_punct("=") {
                self.skip_initializer()?;
            }
            if storage == Some(Storage::Typedef) {
                let ty = self.define_typedef(&name, ty, at)?;
                out.push(Declaration {
                    name: Some(name),
                    ty,
                    typedef: true,
                    storage,
                });
            } else {
                out.push(Declaration {
                    name: Some(name),
                    ty,
                    typedef: false,
                    storage,
                });
            }
            if !self.eat_punct(",") {
                break;
            }
        }
        self.depth -= 1;
        Ok(out)
    }

    /// Register a typedef, refusing a second one that means something else.
    ///
    /// The store keys named types by name, so a silent second definition would
    /// return the first and the reader would be told the wrong width. Two
    /// identical definitions are ordinary in a header and are not an error.
    fn define_typedef(&mut self, name: &str, ty: TypeId, at: usize) -> Result<TypeId, ParseError> {
        if let Some(existing) = self.types.typedef(name) {
            if let Some(Type::Typedef(_, inner)) = self.types.get(existing) {
                if *inner != ty {
                    return Err(self.error(
                        at,
                        format!(
                            "`{name}` is already `{}` and this makes it `{}`; \
                             the parser does not preprocess, so both arms of a `#if` are read",
                            self.types.name_of(*inner),
                            self.types.name_of(ty)
                        ),
                    ));
                }
            }
            return Ok(existing);
        }
        Ok(self.types.add(Type::Typedef(name.to_string(), ty)))
    }

    fn skip_initializer(&mut self) -> Result<(), ParseError> {
        let mut depth = 0i32;
        while let Some(t) = self.peek().cloned() {
            match t {
                Token::Punct("{") | Token::Punct("(") | Token::Punct("[") => depth += 1,
                Token::Punct("}") | Token::Punct(")") | Token::Punct("]") => depth -= 1,
                Token::Punct(",") | Token::Punct(";") if depth <= 0 => return Ok(()),
                _ => {}
            }
            self.at += 1;
        }
        Ok(())
    }

    // -- declaration specifiers ------------------------------------------

    fn specifiers(&mut self) -> Result<Specs, ParseError> {
        let mut specs = Specs::default();
        loop {
            let at = self.here();
            let Some(Token::Word(w)) = self.peek().cloned() else {
                if let Some(Token::Attribute(a)) = self.peek().cloned() {
                    return Err(self.error(
                        at,
                        format!("`__attribute__(({a}))` changes the layout and is not implemented"),
                    ));
                }
                break;
            };
            match normalize(&w) {
                "typedef" => specs.set_storage(Storage::Typedef),
                "extern" => specs.set_storage(Storage::Extern),
                "static" => specs.set_storage(Storage::Static),
                "auto" | "register" => specs.set_storage(Storage::Automatic),
                "const" => specs.quals.is_const = true,
                "volatile" => specs.quals.is_volatile = true,
                "restrict" => specs.quals.is_restrict = true,
                // `_Atomic` without parentheses is a qualifier and the model
                // has no room for it; dropping it keeps the layout right.
                "_Atomic" | "_Thread_local" | "inline" | "_Noreturn" | "__extension__" => {}
                "void" | "char" | "short" | "int" | "long" | "float" | "double" | "signed"
                | "unsigned" | "_Bool" | "_Complex" => {
                    if specs.base.is_some() {
                        return Err(self
                            .error(at, format!("`{w}` follows a type that is already complete")));
                    }
                    specs.words.push(normalize(&w).to_string());
                }
                "struct" | "union" => {
                    if specs.base.is_some() || !specs.words.is_empty() {
                        return Err(self.error(at, "two type names in one declaration"));
                    }
                    self.at += 1;
                    specs.base = Some(self.composite(normalize(&w) == "union")?);
                    continue;
                }
                "enum" => {
                    if specs.base.is_some() || !specs.words.is_empty() {
                        return Err(self.error(at, "two type names in one declaration"));
                    }
                    self.at += 1;
                    specs.base = Some(self.enumeration()?);
                    continue;
                }
                other => {
                    if specs.base.is_some() || !specs.words.is_empty() {
                        break;
                    }
                    match self.named_type(other) {
                        Some(id) => specs.base = Some(id),
                        None => {
                            return Err(self
                                .error(at, format!("`{other}` is not a type this parser knows")));
                        }
                    }
                }
            }
            self.at += 1;
        }
        Ok(specs)
    }

    /// A type name already in the store, or one of the fixed-width names every
    /// C program assumes `stdint.h` provides.
    fn named_type(&mut self, name: &str) -> Option<TypeId> {
        if let Some(id) = self.types.typedef(name) {
            return Some(id);
        }
        let model = self.types.model();
        let ty = builtin(name, model)?;
        Some(self.types.add(ty))
    }

    fn base_type(&mut self, specs: &Specs, at: usize) -> Result<TypeId, ParseError> {
        let model = self.types.model();
        let base = match specs.base {
            Some(id) => {
                if !specs.words.is_empty() {
                    return Err(self.error(at, "two type names in one declaration"));
                }
                id
            }
            None => {
                let ty = combine(&specs.words, model)
                    .ok_or_else(|| self.error(at, describe_bad_specifiers(&specs.words)))?;
                self.types.add(ty)
            }
        };
        Ok(self.types.qualified(base, specs.quals))
    }

    // -- declarators ------------------------------------------------------

    fn full_declarator(&mut self, base: TypeId) -> Result<(TypeId, Option<String>), ParseError> {
        let d = self.parse_declarator(true)?;
        let (ty, name) = self.apply(&d, base)?;
        Ok((ty, name))
    }

    fn parse_declarator(&mut self, allow_abstract: bool) -> Result<Dcl, ParseError> {
        self.guard()?;
        let mut pointers: Vec<Qualifiers> = Vec::new();
        while self.eat_punct("*") {
            pointers.push(self.qualifiers_only());
        }
        let mut node = self.direct_declarator(allow_abstract)?;
        for q in pointers.into_iter().rev() {
            node = Dcl::Pointer(q, Box::new(node));
        }
        self.depth -= 1;
        Ok(node)
    }

    fn qualifiers_only(&mut self) -> Qualifiers {
        let mut q = Qualifiers::default();
        while let Some(Token::Word(w)) = self.peek().cloned() {
            match normalize(&w) {
                "const" => q.is_const = true,
                "volatile" => q.is_volatile = true,
                "restrict" => q.is_restrict = true,
                "_Atomic" => {}
                _ => break,
            }
            self.at += 1;
        }
        q
    }

    fn direct_declarator(&mut self, allow_abstract: bool) -> Result<Dcl, ParseError> {
        self.guard()?;
        let at = self.here();
        let mut node = match self.peek().cloned() {
            Some(Token::Word(w)) if self.starts_declarator_name(&w) => {
                self.at += 1;
                Dcl::Name(Some(w))
            }
            Some(Token::Punct("(")) if self.paren_is_declarator() => {
                self.at += 1;
                let inner = self.parse_declarator(allow_abstract)?;
                self.expect_punct(")", "to close a parenthesized declarator")?;
                Dcl::Nested(Box::new(inner))
            }
            _ if allow_abstract => Dcl::Name(None),
            other => {
                self.depth -= 1;
                let found = match other {
                    Some(t) => format!("{t}"),
                    None => "the end of the text".to_string(),
                };
                return Err(self.error(at, format!("expected a declared name, found {found}")));
            }
        };

        loop {
            if self.eat_punct("[") {
                let count = self.array_bound()?;
                node = Dcl::Array(Box::new(node), count);
                continue;
            }
            if self.eat_punct("(") {
                let (parameters, varargs) = self.parameters()?;
                node = Dcl::Func(Box::new(node), parameters, varargs);
                continue;
            }
            break;
        }
        self.depth -= 1;
        Ok(node)
    }

    /// True when a word in declarator position is the declared name rather
    /// than the start of something else.
    fn starts_declarator_name(&self, w: &str) -> bool {
        !is_keyword(normalize(w))
    }

    /// `(` after the pointers is either a parenthesized declarator or the
    /// parameter list of an abstract function type. C decides by what follows.
    fn paren_is_declarator(&self) -> bool {
        match self.peek_at(1) {
            Some(Token::Punct("*")) | Some(Token::Punct("(")) => true,
            Some(Token::Word(w)) => {
                !is_keyword(normalize(w))
                    && self.types.typedef(w).is_none()
                    && builtin(w, self.types.model()).is_none()
            }
            _ => false,
        }
    }

    fn array_bound(&mut self) -> Result<Option<u64>, ParseError> {
        // `static` and qualifiers inside the brackets are a promise to the
        // optimizer and say nothing about the layout.
        loop {
            if self.eat_word("static") {
                continue;
            }
            let before = self.at;
            self.qualifiers_only();
            if self.at == before {
                break;
            }
        }
        if self.eat_punct("]") {
            return Ok(None);
        }
        let at = self.here();
        if self.eat_punct("*") {
            self.expect_punct("]", "to close a variable length array bound")?;
            return Err(self.error(at, "a variable length array has no fixed size"));
        }
        let value = self.constant()?;
        self.expect_punct("]", "to close an array bound")?;
        if value < 0 {
            return Err(self.error(at, "an array bound cannot be negative"));
        }
        Ok(Some(value as u64))
    }

    #[allow(clippy::type_complexity)]
    fn parameters(&mut self) -> Result<(Vec<(Option<String>, TypeId)>, bool), ParseError> {
        let mut out = Vec::new();
        let mut varargs = false;
        if self.eat_punct(")") {
            // `f()` says nothing about the parameters; the model has no way to
            // record "unspecified" apart from "none", and none is the reading
            // every modern compiler gives it.
            return Ok((out, false));
        }
        loop {
            let at = self.here();
            if self.eat_punct("...") {
                varargs = true;
                break;
            }
            let specs = self.specifiers()?;
            let base = self.base_type(&specs, at)?;
            let d = self.parse_declarator(true)?;
            let (ty, name) = self.apply(&d, base)?;
            // `(void)` alone is an empty parameter list, not a parameter.
            if out.is_empty()
                && name.is_none()
                && !varargs
                && ty == Types::VOID
                && matches!(self.peek(), Some(Token::Punct(")")))
            {
                break;
            }
            let ty = self.adjust_parameter(ty, at)?;
            out.push((name, ty));
            if !self.eat_punct(",") {
                break;
            }
        }
        self.expect_punct(")", "to close a parameter list")?;
        Ok((out, varargs))
    }

    /// A parameter declared as an array or a function is a pointer, which is
    /// what the convention actually passes.
    fn adjust_parameter(&mut self, ty: TypeId, at: usize) -> Result<TypeId, ParseError> {
        match self.types.get(self.types.resolve(ty)) {
            Some(Type::Array(inner, _)) => {
                let inner = *inner;
                Ok(self.types.pointer(inner))
            }
            Some(Type::Function(_)) => Ok(self.types.pointer(ty)),
            Some(Type::Void) => Err(self.error(at, "a parameter cannot be `void`")),
            _ => Ok(ty),
        }
    }

    /// Give a declarator a base type, producing the type and the name.
    ///
    /// A loop rather than a recursion. `int *****p` is a chain five thousand
    /// long if somebody types it that way, and refusing it for depth would be
    /// refusing something that costs linear memory and no stack. What the
    /// parser does bound is nesting, which is where the recursion actually is.
    fn apply(&mut self, d: &Dcl, mut base: TypeId) -> Result<(TypeId, Option<String>), ParseError> {
        let mut node = d;
        loop {
            match node {
                Dcl::Name(n) => return Ok((base, n.clone())),
                Dcl::Pointer(q, inner) => {
                    let p = self.types.pointer(base);
                    base = self.types.qualified(p, *q);
                    node = inner;
                }
                Dcl::Array(inner, count) => {
                    if self.types.get(self.types.resolve(base)) == Some(&Type::Void) {
                        return Err(
                            self.error(self.here(), "an array of `void` has no element size")
                        );
                    }
                    base = self.types.add(Type::Array(base, *count));
                    node = inner;
                }
                Dcl::Func(inner, parameters, varargs) => {
                    if matches!(
                        self.types.get(self.types.resolve(base)),
                        Some(Type::Array(..)) | Some(Type::Function(_))
                    ) {
                        return Err(self.error(
                            self.here(),
                            "a function cannot return an array or another function",
                        ));
                    }
                    let returns = (self.types.resolve(base) != Types::VOID).then_some(base);
                    base = self.types.add(Type::Function(Signature {
                        returns,
                        parameters: parameters.clone(),
                        varargs: *varargs,
                    }));
                    node = inner;
                }
                Dcl::Nested(inner) => node = inner,
            }
        }
    }

    // -- tagged types ------------------------------------------------------

    fn composite(&mut self, union: bool) -> Result<TypeId, ParseError> {
        self.guard()?;
        let keyword = if union { "union" } else { "struct" };
        let at = self.here();
        let tag = match self.peek().cloned() {
            Some(Token::Word(w)) if !is_keyword(normalize(&w)) => {
                self.at += 1;
                Some(w)
            }
            _ => None,
        };

        // Registering the tag before the body is parsed is what makes
        // `struct node { struct node *next; }` work at all.
        let id = match &tag {
            Some(t) => match self.types.composite(union, t) {
                Some(id) => id,
                None => self.types.add(Type::Composite(Composite {
                    name: Some(t.clone()),
                    union,
                    size: None,
                    fields: Vec::new(),
                })),
            },
            None => TypeId(u32::MAX),
        };

        if !self.eat_punct("{") {
            self.depth -= 1;
            return match tag {
                Some(_) => Ok(id),
                None => Err(self.error(at, format!("`{keyword}` with no tag and no body"))),
            };
        }

        let members = self.members()?;
        let (fields, size) = self.layout(union, members, at)?;
        let complete = Type::Composite(Composite {
            name: tag.clone(),
            union,
            size: Some(size),
            fields,
        });
        self.depth -= 1;
        match tag {
            Some(_) => {
                self.types.define(id, complete);
                Ok(id)
            }
            None => Ok(self.types.add(complete)),
        }
    }

    fn members(&mut self) -> Result<Vec<Member>, ParseError> {
        let mut out = Vec::new();
        while !self.eat_punct("}") {
            if self.peek().is_none() {
                return Err(self.error(self.here(), "a structure body was never closed"));
            }
            if self.eat_punct(";") {
                continue;
            }
            let at = self.here();
            let specs = self.specifiers()?;
            if specs.storage.is_some() {
                return Err(self.error(at, "a structure member has no storage class"));
            }
            let base = self.base_type(&specs, at)?;

            // An anonymous member: `struct { int a; };` inside another.
            if self.eat_punct(";") {
                let resolved = self.types.resolve(base);
                if !matches!(self.types.get(resolved), Some(Type::Composite(_))) {
                    return Err(self.error(at, "this member declares a type and no field"));
                }
                out.push(Member {
                    name: None,
                    ty: base,
                    bits: None,
                    at,
                });
                continue;
            }

            loop {
                let at = self.here();
                // `int : 3;` is unnamed padding and has no declarator.
                if self.eat_punct(":") {
                    let width = self.constant()?;
                    out.push(Member {
                        name: None,
                        ty: base,
                        bits: Some(self.bit_width(width, at)?),
                        at,
                    });
                } else {
                    let (ty, name) = self.full_declarator(base)?;
                    let bits = if self.eat_punct(":") {
                        let width = self.constant()?;
                        Some(self.bit_width(width, at)?)
                    } else {
                        None
                    };
                    let Some(name) = name else {
                        return Err(self.error(at, "a structure member needs a name"));
                    };
                    out.push(Member {
                        name: Some(name),
                        ty,
                        bits,
                        at,
                    });
                }
                if !self.eat_punct(",") {
                    break;
                }
            }
            self.expect_punct(";", "after a structure member")?;
        }
        Ok(out)
    }

    fn bit_width(&self, width: i128, at: usize) -> Result<u8, ParseError> {
        if !(0..=64).contains(&width) {
            return Err(self.error(at, format!("{width} is not a bitfield width")));
        }
        Ok(width as u8)
    }

    /// Place the members, in bits, and give the whole thing a size.
    ///
    /// The rule is the one the System V and Itanium C++ ABIs share: a bitfield
    /// goes in the current storage unit of its declared type when it fits and
    /// starts a new one when it does not, and a zero-width one closes the unit.
    /// A field records the byte offset of the unit holding its first bit,
    /// which is what the debug formats record too; the model has no room for
    /// the bit position within it.
    fn layout(
        &mut self,
        union: bool,
        members: Vec<Member>,
        at: usize,
    ) -> Result<(Vec<Field>, u64), ParseError> {
        let mut fields = Vec::new();
        let mut bits: u64 = 0;
        let mut max_align: u64 = 1;
        let mut widest: u64 = 0;

        for (n, m) in members.iter().enumerate() {
            let align = self.types.align_of(m.ty).unwrap_or(1).max(1);
            max_align = max_align.max(align);
            let last = n + 1 == members.len();
            let size = match self.types.size_of(m.ty) {
                Some(s) => s,
                // A flexible array member is the one incomplete type a
                // structure may end with.
                None if last
                    && matches!(
                        self.types.get(self.types.resolve(m.ty)),
                        Some(Type::Array(_, None))
                    ) =>
                {
                    0
                }
                None => {
                    let name = m.name.clone().unwrap_or_else(|| "a member".into());
                    return Err(self.error(
                        m.at,
                        format!(
                            "`{name}` has type `{}`, whose size is not known here",
                            self.types.name_of(m.ty)
                        ),
                    ));
                }
            };

            if union {
                if m.bits == Some(0) {
                    continue;
                }
                widest = widest.max(size);
                fields.push(Field {
                    name: m.name.clone().unwrap_or_default(),
                    ty: m.ty,
                    offset: 0,
                    bits: m.bits,
                });
                continue;
            }

            match m.bits {
                None => {
                    bits = round_up(bits, align * 8);
                    let offset = bits / 8;
                    bits += size * 8;
                    fields.push(Field {
                        name: m.name.clone().unwrap_or_default(),
                        ty: m.ty,
                        offset,
                        bits: None,
                    });
                }
                Some(0) => {
                    // A zero-width bitfield closes the current unit.
                    bits = round_up(bits, align * 8);
                }
                Some(width) => {
                    let unit = (size.max(1)) * 8;
                    let start = (bits / unit) * unit;
                    if bits + width as u64 > start + unit {
                        bits = round_up(bits, align * 8);
                    }
                    let offset = (bits / unit) * unit / 8;
                    fields.push(Field {
                        name: m.name.clone().unwrap_or_default(),
                        ty: m.ty,
                        offset,
                        bits: Some(width),
                    });
                    bits += width as u64;
                }
            }
        }

        let size = if union {
            round_up(widest, max_align)
        } else {
            round_up(round_up(bits, 8) / 8, max_align)
        };
        // A structure larger than a process address space is a mistake in the
        // text rather than a type.
        if size > u32::MAX as u64 {
            return Err(self.error(at, "this structure is larger than four gigabytes"));
        }
        Ok((fields, size))
    }

    fn enumeration(&mut self) -> Result<TypeId, ParseError> {
        self.guard()?;
        let at = self.here();
        let tag = match self.peek().cloned() {
            Some(Token::Word(w)) if !is_keyword(normalize(&w)) => {
                self.at += 1;
                Some(w)
            }
            _ => None,
        };
        // C23 allows a fixed underlying type; the model has no room for one.
        if self.eat_punct(":") {
            return Err(self.error(
                at,
                "an enumeration with a fixed underlying type is not read",
            ));
        }
        if !self.eat_punct("{") {
            self.depth -= 1;
            return match &tag {
                Some(t) => Ok(match self.types.enumeration(t) {
                    Some(id) => id,
                    None => self.types.add(Type::Enum(Enumeration {
                        name: tag.clone(),
                        size: self.types.model().enum_size,
                        values: Vec::new(),
                    })),
                }),
                None => Err(self.error(at, "`enum` with no tag and no body")),
            };
        }

        let mut values: Vec<(String, i64)> = Vec::new();
        let mut next: i128 = 0;
        while !self.eat_punct("}") {
            let at = self.here();
            let Some(Token::Word(name)) = self.bump() else {
                return Err(self.error(at, "an enumerator must be a name"));
            };
            if is_keyword(normalize(&name)) {
                return Err(self.error(at, format!("`{name}` is a keyword, not an enumerator")));
            }
            if self.eat_punct("=") {
                next = self.constant()?;
            }
            if !(i64::MIN as i128..=u64::MAX as i128).contains(&next) {
                return Err(self.error(at, format!("`{name}` has a value no integer type holds")));
            }
            self.enumerators.insert(name.clone(), next);
            values.push((name, next as i64));
            next = next.wrapping_add(1);
            if !self.eat_punct(",") {
                self.expect_punct("}", "to close an enumeration")?;
                break;
            }
        }

        // Enumerators that do not fit the target's `int` widen the type, which
        // is what every compiler this tool reads output from does.
        let model = self.types.model();
        let fits = values
            .iter()
            .all(|(_, v)| (i32::MIN as i64..=u32::MAX as i64).contains(v));
        let size = if fits { model.enum_size } else { 8 };
        let ty = Type::Enum(Enumeration {
            name: tag.clone(),
            size,
            values,
        });
        self.depth -= 1;
        match &tag {
            Some(t) => {
                let id = match self.types.enumeration(t) {
                    Some(id) => id,
                    None => self.types.add(Type::Enum(Enumeration {
                        name: tag.clone(),
                        size,
                        values: Vec::new(),
                    })),
                };
                self.types.define(id, ty);
                Ok(id)
            }
            None => Ok(self.types.add(ty)),
        }
    }

    // -- constant expressions ---------------------------------------------

    fn constant(&mut self) -> Result<i128, ParseError> {
        self.guard()?;
        let v = self.conditional(0)?;
        self.depth -= 1;
        Ok(v)
    }

    fn conditional(&mut self, depth: u32) -> Result<i128, ParseError> {
        let cond = self.binary(0, depth)?;
        if self.eat_punct("?") {
            let a = self.conditional(depth + 1)?;
            self.expect_punct(":", "in a conditional expression")?;
            let b = self.conditional(depth + 1)?;
            return Ok(if cond != 0 { a } else { b });
        }
        Ok(cond)
    }

    fn binary(&mut self, min: u8, depth: u32) -> Result<i128, ParseError> {
        if depth > MAX_DEPTH {
            return Err(self.error(self.here(), "this expression nests too deeply to read"));
        }
        let mut left = self.unary(depth)?;
        while let Some(Token::Punct(op)) = self.peek().cloned() {
            let Some(prec) = precedence(op) else { break };
            if prec < min {
                break;
            }
            let at = self.here();
            self.at += 1;
            let right = self.binary(prec + 1, depth + 1)?;
            left = match op {
                "*" => left.wrapping_mul(right),
                "/" | "%" => {
                    if right == 0 {
                        return Err(self.error(at, "division by zero in a constant expression"));
                    }
                    if op == "/" {
                        left / right
                    } else {
                        left % right
                    }
                }
                "+" => left.wrapping_add(right),
                "-" => left.wrapping_sub(right),
                "<<" => left.wrapping_shl((right as u32).min(127)),
                ">>" => left.wrapping_shr((right as u32).min(127)),
                "<" => (left < right) as i128,
                ">" => (left > right) as i128,
                "<=" => (left <= right) as i128,
                ">=" => (left >= right) as i128,
                "==" => (left == right) as i128,
                "!=" => (left != right) as i128,
                "&" => left & right,
                "^" => left ^ right,
                "|" => left | right,
                "&&" => ((left != 0) && (right != 0)) as i128,
                "||" => ((left != 0) || (right != 0)) as i128,
                _ => return Err(self.error(at, format!("`{op}` is not an operator here"))),
            };
        }
        Ok(left)
    }

    fn unary(&mut self, depth: u32) -> Result<i128, ParseError> {
        if depth > MAX_DEPTH {
            return Err(self.error(self.here(), "this expression nests too deeply to read"));
        }
        let at = self.here();
        if self.eat_punct("-") {
            return Ok(self.unary(depth + 1)?.wrapping_neg());
        }
        if self.eat_punct("+") {
            return self.unary(depth + 1);
        }
        if self.eat_punct("~") {
            return Ok(!self.unary(depth + 1)?);
        }
        if self.eat_punct("!") {
            return Ok((self.unary(depth + 1)? == 0) as i128);
        }
        if self.eat_punct("(") {
            let v = self.conditional(depth + 1)?;
            self.expect_punct(")", "to close a parenthesized expression")?;
            return Ok(v);
        }
        match self.bump() {
            Some(Token::Number(n)) => Ok(n),
            Some(Token::Word(w)) => match self.enumerators.get(&w).copied() {
                Some(v) => Ok(v),
                None => match self.macro_value(&w) {
                    Some(v) => Ok(v),
                    None => Err(self.error(
                        at,
                        format!(
                            "`{w}` has no value here; only enumerators, object-like \
                             `#define`s and literals do"
                        ),
                    )),
                },
            },
            other => {
                let found = match other {
                    Some(t) => format!("{t}"),
                    None => "the end of the text".to_string(),
                };
                Err(self.error(at, format!("expected a constant, found {found}")))
            }
        }
    }
}

/// A declarator's shape, before a base type is applied to it.
///
/// The outermost node is the one applied to the base type first, which is what
/// makes `char *argv[]` an array of pointers and `char (*argv)[]` a pointer to
/// an array without either spelling needing a special case.
#[derive(Debug, Clone)]
enum Dcl {
    Name(Option<String>),
    Pointer(Qualifiers, Box<Dcl>),
    Array(Box<Dcl>, Option<u64>),
    Func(Box<Dcl>, Vec<(Option<String>, TypeId)>, bool),
    Nested(Box<Dcl>),
}

struct Member {
    name: Option<String>,
    ty: TypeId,
    bits: Option<u8>,
    at: usize,
}

#[derive(Debug, Default)]
struct Specs {
    storage: Option<Storage>,
    quals: Qualifiers,
    base: Option<TypeId>,
    words: Vec<String>,
}

impl Specs {
    fn set_storage(&mut self, s: Storage) {
        self.storage = Some(s);
    }
}

fn round_up(v: u64, to: u64) -> u64 {
    if to <= 1 {
        return v;
    }
    v.div_ceil(to) * to
}

fn precedence(op: &str) -> Option<u8> {
    Some(match op {
        "||" => 1,
        "&&" => 2,
        "|" => 3,
        "^" => 4,
        "&" => 5,
        "==" | "!=" => 6,
        "<" | ">" | "<=" | ">=" => 7,
        "<<" | ">>" => 8,
        "+" | "-" => 9,
        "*" | "/" | "%" => 10,
        _ => return None,
    })
}

/// GNU spells several keywords with underscores around them so a program may
/// use the bare word as an identifier. They mean the same thing.
fn normalize(word: &str) -> &str {
    match word {
        "__const" | "__const__" => "const",
        "__volatile" | "__volatile__" => "volatile",
        "__restrict" | "__restrict__" => "restrict",
        "__signed" | "__signed__" => "signed",
        "__unsigned" | "__unsigned__" => "unsigned",
        "__inline" | "__inline__" => "inline",
        "__complex__" => "_Complex",
        "__extension__" => "__extension__",
        other => other,
    }
}

fn is_keyword(word: &str) -> bool {
    matches!(
        word,
        "void"
            | "char"
            | "short"
            | "int"
            | "long"
            | "float"
            | "double"
            | "signed"
            | "unsigned"
            | "_Bool"
            | "_Complex"
            | "struct"
            | "union"
            | "enum"
            | "const"
            | "volatile"
            | "restrict"
            | "_Atomic"
            | "typedef"
            | "extern"
            | "static"
            | "auto"
            | "register"
            | "inline"
            | "_Noreturn"
            | "_Thread_local"
            | "__extension__"
            | "sizeof"
    )
}

/// The fixed-width names every C program assumes `stdint.h` provides.
///
/// They map to the integer type rather than to a typedef of it, because that
/// is what they are: `int32_t` names a four-byte signed integer and nothing
/// else, and making it a distinct node would make `int` and `int32_t` compare
/// unequal for no gain. A header that defines them itself wins, because the
/// store is consulted first.
fn builtin(name: &str, model: Model) -> Option<Type> {
    let signed = |size: u8| Type::Int { size, signed: true };
    let unsigned = |size: u8| Type::Int {
        size,
        signed: false,
    };
    Some(match name {
        "int8_t" => signed(1),
        "int16_t" => signed(2),
        "int32_t" => signed(4),
        "int64_t" => signed(8),
        "uint8_t" => unsigned(1),
        "uint16_t" => unsigned(2),
        "uint32_t" => unsigned(4),
        "uint64_t" => unsigned(8),
        "intmax_t" => signed(8),
        "uintmax_t" => unsigned(8),
        "intptr_t" | "ssize_t" | "ptrdiff_t" => signed(model.pointer),
        "uintptr_t" | "size_t" => unsigned(model.pointer),
        // Four bytes on every target with an ELF or Mach-O container; the
        // two-byte Windows spelling is `wchar_t` too and is not distinguished.
        "wchar_t" => signed(4),
        "char8_t" => unsigned(1),
        "char16_t" => unsigned(2),
        "char32_t" => unsigned(4),
        "bool" => Type::Bool,
        _ => return None,
    })
}

/// Turn the collected `int`, `long`, `unsigned` and friends into one type.
fn combine(words: &[String], model: Model) -> Option<Type> {
    let count = |w: &str| words.iter().filter(|x| x.as_str() == w).count();
    let signed = count("signed");
    let unsigned = count("unsigned");
    if signed + unsigned > 1 {
        return None;
    }
    let longs = count("long");
    let is_signed = unsigned == 0;

    if count("_Complex") > 0 {
        // The model has no complex type and pretending it is a `double` would
        // halve the size.
        return None;
    }
    if count("void") > 0 {
        return (words.len() == 1).then_some(Type::Void);
    }
    if count("_Bool") > 0 {
        return (words.len() == 1).then_some(Type::Bool);
    }
    if count("float") > 0 {
        return (words.len() == 1).then_some(Type::Float { size: model.float });
    }
    if count("double") > 0 {
        if count("short") > 0 || count("int") > 0 || signed + unsigned > 0 || longs > 1 {
            return None;
        }
        let size = if longs == 1 {
            model.long_double
        } else {
            model.double
        };
        return Some(Type::Float { size });
    }
    if count("char") > 0 {
        if count("short") > 0 || longs > 0 || count("int") > 0 {
            return None;
        }
        let signedness = if signed + unsigned == 0 {
            model.char_signed
        } else {
            is_signed
        };
        return Some(Type::Int {
            size: 1,
            signed: signedness,
        });
    }
    if count("short") > 0 {
        if longs > 0 {
            return None;
        }
        return Some(Type::Int {
            size: model.short,
            signed: is_signed,
        });
    }
    let size = match longs {
        0 => model.int,
        1 => model.long,
        2 => model.long_long,
        _ => return None,
    };
    // `signed`, `unsigned`, `int`, `long` and `long long` in any order; a word
    // that is none of those means the caller did not collect a type at all.
    if count("int") + signed + unsigned + longs != words.len() {
        return None;
    }
    if words.is_empty() {
        return None;
    }
    Some(Type::Int {
        size,
        signed: is_signed,
    })
}

fn describe_bad_specifiers(words: &[String]) -> String {
    if words.is_empty() {
        return "this declaration names no type".to_string();
    }
    format!("`{}` is not a type", words.join(" "))
}
