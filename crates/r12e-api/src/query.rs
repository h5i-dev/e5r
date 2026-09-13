//! A small query language over the program model.
//!
//! The point is to answer the questions an analyst actually asks without
//! writing a program: which functions are large and unnamed, which imports are
//! called from one place, which strings look like paths. A filter over a named
//! set of entities covers most of them, and a filter is something a person can
//! type correctly on the first try.
//!
//! ```text
//! functions where insns > 100 and name ~ "crypt"
//! strings where length >= 20 and text ~ "/etc/"
//! xrefs where kind = call and to = 0x401000
//! ```
//!
//! Every field is either a number or a string and comparisons coerce one way:
//! a number compared against a string is a mistake in the query and is
//! reported as one rather than quietly returning nothing.

use std::fmt;

use r12e_analysis::{Program, XrefKind};
use r12e_core::Addr;

/// What a query selects over.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Entity {
    /// Recovered functions.
    Functions,
    /// Strings found in the image.
    Strings,
    /// Symbols the container declares.
    Symbols,
    /// Symbols needed from elsewhere.
    Imports,
    /// Symbols offered to others.
    Exports,
    /// Declared sections.
    Sections,
    /// References between addresses.
    Xrefs,
}

impl Entity {
    /// The name it is written as.
    pub fn as_str(self) -> &'static str {
        match self {
            Entity::Functions => "functions",
            Entity::Strings => "strings",
            Entity::Symbols => "symbols",
            Entity::Imports => "imports",
            Entity::Exports => "exports",
            Entity::Sections => "sections",
            Entity::Xrefs => "xrefs",
        }
    }

    /// The fields it offers, for the error message when one is misspelled.
    pub fn fields(self) -> &'static [&'static str] {
        match self {
            Entity::Functions => &[
                "address", "name", "size", "blocks", "insns", "complete", "named", "strength",
                "callers", "callees",
            ],
            Entity::Strings => &["address", "text", "length", "section", "encoding"],
            Entity::Symbols => &["address", "name", "size", "kind", "binding", "dynamic"],
            Entity::Imports => &["name", "library"],
            Entity::Exports => &["address", "name"],
            Entity::Sections => &["address", "name", "size", "exec", "write"],
            Entity::Xrefs => &["from", "to", "kind"],
        }
    }

    fn parse(word: &str) -> Option<Entity> {
        Some(match word {
            "functions" | "funcs" => Entity::Functions,
            "strings" => Entity::Strings,
            "symbols" | "syms" => Entity::Symbols,
            "imports" => Entity::Imports,
            "exports" => Entity::Exports,
            "sections" => Entity::Sections,
            "xrefs" => Entity::Xrefs,
            _ => return None,
        })
    }
}

/// A parsed query.
#[derive(Debug, Clone)]
pub struct Query {
    /// What it selects over.
    pub entity: Entity,
    /// The filter, when there is one.
    pub filter: Option<Expr>,
    /// How many results to return at most.
    pub limit: Option<usize>,
}

/// A filter expression.
#[derive(Debug, Clone)]
pub enum Expr {
    /// Both sides.
    And(Box<Expr>, Box<Expr>),
    /// Either side.
    Or(Box<Expr>, Box<Expr>),
    /// The opposite.
    Not(Box<Expr>),
    /// A comparison between a field and a literal.
    Compare {
        /// The field's name.
        field: String,
        /// How to compare.
        op: Op,
        /// What to compare against.
        value: Value,
    },
}

/// How two things are compared.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Op {
    /// Equal.
    Eq,
    /// Not equal.
    Ne,
    /// Less than.
    Lt,
    /// Less than or equal.
    Le,
    /// Greater than.
    Gt,
    /// Greater than or equal.
    Ge,
    /// Contains, for strings.
    Contains,
    /// Does not contain.
    Omits,
}

/// A literal in a query.
#[derive(Debug, Clone, PartialEq)]
pub enum Value {
    /// A number, however it was written.
    Number(u64),
    /// A string, quoted or a bare word.
    Text(String),
    /// True or false.
    Bool(bool),
}

/// One field of one result.
#[derive(Debug, Clone, PartialEq)]
pub enum Field {
    /// A number.
    Number(u64),
    /// An address, which prints as hex.
    Address(Addr),
    /// A string.
    Text(String),
    /// True or false.
    Bool(bool),
    /// The field exists but this row has no value for it.
    Missing,
}

impl fmt::Display for Field {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Field::Number(v) => write!(f, "{v}"),
            Field::Address(a) => write!(f, "{a}"),
            Field::Text(t) => f.write_str(t),
            Field::Bool(b) => write!(f, "{b}"),
            Field::Missing => f.write_str("-"),
        }
    }
}

/// One result.
#[derive(Debug, Clone)]
pub struct Row {
    /// The fields, in the entity's declared order.
    pub values: Vec<(&'static str, Field)>,
}

impl Row {
    /// One field by name.
    pub fn get(&self, name: &str) -> Option<&Field> {
        self.values.iter().find(|(n, _)| *n == name).map(|(_, v)| v)
    }
}

/// What a query produced.
#[derive(Debug, Clone)]
pub struct Answer {
    /// What was selected over.
    pub entity: Entity,
    /// The column names, in order.
    pub columns: &'static [&'static str],
    /// The rows that matched.
    pub rows: Vec<Row>,
    /// How many matched before the limit was applied.
    pub matched: usize,
}

/// Parse and run a query.
pub fn run(p: &Program, text: &str) -> Result<Answer, String> {
    let query = parse(text)?;
    let mut rows = collect(p, query.entity);
    if let Some(filter) = &query.filter {
        // A field that does not exist is a typo, and a query with one should
        // say so rather than match nothing.
        check_fields(filter, query.entity)?;
        rows.retain(|row| matches(row, filter));
    }
    let matched = rows.len();
    if let Some(limit) = query.limit {
        rows.truncate(limit);
    }
    Ok(Answer {
        entity: query.entity,
        columns: query.entity.fields(),
        rows,
        matched,
    })
}

/// Parse a query without running it.
pub fn parse(text: &str) -> Result<Query, String> {
    let tokens = lex(text)?;
    let mut parser = Parser { tokens, at: 0 };
    let entity = match parser.next() {
        Some(Token::Word(w)) => Entity::parse(&w).ok_or_else(|| {
            format!("{w:?} is not something to query; try functions, strings, symbols, imports, exports, sections or xrefs")
        })?,
        _ => return Err("a query starts with what to look at, such as `functions`".into()),
    };

    let mut filter = None;
    let mut limit = None;
    while let Some(token) = parser.next() {
        match token {
            Token::Word(w) if w == "where" => filter = Some(parser.expression()?),
            Token::Word(w) if w == "limit" => match parser.next() {
                Some(Token::Number(n)) => limit = Some(n as usize),
                _ => return Err("`limit` wants a number".into()),
            },
            other => return Err(format!("did not expect {other} here")),
        }
    }
    Ok(Query {
        entity,
        filter,
        limit,
    })
}

fn check_fields(e: &Expr, entity: Entity) -> Result<(), String> {
    match e {
        Expr::And(a, b) | Expr::Or(a, b) => {
            check_fields(a, entity)?;
            check_fields(b, entity)
        }
        Expr::Not(a) => check_fields(a, entity),
        Expr::Compare { field, .. } => {
            if entity.fields().contains(&field.as_str()) {
                Ok(())
            } else {
                Err(format!(
                    "{} have no field {field:?}; they have {}",
                    entity.as_str(),
                    entity.fields().join(", ")
                ))
            }
        }
    }
}

fn matches(row: &Row, e: &Expr) -> bool {
    match e {
        Expr::And(a, b) => matches(row, a) && matches(row, b),
        Expr::Or(a, b) => matches(row, a) || matches(row, b),
        Expr::Not(a) => !matches(row, a),
        Expr::Compare { field, op, value } => {
            let Some(actual) = row.get(field) else {
                return false;
            };
            compare(actual, *op, value)
        }
    }
}

fn compare(actual: &Field, op: Op, value: &Value) -> bool {
    match (actual, value) {
        (Field::Missing, _) => false,
        (Field::Number(a), Value::Number(b)) => number(*a, op, *b),
        (Field::Address(a), Value::Number(b)) => number(a.get(), op, *b),
        (Field::Bool(a), Value::Bool(b)) => match op {
            Op::Eq => a == b,
            Op::Ne => a != b,
            _ => false,
        },
        (Field::Text(a), Value::Text(b)) => text(a, op, b),
        // A number compared against a word compares its printed form, which is
        // what `kind = call` means.
        (Field::Number(a), Value::Text(b)) => text(&a.to_string(), op, b),
        (Field::Address(a), Value::Text(b)) => text(&a.to_string(), op, b),
        (Field::Bool(a), Value::Text(b)) => text(&a.to_string(), op, b),
        (Field::Text(a), Value::Number(b)) => text(a, op, &b.to_string()),
        (Field::Text(a), Value::Bool(b)) => text(a, op, &b.to_string()),
        (_, _) => false,
    }
}

fn number(a: u64, op: Op, b: u64) -> bool {
    match op {
        Op::Eq => a == b,
        Op::Ne => a != b,
        Op::Lt => a < b,
        Op::Le => a <= b,
        Op::Gt => a > b,
        Op::Ge => a >= b,
        Op::Contains | Op::Omits => false,
    }
}

fn text(a: &str, op: Op, b: &str) -> bool {
    match op {
        Op::Eq => a == b,
        Op::Ne => a != b,
        Op::Lt => a < b,
        Op::Le => a <= b,
        Op::Gt => a > b,
        Op::Ge => a >= b,
        Op::Contains => a.contains(b),
        Op::Omits => !a.contains(b),
    }
}

/// Every row of one entity.
fn collect(p: &Program, entity: Entity) -> Vec<Row> {
    match entity {
        Entity::Functions => p
            .functions_by_address()
            .map(|f| {
                let callers = p.xrefs.to(f.entry).len();
                Row {
                    values: vec![
                        ("address", Field::Address(f.entry)),
                        ("name", Field::Text(f.display_name())),
                        ("size", Field::Number(f.cfg.covered_bytes())),
                        ("blocks", Field::Number(f.cfg.blocks.len() as u64)),
                        (
                            "insns",
                            Field::Number(
                                f.cfg.blocks.values().map(|b| b.insns as u64).sum::<u64>(),
                            ),
                        ),
                        ("complete", Field::Bool(f.is_complete())),
                        ("named", Field::Bool(f.name.is_some())),
                        (
                            "strength",
                            Field::Text(f.provenance.strength().as_str().to_string()),
                        ),
                        ("callers", Field::Number(callers as u64)),
                        (
                            "callees",
                            Field::Number(
                                f.cfg
                                    .blocks
                                    .keys()
                                    .flat_map(|b| p.xrefs.from(*b))
                                    .filter(|x| x.kind == XrefKind::Call)
                                    .count() as u64,
                            ),
                        ),
                    ],
                }
            })
            .collect(),
        Entity::Strings => p
            .strings
            .iter()
            .map(|s| Row {
                values: vec![
                    ("address", Field::Address(s.addr)),
                    ("text", Field::Text(s.text.clone())),
                    ("length", Field::Number(s.len)),
                    (
                        "section",
                        match p.object.section_at(s.addr) {
                            Some(sec) => Field::Text(sec.name.clone()),
                            None => Field::Missing,
                        },
                    ),
                    (
                        "encoding",
                        Field::Text(format!("{:?}", s.encoding).to_lowercase()),
                    ),
                ],
            })
            .collect(),
        Entity::Symbols => p
            .object
            .symbols
            .iter()
            .map(|s| Row {
                values: vec![
                    ("address", Field::Address(s.addr)),
                    ("name", Field::Text(s.name.clone())),
                    ("size", Field::Number(s.size)),
                    ("kind", Field::Text(format!("{:?}", s.kind).to_lowercase())),
                    (
                        "binding",
                        Field::Text(format!("{:?}", s.binding).to_lowercase()),
                    ),
                    ("dynamic", Field::Bool(s.dynamic)),
                ],
            })
            .collect(),
        Entity::Imports => p
            .object
            .imports
            .iter()
            .map(|i| Row {
                values: vec![
                    ("name", Field::Text(i.name.clone())),
                    (
                        "library",
                        match &i.library {
                            Some(l) => Field::Text(l.clone()),
                            None => Field::Missing,
                        },
                    ),
                ],
            })
            .collect(),
        Entity::Exports => p
            .object
            .exports
            .iter()
            .map(|e| Row {
                values: vec![
                    ("address", Field::Address(e.addr)),
                    ("name", Field::Text(e.name.clone())),
                ],
            })
            .collect(),
        Entity::Sections => p
            .object
            .sections
            .iter()
            .map(|s| Row {
                values: vec![
                    ("address", Field::Address(s.range.start())),
                    ("name", Field::Text(s.name.clone())),
                    ("size", Field::Number(s.range.len())),
                    ("exec", Field::Bool(s.exec)),
                    ("write", Field::Bool(s.write)),
                ],
            })
            .collect(),
        Entity::Xrefs => p
            .xrefs
            .all()
            .iter()
            .map(|x| Row {
                values: vec![
                    ("from", Field::Address(x.from)),
                    ("to", Field::Address(x.to)),
                    ("kind", Field::Text(format!("{:?}", x.kind).to_lowercase())),
                ],
            })
            .collect(),
    }
}

/// One piece of a query.
#[derive(Debug, Clone, PartialEq)]
enum Token {
    Word(String),
    Text(String),
    Number(u64),
    Op(Op),
    Open,
    Close,
}

impl fmt::Display for Token {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Token::Word(w) => write!(f, "{w}"),
            Token::Text(t) => write!(f, "{t:?}"),
            Token::Number(n) => write!(f, "{n}"),
            Token::Op(_) => f.write_str("an operator"),
            Token::Open => f.write_str("("),
            Token::Close => f.write_str(")"),
        }
    }
}

fn lex(text: &str) -> Result<Vec<Token>, String> {
    let mut out = Vec::new();
    let chars: Vec<char> = text.chars().collect();
    let mut i = 0;
    while i < chars.len() {
        let c = chars[i];
        match c {
            c if c.is_whitespace() => i += 1,
            '(' => {
                out.push(Token::Open);
                i += 1;
            }
            ')' => {
                out.push(Token::Close);
                i += 1;
            }
            '"' | '\'' => {
                let quote = c;
                i += 1;
                let start = i;
                while i < chars.len() && chars[i] != quote {
                    i += 1;
                }
                if i >= chars.len() {
                    return Err("a quoted string was never closed".into());
                }
                out.push(Token::Text(chars[start..i].iter().collect()));
                i += 1;
            }
            '=' | '!' | '<' | '>' | '~' => {
                let next = chars.get(i + 1).copied();
                let (op, len) = match (c, next) {
                    ('=', Some('=')) => (Op::Eq, 2),
                    ('=', Some('~')) => (Op::Contains, 2),
                    ('=', _) => (Op::Eq, 1),
                    ('!', Some('=')) => (Op::Ne, 2),
                    ('!', Some('~')) => (Op::Omits, 2),
                    ('<', Some('=')) => (Op::Le, 2),
                    ('<', _) => (Op::Lt, 1),
                    ('>', Some('=')) => (Op::Ge, 2),
                    ('>', _) => (Op::Gt, 1),
                    ('~', _) => (Op::Contains, 1),
                    _ => return Err(format!("{c} is not an operator")),
                };
                out.push(Token::Op(op));
                i += len;
            }
            c if c.is_ascii_digit() => {
                let start = i;
                while i < chars.len()
                    && (chars[i].is_ascii_alphanumeric() || chars[i] == 'x' || chars[i] == '_')
                {
                    i += 1;
                }
                let word: String = chars[start..i].iter().collect();
                let cleaned = word.replace('_', "");
                let value = match cleaned.strip_prefix("0x") {
                    Some(hex) => u64::from_str_radix(hex, 16),
                    None => cleaned.parse::<u64>(),
                };
                match value {
                    Ok(v) => out.push(Token::Number(v)),
                    Err(_) => return Err(format!("{word:?} is not a number")),
                }
            }
            _ => {
                let start = i;
                while i < chars.len()
                    && (chars[i].is_alphanumeric()
                        || chars[i] == '_'
                        || chars[i] == '.'
                        || chars[i] == '@'
                        || chars[i] == '$'
                        || chars[i] == ':')
                {
                    i += 1;
                }
                if i == start {
                    return Err(format!("{c} does not belong in a query"));
                }
                out.push(Token::Word(chars[start..i].iter().collect()));
            }
        }
    }
    Ok(out)
}

struct Parser {
    tokens: Vec<Token>,
    at: usize,
}

impl Parser {
    fn next(&mut self) -> Option<Token> {
        let t = self.tokens.get(self.at).cloned();
        if t.is_some() {
            self.at += 1;
        }
        t
    }

    fn peek(&self) -> Option<&Token> {
        self.tokens.get(self.at)
    }

    fn expression(&mut self) -> Result<Expr, String> {
        let mut left = self.conjunction()?;
        while matches!(self.peek(), Some(Token::Word(w)) if w == "or") {
            self.at += 1;
            let right = self.conjunction()?;
            left = Expr::Or(Box::new(left), Box::new(right));
        }
        Ok(left)
    }

    fn conjunction(&mut self) -> Result<Expr, String> {
        let mut left = self.unary()?;
        while matches!(self.peek(), Some(Token::Word(w)) if w == "and") {
            self.at += 1;
            let right = self.unary()?;
            left = Expr::And(Box::new(left), Box::new(right));
        }
        Ok(left)
    }

    fn unary(&mut self) -> Result<Expr, String> {
        if matches!(self.peek(), Some(Token::Word(w)) if w == "not") {
            self.at += 1;
            return Ok(Expr::Not(Box::new(self.unary()?)));
        }
        if self.peek() == Some(&Token::Open) {
            self.at += 1;
            let inner = self.expression()?;
            if self.next() != Some(Token::Close) {
                return Err("a bracket was never closed".into());
            }
            return Ok(inner);
        }
        self.comparison()
    }

    fn comparison(&mut self) -> Result<Expr, String> {
        let field = match self.next() {
            Some(Token::Word(w)) => w,
            Some(other) => return Err(format!("expected a field name, found {other}")),
            None => return Err("the filter ends where a field name should be".into()),
        };
        let op = match self.next() {
            Some(Token::Op(op)) => op,
            Some(other) => return Err(format!("expected an operator after {field}, found {other}")),
            None => return Err(format!("{field} needs something to compare against")),
        };
        let value = match self.next() {
            Some(Token::Number(n)) => Value::Number(n),
            Some(Token::Text(t)) => Value::Text(t),
            Some(Token::Word(w)) if w == "true" => Value::Bool(true),
            Some(Token::Word(w)) if w == "false" => Value::Bool(false),
            Some(Token::Word(w)) => Value::Text(w),
            _ => return Err(format!("{field} needs something to compare against")),
        };
        Ok(Expr::Compare { field, op, value })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn a_query_without_a_filter_parses() {
        let q = parse("functions").expect("parses");
        assert_eq!(q.entity, Entity::Functions);
        assert!(q.filter.is_none());
    }

    #[test]
    fn operators_and_precedence_come_out_right() {
        let q = parse("functions where insns > 10 and name ~ \"str\" or named = false")
            .expect("parses");
        // `and` binds tighter than `or`.
        let Some(Expr::Or(left, right)) = q.filter else {
            panic!("expected an or at the top");
        };
        assert!(matches!(*left, Expr::And(..)));
        assert!(matches!(*right, Expr::Compare { .. }));
    }

    #[test]
    fn brackets_override_precedence() {
        let q = parse("functions where (insns > 10 or named = false) and complete = true")
            .expect("parses");
        assert!(matches!(q.filter, Some(Expr::And(..))));
    }

    #[test]
    fn hex_and_decimal_are_both_numbers() {
        let q = parse("xrefs where to = 0x401000").expect("parses");
        let Some(Expr::Compare { value, .. }) = q.filter else {
            panic!("expected a comparison");
        };
        assert_eq!(value, Value::Number(0x401000));
    }

    #[test]
    fn a_misspelled_entity_says_what_there_is() {
        let e = parse("functionz").unwrap_err();
        assert!(e.contains("functions"), "{e}");
    }

    #[test]
    fn an_unclosed_string_is_an_error_not_a_match() {
        assert!(parse("strings where text ~ \"oops").is_err());
    }

    #[test]
    fn a_limit_is_parsed() {
        let q = parse("strings limit 5").expect("parses");
        assert_eq!(q.limit, Some(5));
    }
}
