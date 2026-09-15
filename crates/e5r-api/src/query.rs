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
//! Every field has a kind: a number, an address, text, or true and false.
//! Text takes any literal, because comparing it against a number or a bool is
//! a search for the characters they print as. The other kinds are narrow, so a
//! number compared against a word is a mistake in the query and is reported as
//! one rather than quietly returning nothing.
//!
//! Two of the entities are questions about dataflow rather than about a table,
//! and they are the reason this language exists rather than a filter over a
//! listing. A call site knows what it hands over, so it can be asked:
//!
//! ```text
//! calls to "memcpy" where arg3 is not bounded
//! calls to "memcpy" where arg3 is bounded
//! calls where target is indirect
//! calls to "strcpy"
//! functions where reads any argument of a call to "system"
//! values reaching arg1 of calls to "system"
//! ```
//!
//! `is not bounded` covers two different answers and the row says which: a
//! value the code constrains nowhere is `unconstrained`, and one the analysis
//! could not follow is `unknown`. They are never printed as each other, which
//! is the whole point of asking. `crate::dataflow` decides them and explains
//! how.

use std::collections::{BTreeMap, BTreeSet};
use std::fmt;

use e5r_analysis::{Program, XrefKind};
use e5r_core::Addr;

use crate::dataflow::{self, ArgumentFact, Basis, CallSite, Source, Verdict};

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
    /// Call sites, with what each one hands over.
    Calls,
    /// The values that reach one argument of a call.
    Values,
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
            Entity::Calls => "calls",
            Entity::Values => "values",
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
            Entity::Calls => &[
                "address", "function", "target", "indirect", "argument", "verdict", "bound",
                "basis", "source", "strength",
            ],
            Entity::Values => &[
                "address", "function", "argument", "source", "detail", "strength",
            ],
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
            "calls" => Entity::Calls,
            "values" => Entity::Values,
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
    /// The callee a `calls to "name"` query is about.
    pub target: Option<String>,
    /// The argument a `values reaching argN` query is about, counting from
    /// zero.
    pub argument: Option<usize>,
}

impl Query {
    /// Whether the filter asks this entity something it can answer.
    ///
    /// Separate from parsing because it is a different kind of mistake: the
    /// text was a query, but `strings` have no `arg3`. Separate from running
    /// because a caller with no program loaded, such as a prompt checking a
    /// line as it is typed, can still be told about it.
    pub fn validate(&self) -> Result<(), String> {
        match &self.filter {
            Some(filter) => check(filter, self.entity),
            None => Ok(()),
        }
    }
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
    /// A question about what the code does with a value.
    Fact(Fact),
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

/// A question a table cannot answer, asked of the dataflow instead.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Fact {
    /// `arg3 is bounded`, and the rest of the forms `is` takes.
    Argument {
        /// Which argument, counting from zero: `arg1` is zero.
        index: usize,
        /// What is being asked about it.
        want: Want,
    },
    /// `target is indirect`, or `target is direct`.
    Indirect(bool),
    /// `reads any argument of a call to "system"`.
    Reads {
        /// True for `every`, false for `any`.
        every: bool,
        /// The callee.
        callee: String,
    },
}

/// What `argN is ...` asks.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Want {
    /// A constant bound the code establishes.
    Bounded,
    /// A bound that is in the instruction.
    Constant,
    /// Proved to exceed any bound on some path.
    Unconstrained,
    /// No bound established, which is not the same claim.
    Unknown,
}

impl Want {
    /// The word it is written as.
    fn parse(word: &str) -> Option<Want> {
        Some(match word {
            "bounded" => Want::Bounded,
            "constant" => Want::Constant,
            "unconstrained" => Want::Unconstrained,
            "unknown" => Want::Unknown,
            _ => return None,
        })
    }
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

impl Op {
    /// The symbol it is written as, so an error can quote the query back.
    pub fn as_str(self) -> &'static str {
        match self {
            Op::Eq => "=",
            Op::Ne => "!=",
            Op::Lt => "<",
            Op::Le => "<=",
            Op::Gt => ">",
            Op::Ge => ">=",
            Op::Contains => "~",
            Op::Omits => "!~",
        }
    }
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

impl Value {
    /// How an error message writes it back.
    fn describe(&self) -> String {
        match self {
            Value::Number(n) => n.to_string(),
            Value::Text(t) => format!("{t:?}"),
            Value::Bool(b) => b.to_string(),
        }
    }
}

/// What kind of value a field holds.
///
/// A field's kind is what makes `insns > "large"` a mistake in the query
/// rather than a filter that matches nothing, which is the difference between
/// being told about a typo and believing an empty answer.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Kind {
    /// A count, a size or a length.
    Number,
    /// An address, which is a number written in hex.
    Address,
    /// Text.
    Text,
    /// True or false.
    Bool,
}

impl Kind {
    /// The phrase an error message uses for it.
    fn as_str(self) -> &'static str {
        match self {
            Kind::Number => "a number",
            Kind::Address => "an address",
            Kind::Text => "text",
            Kind::Bool => "true or false",
        }
    }
}

/// The kind of one field.
///
/// Keyed by name rather than by entity, because a name means the same thing
/// wherever it appears: `size` is a size in a symbol and in a section. A test
/// checks the table against the rows the entities actually build, so it cannot
/// drift away from them.
fn field_kind(field: &str) -> Kind {
    match field {
        "address" | "from" | "to" => Kind::Address,
        "size" | "blocks" | "insns" | "length" | "callers" | "callees" => Kind::Number,
        "complete" | "named" | "exec" | "write" | "dynamic" | "indirect" => Kind::Bool,
        _ => Kind::Text,
    }
}

/// Whether a number was written with quotes around it.
fn looks_numeric(text: &str) -> bool {
    let cleaned = text.replace('_', "");
    match cleaned.strip_prefix("0x") {
        Some(hex) => u64::from_str_radix(hex, 16).is_ok(),
        None => cleaned.parse::<u64>().is_ok(),
    }
}

/// Whether this literal is a sensible thing to compare this field against.
///
/// Text takes anything, since a number or a bool compared against text is a
/// search for the characters it prints as, which is what `kind = call` means.
/// The other kinds are narrow, and say so.
fn check_value(field: &str, op: Op, value: &Value) -> Result<(), String> {
    let kind = field_kind(field);
    match kind {
        Kind::Text => Ok(()),
        Kind::Number | Kind::Address => {
            if matches!(op, Op::Contains | Op::Omits) {
                return Err(format!(
                    "`{field}` is {}, and `{}` searches text; compare it with =, !=, <, <=, > or >=",
                    kind.as_str(),
                    op.as_str()
                ));
            }
            match value {
                Value::Number(_) => Ok(()),
                Value::Text(t) if looks_numeric(t) => Err(format!(
                    "`{field}` is {}, and {t:?} is quoted; write `{field} {} {t}`",
                    kind.as_str(),
                    op.as_str()
                )),
                _ => Err(format!(
                    "`{field}` is {}, and {} is not one",
                    kind.as_str(),
                    value.describe()
                )),
            }
        }
        Kind::Bool => match (op, value) {
            (Op::Eq | Op::Ne, Value::Bool(_)) => Ok(()),
            (Op::Eq | Op::Ne, _) => Err(format!(
                "`{field}` is true or false, and {} is neither; write `{field} = true`",
                value.describe()
            )),
            _ => Err(format!(
                "`{field}` is true or false, and `{}` cannot compare it; \
                 write `{field} = true` or `{field} != true`",
                op.as_str()
            )),
        },
    }
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
    // A field that does not exist is a typo, and a query with one should say
    // so rather than match nothing.
    query.validate()?;
    let mut rows = match query.entity {
        Entity::Calls | Entity::Values => dataflow_rows(p, &query),
        _ => {
            let reads = reads_sets(p, query.filter.as_ref());
            let context = Context {
                site: None,
                reads: &reads,
            };
            let mut rows = collect(p, query.entity);
            if let Some(filter) = &query.filter {
                rows.retain(|row| matches(row, &context, filter));
            }
            rows
        }
    };
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

/// The rows of a query about what a call hands over.
///
/// One row per call per argument the query asked about, because a question
/// about two arguments has two answers and folding them into one row would
/// have to drop one. A query that names no argument gets one row per call.
fn dataflow_rows(p: &Program, query: &Query) -> Vec<Row> {
    let sites = sites(p, query);
    let reads = reads_sets(p, query.filter.as_ref());
    let wanted = referenced(query.filter.as_ref());

    let mut rows = Vec::new();
    for site in &sites {
        // A question about a third argument is a question about calls that
        // have one; without this a call taking two would match `arg3 is not
        // bounded` by having no third argument at all.
        if !wanted.iter().all(|i| site.argument(*i).is_some()) {
            continue;
        }
        if let Some(filter) = &query.filter {
            let context = Context {
                site: Some(site),
                reads: &reads,
            };
            if !matches(&call_row(site, None), &context, filter) {
                continue;
            }
        }
        match query.entity {
            Entity::Values => {
                let Some(index) = query.argument else {
                    continue;
                };
                let Some(argument) = site.argument(index) else {
                    continue;
                };
                for source in &argument.sources {
                    rows.push(value_row(site, argument, source));
                }
            }
            _ if wanted.is_empty() => rows.push(call_row(site, None)),
            _ => {
                for index in &wanted {
                    rows.push(call_row(site, site.argument(*index)));
                }
            }
        }
    }
    rows
}

/// The call sites a query is about.
///
/// Naming the callee turns the question into a lookup: the cross references
/// say which functions call it, and only those are lifted. Without a name
/// every function has to be looked at, because an indirect call is not in any
/// callee's reference list.
fn sites(p: &Program, query: &Query) -> Vec<CallSite> {
    match &query.target {
        Some(name) => dataflow::call_sites_to(p, name),
        None => dataflow::call_sites(p),
    }
}

/// The arguments a filter asks about, in order.
fn referenced(filter: Option<&Expr>) -> Vec<usize> {
    let mut out = Vec::new();
    fn walk(e: &Expr, out: &mut Vec<usize>) {
        match e {
            Expr::And(a, b) | Expr::Or(a, b) => {
                walk(a, out);
                walk(b, out);
            }
            Expr::Not(a) => walk(a, out),
            Expr::Fact(Fact::Argument { index, .. }) if !out.contains(index) => out.push(*index),
            _ => {}
        }
    }
    if let Some(e) = filter {
        walk(e, &mut out);
    }
    out.sort_unstable();
    out
}

/// One call, described for the argument the query asked about.
fn call_row(site: &CallSite, argument: Option<&ArgumentFact>) -> Row {
    let strength = match argument {
        Some(a) => a.strength,
        // With no argument in question the row's claim is about who is being
        // called, so that is the strength it carries.
        None => site.target_strength,
    };
    Row {
        values: vec![
            ("address", Field::Address(site.at)),
            ("function", Field::Text(site.caller_name.clone())),
            ("target", Field::Text(site.target_text())),
            ("indirect", Field::Bool(site.indirect)),
            (
                "argument",
                match argument {
                    Some(a) => Field::Text(a.name()),
                    None => Field::Missing,
                },
            ),
            (
                "verdict",
                match argument {
                    Some(a) => Field::Text(a.verdict.as_str().to_string()),
                    None => Field::Missing,
                },
            ),
            (
                "bound",
                match argument.and_then(|a| a.bound_text()) {
                    Some(b) => Field::Text(b),
                    None => Field::Missing,
                },
            ),
            (
                "basis",
                match argument {
                    Some(a) => Field::Text(a.basis.as_str().to_string()),
                    None => Field::Missing,
                },
            ),
            (
                "source",
                match argument {
                    Some(a) => Field::Text(a.source_text()),
                    None => Field::Missing,
                },
            ),
            ("strength", Field::Text(strength.as_str().to_string())),
        ],
    }
}

/// One value that reaches one argument.
fn value_row(site: &CallSite, argument: &ArgumentFact, source: &Source) -> Row {
    Row {
        values: vec![
            ("address", Field::Address(site.at)),
            ("function", Field::Text(site.caller_name.clone())),
            ("argument", Field::Text(argument.name())),
            ("source", Field::Text(kind_of(source).to_string())),
            ("detail", Field::Text(source.describe())),
            (
                "strength",
                Field::Text(source.strength().as_str().to_string()),
            ),
        ],
    }
}

/// The one word that says what kind of source it is.
fn kind_of(source: &Source) -> &'static str {
    match source {
        Source::Constant { text: Some(_), .. } => "string",
        Source::Constant {
            symbol: Some(_), ..
        } => "address",
        Source::Constant { .. } => "literal",
        Source::Caller { .. } => "argument",
        Source::Frame { .. } => "frame",
        Source::Memory { .. } => "memory",
        Source::Result { .. } => "result",
        Source::Clobbered => "clobbered",
        Source::Computed { .. } => "computed",
        Source::Nothing => "nothing",
    }
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

    // `values reaching arg1 of calls`: which value, of which call. The clause
    // is what makes the question answerable, so it is required rather than
    // defaulted to the first argument of everything.
    let argument = match entity {
        Entity::Values => Some(parser.reaching()?),
        _ => None,
    };
    // `calls to "memcpy"`: sugar for a comparison against the target, except
    // that it also matches the import thunk that stands in for it.
    let mut target = None;
    if matches!(entity, Entity::Calls | Entity::Values)
        && matches!(parser.peek(), Some(Token::Word(w)) if w == "to")
    {
        parser.at += 1;
        target = Some(parser.name("`to` wants the name of what is called")?);
    }

    let mut filter = None;
    let mut limit = None;
    while let Some(token) = parser.next() {
        match token {
            Token::Word(w) if w == "where" => {
                // A bare `where` is a half-typed query, not a query with an
                // empty filter that matches everything.
                if parser.peek().is_none() {
                    return Err("`where` wants a filter and this query ends after it; \
                         try `where insns > 100`"
                        .into());
                }
                filter = Some(parser.expression()?)
            }
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
        target,
        argument,
    })
}

fn check(e: &Expr, entity: Entity) -> Result<(), String> {
    match e {
        Expr::And(a, b) | Expr::Or(a, b) => {
            check(a, entity)?;
            check(b, entity)
        }
        Expr::Not(a) => check(a, entity),
        // A dataflow question asked of the wrong thing is a mistake in the
        // query, and saying which thing does answer it is more use than a
        // list of fields.
        Expr::Fact(Fact::Argument { .. } | Fact::Indirect(_)) => {
            if matches!(entity, Entity::Calls | Entity::Values) {
                Ok(())
            } else {
                Err(format!(
                    "an argument and a target belong to a call, and {} are not calls; \
                     try `calls to \"memcpy\" where arg3 is not bounded`",
                    entity.as_str()
                ))
            }
        }
        Expr::Fact(Fact::Reads { .. }) => {
            if entity == Entity::Functions {
                Ok(())
            } else {
                Err(format!(
                    "`reads` asks what a function does, and {} are not functions; \
                     try `functions where reads any argument of a call to \"system\"`",
                    entity.as_str()
                ))
            }
        }
        Expr::Compare { field, op, value } => {
            if !entity.fields().contains(&field.as_str()) {
                return Err(format!(
                    "{} have no field {field:?}; they have {}",
                    entity.as_str(),
                    entity.fields().join(", ")
                ));
            }
            check_value(field, *op, value)
        }
    }
}

fn matches(row: &Row, context: &Context<'_>, e: &Expr) -> bool {
    match e {
        Expr::And(a, b) => matches(row, context, a) && matches(row, context, b),
        Expr::Or(a, b) => matches(row, context, a) || matches(row, context, b),
        Expr::Not(a) => !matches(row, context, a),
        Expr::Fact(fact) => context.holds(row, fact),
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
///
/// The two dataflow entities are not here: their rows come from lifting the
/// functions a query is about rather than from a table, which is what
/// `dataflow_rows` does.
fn collect(p: &Program, entity: Entity) -> Vec<Row> {
    match entity {
        Entity::Calls | Entity::Values => Vec::new(),
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

/// What a fact needs that a row does not carry.
struct Context<'a> {
    /// The call the row describes, when it describes one.
    site: Option<&'a CallSite>,
    /// Which functions satisfy each `reads` fact, worked out once.
    reads: &'a BTreeMap<(String, bool), BTreeSet<Addr>>,
}

impl Context<'_> {
    /// Whether a fact holds of what this row describes.
    fn holds(&self, row: &Row, fact: &Fact) -> bool {
        match fact {
            Fact::Argument { index, want } => {
                let Some(argument) = self.site.and_then(|s| s.argument(*index)) else {
                    return false;
                };
                match want {
                    Want::Bounded => argument.verdict == Verdict::Bounded,
                    // A constant is a bound that needed no analysis to find.
                    Want::Constant => {
                        argument.verdict == Verdict::Bounded && argument.basis == Basis::Literal
                    }
                    Want::Unconstrained => argument.verdict == Verdict::Unconstrained,
                    Want::Unknown => argument.verdict == Verdict::Unknown,
                }
            }
            Fact::Indirect(want) => self.site.is_some_and(|s| s.indirect == *want),
            Fact::Reads { every, callee } => {
                let Some(Field::Address(at)) = row.get("address") else {
                    return false;
                };
                self.reads
                    .get(&(callee.clone(), *every))
                    .is_some_and(|set| set.contains(at))
            }
        }
    }
}

/// The functions each `reads` fact in a filter is true of.
///
/// Worked out once per query rather than per function: the answer needs the
/// call sites of every function that calls the named callee, and that set is
/// the same whichever function the filter is being tested against.
fn reads_sets(p: &Program, filter: Option<&Expr>) -> BTreeMap<(String, bool), BTreeSet<Addr>> {
    let mut wanted: Vec<(String, bool)> = Vec::new();
    fn walk(e: &Expr, out: &mut Vec<(String, bool)>) {
        match e {
            Expr::And(a, b) | Expr::Or(a, b) => {
                walk(a, out);
                walk(b, out);
            }
            Expr::Not(a) => walk(a, out),
            Expr::Fact(Fact::Reads { every, callee }) => {
                let key = (callee.clone(), *every);
                if !out.contains(&key) {
                    out.push(key);
                }
            }
            _ => {}
        }
    }
    if let Some(e) = filter {
        walk(e, &mut wanted);
    }
    let mut out = BTreeMap::new();
    for (callee, every) in wanted {
        let set = reads_set(p, &callee, every);
        out.insert((callee, every), set);
    }
    out
}

/// The functions that hand a call to `callee` something they read.
///
/// A literal is not read, whatever it addresses: a command built from a string
/// in the image is the program's own, and a command that arrived from
/// somewhere else is the one worth looking at.
fn reads_set(p: &Program, callee: &str, every: bool) -> BTreeSet<Addr> {
    let sites = dataflow::call_sites_to(p, callee);
    let mut out = BTreeSet::new();
    for site in &sites {
        if site.arguments.is_empty() {
            continue;
        }
        let read = |a: &ArgumentFact| a.sources.iter().any(|s| s.is_read());
        let hit = if every {
            site.arguments.iter().all(read)
        } else {
            site.arguments.iter().any(read)
        };
        if hit {
            out.insert(site.caller);
        }
    }
    out
}

/// The argument a word like `arg3` names, counting from zero.
fn argument_index(word: &str) -> Option<usize> {
    let n: usize = word.strip_prefix("arg")?.parse().ok()?;
    // `arg0` is nobody's first argument, and a number past what any
    // convention passes in registers is a typo rather than a question.
    (1..=64).contains(&n).then_some(n - 1)
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
            Token::Op(op) => f.write_str(op.as_str()),
            Token::Open => f.write_str("("),
            Token::Close => f.write_str(")"),
        }
    }
}

/// A token as an error message names it.
fn found(token: Option<&Token>) -> String {
    match token {
        Some(t) => format!("{t}"),
        None => "the end of the query".to_string(),
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
                    // Naming the text makes it obvious which quote was lost,
                    // which a query with several of them needs.
                    let rest: String = chars[start..].iter().collect();
                    return Err(format!(
                        "a quoted string was never closed: {quote}{rest} has no closing {quote}"
                    ));
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

    fn peek_at(&self, n: usize) -> Option<&Token> {
        self.tokens.get(self.at + n)
    }

    /// The next token as a name, quoted or not.
    fn name(&mut self, wanted: &str) -> Result<String, String> {
        match self.next() {
            Some(Token::Text(t)) | Some(Token::Word(t)) => Ok(t),
            other => Err(format!("{wanted}, not {}", found(other.as_ref()))),
        }
    }

    /// One expected word, for the fixed parts of a clause.
    fn word(&mut self, wanted: &str, hint: &str) -> Result<(), String> {
        match self.next() {
            Some(Token::Word(w)) if w == wanted => Ok(()),
            other => Err(format!(
                "expected `{wanted}` here, found {}; {hint}",
                found(other.as_ref())
            )),
        }
    }

    /// The `reaching argN of calls` a `values` query begins with.
    fn reaching(&mut self) -> Result<usize, String> {
        const HINT: &str = "a value query reads `values reaching arg1 of calls to \"system\"`";
        self.word("reaching", HINT)?;
        let index = match self.next() {
            Some(Token::Word(w)) => argument_index(&w).ok_or_else(|| {
                format!("{w:?} does not name an argument; they are arg1, arg2 and so on")
            })?,
            other => {
                return Err(format!(
                    "expected an argument such as `arg1`, found {}; {HINT}",
                    found(other.as_ref())
                ));
            }
        };
        self.word("of", HINT)?;
        self.word("calls", HINT)?;
        Ok(index)
    }

    /// A question about dataflow, when that is what comes next.
    ///
    /// Recognized by shape rather than by a keyword list, so `target` and
    /// `argument` are still ordinary fields when they are compared rather than
    /// asked about.
    fn fact(&mut self) -> Result<Option<Expr>, String> {
        let Some(Token::Word(head)) = self.peek().cloned() else {
            return Ok(None);
        };
        if head == "reads" {
            self.at += 1;
            return self.reads().map(Some);
        }
        let is_next = matches!(self.peek_at(1), Some(Token::Word(w)) if w == "is");
        if !is_next {
            return Ok(None);
        }
        if head != "target" && argument_index(&head).is_none() {
            return Ok(None);
        }
        self.at += 2;
        let negated = matches!(self.peek(), Some(Token::Word(w)) if w == "not");
        if negated {
            self.at += 1;
        }
        let word = match self.next() {
            Some(Token::Word(w)) => w,
            other => {
                return Err(format!(
                    "`{head} is` wants a word such as bounded, unconstrained, unknown, \
                     constant, direct or indirect, found {}",
                    found(other.as_ref())
                ));
            }
        };
        let fact = if head == "target" {
            match word.as_str() {
                "indirect" => Fact::Indirect(true),
                "direct" => Fact::Indirect(false),
                _ => {
                    return Err(format!("a target is `direct` or `indirect`, not {word:?}"));
                }
            }
        } else {
            let index = argument_index(&head).unwrap_or_default();
            let want = Want::parse(&word).ok_or_else(|| {
                format!(
                    "did not understand `{head} is {word}`; an argument is bounded, \
                     constant, unconstrained or unknown"
                )
            })?;
            Fact::Argument { index, want }
        };
        let expr = Expr::Fact(fact);
        // `is not bounded` is the negation and nothing more: it covers both
        // ways of not being bounded, and the row says which one this is.
        Ok(Some(if negated {
            Expr::Not(Box::new(expr))
        } else {
            expr
        }))
    }

    /// `reads any argument of a call to "system"`.
    fn reads(&mut self) -> Result<Expr, String> {
        const HINT: &str = "it reads `reads any argument of a call to \"system\"`";
        let every = match self.next() {
            Some(Token::Word(w)) if w == "any" => false,
            Some(Token::Word(w)) if w == "every" => true,
            other => {
                return Err(format!(
                    "`reads` wants `any` or `every`, found {}; {HINT}",
                    found(other.as_ref())
                ));
            }
        };
        match self.next() {
            Some(Token::Word(w)) if w == "argument" || w == "arguments" => {}
            other => {
                return Err(format!(
                    "expected `argument` here, found {}; {HINT}",
                    found(other.as_ref())
                ));
            }
        }
        self.word("of", HINT)?;
        if matches!(self.peek(), Some(Token::Word(w)) if w == "a") {
            self.at += 1;
        }
        match self.next() {
            Some(Token::Word(w)) if w == "call" || w == "calls" => {}
            other => {
                return Err(format!(
                    "expected `call` here, found {}; {HINT}",
                    found(other.as_ref())
                ));
            }
        }
        self.word("to", HINT)?;
        let callee = self.name("a call is to something named")?;
        Ok(Expr::Fact(Fact::Reads { every, callee }))
    }

    fn expression(&mut self) -> Result<Expr, String> {
        let mut left = self.conjunction()?;
        while matches!(self.peek(), Some(Token::Word(w)) if w == "or") {
            self.at += 1;
            // Naming the operator that was left dangling beats reporting the
            // missing field name, which the reader did not write.
            if self.peek().is_none() {
                return Err("`or` wants another condition after it".into());
            }
            let right = self.conjunction()?;
            left = Expr::Or(Box::new(left), Box::new(right));
        }
        Ok(left)
    }

    fn conjunction(&mut self) -> Result<Expr, String> {
        let mut left = self.unary()?;
        while matches!(self.peek(), Some(Token::Word(w)) if w == "and") {
            self.at += 1;
            if self.peek().is_none() {
                return Err("`and` wants another condition after it".into());
            }
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
        if let Some(fact) = self.fact()? {
            return Ok(fact);
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
            Some(other) => {
                return Err(format!("expected an operator after {field}, found {other}"));
            }
            None => {
                return Err(format!(
                    "`{field}` needs an operator such as = or > and something to compare against"
                ));
            }
        };
        let value = match self.next() {
            Some(Token::Number(n)) => Value::Number(n),
            Some(Token::Text(t)) => Value::Text(t),
            Some(Token::Word(w)) if w == "true" => Value::Bool(true),
            Some(Token::Word(w)) if w == "false" => Value::Bool(false),
            Some(Token::Word(w)) => Value::Text(w),
            Some(other) => {
                return Err(format!(
                    "`{field} {}` cannot be compared against {other}",
                    op.as_str()
                ));
            }
            None => {
                return Err(format!(
                    "`{field} {}` needs something to compare against",
                    op.as_str()
                ));
            }
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

    #[test]
    fn a_call_query_names_its_callee() {
        let q = parse("calls to \"memcpy\" limit 3").expect("parses");
        assert_eq!(q.entity, Entity::Calls);
        assert_eq!(q.target.as_deref(), Some("memcpy"));
        assert_eq!(q.limit, Some(3));
    }

    #[test]
    fn an_argument_question_is_not_a_comparison() {
        let q = parse("calls to \"memcpy\" where arg3 is not bounded").expect("parses");
        // `arg1` is the first argument, so the third is index two.
        let Some(Expr::Not(inner)) = q.filter else {
            panic!("expected a negation at the top");
        };
        assert!(matches!(
            *inner,
            Expr::Fact(Fact::Argument {
                index: 2,
                want: Want::Bounded
            })
        ));
    }

    #[test]
    fn the_proved_form_is_its_own_question() {
        let q = parse("calls where arg3 is unconstrained").expect("parses");
        assert!(matches!(
            q.filter,
            Some(Expr::Fact(Fact::Argument {
                index: 2,
                want: Want::Unconstrained
            }))
        ));
    }

    #[test]
    fn a_target_can_be_asked_how_it_is_reached() {
        let q = parse("calls where target is indirect").expect("parses");
        assert!(matches!(q.filter, Some(Expr::Fact(Fact::Indirect(true)))));
        let q = parse("calls where target is not indirect").expect("parses");
        assert!(matches!(q.filter, Some(Expr::Not(_))));
    }

    #[test]
    fn a_value_query_says_which_value_of_which_call() {
        let q = parse("values reaching arg1 of calls to \"system\"").expect("parses");
        assert_eq!(q.entity, Entity::Values);
        assert_eq!(q.argument, Some(0));
        assert_eq!(q.target.as_deref(), Some("system"));
    }

    #[test]
    fn a_function_can_be_asked_what_it_hands_to_a_call() {
        let q =
            parse("functions where reads any argument of a call to \"system\"").expect("parses");
        assert!(matches!(
            q.filter,
            Some(Expr::Fact(Fact::Reads { every: false, .. }))
        ));
        let q =
            parse("functions where reads every argument of a call to \"system\"").expect("parses");
        assert!(matches!(
            q.filter,
            Some(Expr::Fact(Fact::Reads { every: true, .. }))
        ));
    }

    #[test]
    fn there_is_no_argument_zero() {
        assert_eq!(argument_index("arg1"), Some(0));
        assert_eq!(argument_index("arg3"), Some(2));
        assert_eq!(argument_index("arg0"), None);
        assert_eq!(argument_index("argument"), None);
        assert_eq!(argument_index("arg99999999999999999999"), None);
    }

    #[test]
    fn a_number_compared_against_a_word_is_a_mistake_not_an_empty_answer() {
        let q = parse("functions where insns > large").expect("parses");
        let e = check(q.filter.as_ref().expect("a filter"), Entity::Functions).unwrap_err();
        assert!(e.contains("insns") && e.contains("large"), "{e}");
    }

    #[test]
    fn a_quoted_number_says_it_is_quoted() {
        let q = parse("functions where insns > \"100\"").expect("parses");
        let e = check(q.filter.as_ref().expect("a filter"), Entity::Functions).unwrap_err();
        assert!(e.contains("quoted"), "{e}");
        assert!(e.contains("insns > 100"), "{e}");
    }

    #[test]
    fn text_still_takes_any_literal() {
        // `kind = call` and `name ~ 64` are searches for what the literal
        // prints as, which is the one coercion worth keeping.
        for text in ["xrefs where kind = call", "functions where name ~ 64"] {
            let q = parse(text).expect("parses");
            let entity = q.entity;
            check(q.filter.as_ref().expect("a filter"), entity).unwrap_or_else(|e| panic!("{e}"));
        }
    }

    #[test]
    fn a_flag_is_compared_against_true_or_false_and_nothing_else() {
        let q = parse("sections where exec = 3").expect("parses");
        let e = check(q.filter.as_ref().expect("a filter"), Entity::Sections).unwrap_err();
        assert!(e.contains("exec") && e.contains("true"), "{e}");
        // Ordering a flag is not a question, whatever it is compared against.
        let q = parse("sections where exec > true").expect("parses");
        assert!(check(q.filter.as_ref().expect("a filter"), Entity::Sections).is_err());
    }

    #[test]
    fn searching_a_number_for_text_is_refused() {
        let q = parse("functions where insns ~ 10").expect("parses");
        let e = check(q.filter.as_ref().expect("a filter"), Entity::Functions).unwrap_err();
        assert!(e.contains("insns") && e.contains('~'), "{e}");
    }

    #[test]
    fn a_bare_where_asks_for_a_filter() {
        let e = parse("functions where").unwrap_err();
        assert!(e.contains("where"), "{e}");
    }

    #[test]
    fn a_trailing_operator_names_the_field_it_left_hanging() {
        let e = parse("functions where insns >").unwrap_err();
        assert!(e.contains("insns >"), "{e}");
    }

    #[test]
    fn an_unclosed_quote_shows_the_text_it_swallowed() {
        let e = parse("strings where text ~ \"oops").unwrap_err();
        assert!(e.contains("oops"), "{e}");
    }

    #[test]
    fn a_dataflow_question_asked_of_the_wrong_thing_says_which_thing_answers_it() {
        let q = parse("strings where arg3 is bounded").expect("parses");
        let e = check(q.filter.as_ref().expect("a filter"), Entity::Strings).unwrap_err();
        assert!(e.contains("calls"), "{e}");
    }
}
