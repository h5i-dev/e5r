//! The SLEIGH preprocessor: `@include`, `@define`, `@if` and `$(name)`.
//!
//! It runs before the lexer and is line oriented, as the language specifies:
//! a directive owns its whole line, and everything else is subject to
//! `$(name)` substitution and then handed on. The output is one flat string
//! plus a map from each emitted line back to the file and line it came from,
//! so that an error thirty thousand lines into a preprocessed x86
//! specification still names `ia.sinc` and a line the author can open.
//!
//! Reference: the SLEIGH manual, "3. Preprocessing".

use std::collections::HashMap;
use std::path::{Path, PathBuf};
use std::sync::Arc;

use crate::error::{Error, Limits, Location, Result};

/// Where the preprocessor gets file contents.
///
/// Reading from disk is only one answer; a test wants an in-memory tree and a
/// caller embedding a specification wants its own. Paths handed to `load` are
/// already resolved against the including file's directory.
pub trait Loader {
    /// Read one file whole.
    fn load(&mut self, path: &Path) -> Result<String>;
}

/// Reads from the filesystem, refusing anything over the byte limit.
#[derive(Debug, Clone)]
pub struct FileLoader {
    /// The largest file that will be read.
    pub max_bytes: usize,
}

impl Default for FileLoader {
    fn default() -> FileLoader {
        FileLoader {
            max_bytes: Limits::default().file_bytes,
        }
    }
}

impl Loader for FileLoader {
    fn load(&mut self, path: &Path) -> Result<String> {
        // The length is checked before the read so that a named pipe or a
        // multi-gigabyte file cannot be turned into an allocation.
        let meta = std::fs::metadata(path)
            .map_err(|e| Error::new(format!("cannot open {}: {e}", path.display())))?;
        if meta.len() as u128 > self.max_bytes as u128 {
            return Err(Error::new(format!(
                "{} is {} bytes, over the {} byte limit",
                path.display(),
                meta.len(),
                self.max_bytes
            )));
        }
        let bytes = std::fs::read(path)
            .map_err(|e| Error::new(format!("cannot read {}: {e}", path.display())))?;
        Ok(String::from_utf8_lossy(&bytes).into_owned())
    }
}

/// A loader over an in-memory tree, for tests and for embedded specifications.
#[derive(Debug, Clone, Default)]
pub struct MemoryLoader {
    files: HashMap<PathBuf, String>,
}

impl MemoryLoader {
    /// An empty tree.
    pub fn new() -> MemoryLoader {
        MemoryLoader::default()
    }

    /// Add one file.
    pub fn insert(&mut self, path: impl Into<PathBuf>, text: impl Into<String>) {
        self.files.insert(path.into(), text.into());
    }

    /// Add one file, taking ownership back for chaining.
    #[must_use]
    pub fn with(mut self, path: impl Into<PathBuf>, text: impl Into<String>) -> MemoryLoader {
        self.insert(path, text);
        self
    }
}

impl Loader for MemoryLoader {
    fn load(&mut self, path: &Path) -> Result<String> {
        self.files
            .get(path)
            .cloned()
            .ok_or_else(|| Error::new(format!("no such file {}", path.display())))
    }
}

/// The preprocessed text of a whole specification.
#[derive(Debug, Clone, Default)]
pub struct Source {
    text: String,
    line_starts: Vec<usize>,
    origins: Vec<Location>,
    warnings: Vec<String>,
}

impl Source {
    /// The flattened text, which is what the lexer reads.
    pub fn text(&self) -> &str {
        &self.text
    }

    /// The original file and line an offset into [`Source::text`] came from.
    pub fn location(&self, offset: usize) -> Option<Location> {
        if self.origins.is_empty() {
            return None;
        }
        // partition_point rather than a scan: a large specification is a
        // million lines and errors are not rare enough to walk it each time.
        let line = self.line_starts.partition_point(|&s| s <= offset);
        let idx = line.saturating_sub(1).min(self.origins.len() - 1);
        Some(self.origins[idx].clone())
    }

    /// How many lines survived preprocessing.
    pub fn lines(&self) -> usize {
        self.origins.len()
    }

    /// Things that were wrong but not fatal, in the order they were found.
    pub fn warnings(&self) -> &[String] {
        &self.warnings
    }

    fn push(&mut self, text: &str, origin: Location) {
        self.line_starts.push(self.text.len());
        self.origins.push(origin);
        self.text.push_str(text);
        self.text.push('\n');
    }
}

/// One frame of `@if` nesting.
struct Cond {
    /// Whether this frame's own condition currently lets lines through.
    active: bool,
    /// Whether any branch of this frame has already been taken.
    taken: bool,
    /// Whether `@else` has been seen, so a second one is an error.
    closed: bool,
    /// Whether the enclosing frames let this one run at all.
    enclosing: bool,
    /// Where the `@if` was, for the error when it is never closed.
    at: Location,
}

/// Runs the preprocessor over a tree of files.
pub struct Preprocessor<'a> {
    loader: &'a mut dyn Loader,
    limits: Limits,
    defines: HashMap<String, String>,
    out: Source,
    files_read: usize,
}

impl<'a> Preprocessor<'a> {
    /// A preprocessor with no definitions beyond what the source makes.
    pub fn new(loader: &'a mut dyn Loader) -> Preprocessor<'a> {
        Preprocessor {
            loader,
            limits: Limits::default(),
            defines: HashMap::new(),
            out: Source::default(),
            files_read: 0,
        }
    }

    /// Replace the bounds. See [`Limits`].
    #[must_use]
    pub fn with_limits(mut self, limits: Limits) -> Self {
        self.limits = limits;
        self
    }

    /// Predefine a macro, as the command line and the `.ldefs` file do.
    #[must_use]
    pub fn define(mut self, name: impl Into<String>, value: impl Into<String>) -> Self {
        self.defines.insert(name.into(), value.into());
        self
    }

    /// Preprocess `path` and everything it includes.
    pub fn run(mut self, path: &Path) -> Result<Source> {
        let mut conds = Vec::new();
        self.file(path, 0, &mut conds)?;
        // A conditional left open at the very end is a mistake in the
        // specification, but the published corpus contains one and everything
        // after it was still meant to be read the way a stream preprocessor
        // reads it. Say so rather than refusing the file.
        for open in &conds {
            self.out.warnings.push(format!(
                "{}: this @if is never closed by an @endif",
                open.at
            ));
        }
        Ok(self.out)
    }

    /// The definitions in force when preprocessing finished. Exposed because
    /// a caller resolving an `.ldefs` variant wants to know what it got.
    pub fn definitions(&self) -> &HashMap<String, String> {
        &self.defines
    }

    fn file(&mut self, path: &Path, depth: usize, conds: &mut Vec<Cond>) -> Result<()> {
        if depth > self.limits.include_depth {
            return Err(Error::new(format!(
                "@include nests more than {} deep at {}",
                self.limits.include_depth,
                path.display()
            )));
        }
        self.files_read += 1;
        if self.files_read > self.limits.include_files {
            return Err(Error::new(format!(
                "more than {} files included",
                self.limits.include_files
            )));
        }

        let text = self.loader.load(path)?;
        let name: Arc<str> = Arc::from(path.to_string_lossy().into_owned());
        let dir = path.parent().map(Path::to_path_buf).unwrap_or_default();

        for (index, raw) in text.lines().enumerate() {
            let line = u32::try_from(index + 1).unwrap_or(u32::MAX);
            let at = Location {
                file: Arc::clone(&name),
                line,
            };
            if self.out.lines() >= self.limits.total_lines {
                return Err(Error::at(
                    at,
                    format!(
                        "more than {} lines after preprocessing",
                        self.limits.total_lines
                    ),
                ));
            }
            let trimmed = raw.trim_start();
            if let Some(rest) = trimmed.strip_prefix('@') {
                self.directive(rest, &at, &dir, depth, conds)?;
                continue;
            }
            if !conds.iter().all(|c| c.active && c.enclosing) {
                continue;
            }
            if raw.trim().is_empty() {
                // Emitting the blank keeps nothing useful and costs a line of
                // the budget, but dropping it would desynchronise nothing:
                // the origin map is per emitted line, not per input line.
                continue;
            }
            let expanded = self.expand(raw, &at)?;
            self.out.push(&expanded, at);
        }

        Ok(())
    }

    fn directive(
        &mut self,
        rest: &str,
        at: &Location,
        dir: &Path,
        depth: usize,
        conds: &mut Vec<Cond>,
    ) -> Result<()> {
        let rest = strip_comment(rest);
        let rest = rest.trim();
        let (word, args) = split_word(rest);
        let live = conds.iter().all(|c| c.active && c.enclosing);

        match word {
            "if" | "ifdef" | "ifndef" => {
                if conds.len() >= self.limits.condition_depth {
                    return Err(Error::at(
                        at.clone(),
                        format!("@if nests more than {} deep", self.limits.condition_depth),
                    ));
                }
                let value = if !live {
                    false
                } else {
                    match word {
                        "ifdef" => self.defined(args, at)?,
                        "ifndef" => !self.defined(args, at)?,
                        _ => self.condition(args, at)?,
                    }
                };
                conds.push(Cond {
                    active: value,
                    taken: value,
                    closed: false,
                    enclosing: live,
                    at: at.clone(),
                });
            }
            "elif" => {
                let Some(frame) = conds.last_mut() else {
                    return Err(Error::at(at.clone(), "@elif without an @if"));
                };
                if frame.closed {
                    return Err(Error::at(at.clone(), "@elif after @else"));
                }
                let enclosing = frame.enclosing;
                let taken = frame.taken;
                frame.active = false;
                let value = if enclosing && !taken {
                    self.condition(args, at)?
                } else {
                    false
                };
                // Re-borrow: the condition evaluation needed `self` immutably.
                let frame = conds.last_mut().expect("frame still there");
                frame.active = value;
                frame.taken |= value;
            }
            "else" => {
                let Some(frame) = conds.last_mut() else {
                    return Err(Error::at(at.clone(), "@else without an @if"));
                };
                if frame.closed {
                    return Err(Error::at(at.clone(), "a second @else for one @if"));
                }
                frame.closed = true;
                frame.active = !frame.taken;
                frame.taken = true;
            }
            "endif" => {
                if conds.pop().is_none() {
                    return Err(Error::at(at.clone(), "@endif without an @if"));
                }
            }
            "define" if live => {
                let (name, value) = split_word(args);
                if !is_identifier(name) {
                    return Err(Error::at(
                        at.clone(),
                        format!("@define wants an identifier, found {name:?}"),
                    ));
                }
                // The value is stored as written and expanded where it is
                // used, so that a macro may name another defined later.
                self.defines.insert(name.to_string(), unquote(value.trim()));
            }
            "undef" if live => {
                let (name, _) = split_word(args);
                self.defines.remove(name);
            }
            "include" if live => {
                let arg = self.expand(args.trim(), at)?;
                let path = unquote(arg.trim());
                if path.is_empty() {
                    return Err(Error::at(at.clone(), "@include with no file name"));
                }
                // Relative to the including file first, as the language
                // specifies; a bare path is the fallback for a caller whose
                // loader has its own roots.
                let target = if dir.as_os_str().is_empty() {
                    PathBuf::from(&path)
                } else {
                    dir.join(&path)
                };
                match self.file(&target, depth + 1, conds) {
                    Ok(()) => {}
                    Err(first) => {
                        let bare = PathBuf::from(&path);
                        if bare == target {
                            return Err(first.or_at(at));
                        }
                        self.file(&bare, depth + 1, conds)
                            .map_err(|_| first.or_at(at))?;
                    }
                }
            }
            "define" | "undef" | "include" => {}
            "" => return Err(Error::at(at.clone(), "an @ with no directive after it")),
            other if live => {
                return Err(Error::at(
                    at.clone(),
                    format!("unknown preprocessor directive @{other}"),
                ));
            }
            _ => {}
        }
        Ok(())
    }

    fn defined(&self, args: &str, at: &Location) -> Result<bool> {
        let (name, tail) = split_word(args.trim());
        if !is_identifier(name) || !tail.trim().is_empty() {
            return Err(Error::at(
                at.clone(),
                "@ifdef and @ifndef take exactly one identifier",
            ));
        }
        Ok(self.defines.contains_key(name))
    }

    fn condition(&self, text: &str, at: &Location) -> Result<bool> {
        let expanded = self.expand(text, at)?;
        let tokens = cond_tokens(&expanded, at)?;
        let mut p = CondParser {
            tokens: &tokens,
            at: 0,
            defines: &self.defines,
            depth: 0,
            max_depth: self.limits.expr_depth,
        };
        let value = p.or_expr(at)?;
        if p.at != p.tokens.len() {
            return Err(Error::at(
                at.clone(),
                format!("trailing text in an @if condition: {text:?}"),
            ));
        }
        value.as_bool(at)
    }

    /// Substitute every `$(name)`, repeatedly, up to the per-line budget.
    ///
    /// A `#` comment is left alone: the corpus has macros named in prose
    /// before they are defined, and expanding a comment would fail on text
    /// that never reaches the parser.
    fn expand(&self, line: &str, at: &Location) -> Result<String> {
        let body = strip_comment(line);
        if !body.contains("$(") {
            return Ok(line.to_string());
        }
        let comment = &line[body.len()..];
        let mut current = body.to_string();
        for _ in 0..self.limits.expansions_per_line {
            let Some(start) = current.find("$(") else {
                current.push_str(comment);
                return Ok(current);
            };
            let Some(end) = current[start + 2..].find(')') else {
                return Err(Error::at(
                    at.clone(),
                    "a $( macro expansion is never closed by )",
                ));
            };
            let end = start + 2 + end;
            let name = &current[start + 2..end];
            let Some(value) = self.defines.get(name) else {
                return Err(Error::at(
                    at.clone(),
                    format!("$({name}) is not defined at this point"),
                ));
            };
            // Guard the one case that cannot terminate: a macro whose body
            // contains its own invocation.
            if value.contains(&format!("$({name})")) {
                return Err(Error::at(
                    at.clone(),
                    format!("the macro {name} expands to itself"),
                ));
            }
            // The expansion is padded, because the language's own corpus
            // writes `is$(AMODE)` and `export$(X)` and means two tokens. No
            // specification relies on the opposite, gluing an expansion to the
            // word after it.
            let mut next = String::with_capacity(current.len() + value.len() + 2);
            next.push_str(&current[..start]);
            next.push(' ');
            next.push_str(value);
            next.push(' ');
            next.push_str(&current[end + 1..]);
            current = next;
        }
        Err(Error::at(
            at.clone(),
            format!(
                "more than {} macro expansions on one line",
                self.limits.expansions_per_line
            ),
        ))
    }
}

/// A value in a preprocessor condition. Strings and booleans do not mix, which
/// is what makes `@if X == "1" && defined(Y)` parse the way it reads.
enum CondValue {
    Str(String),
    Bool(bool),
}

impl CondValue {
    fn as_bool(&self, at: &Location) -> Result<bool> {
        match self {
            CondValue::Bool(b) => Ok(*b),
            CondValue::Str(s) => Err(Error::at(
                at.clone(),
                format!("{s:?} is a string where a condition is needed"),
            )),
        }
    }

    fn as_str(&self) -> String {
        match self {
            CondValue::Bool(b) => b.to_string(),
            CondValue::Str(s) => s.clone(),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum CondTok {
    Ident(String),
    Str(String),
    Op(&'static str),
}

fn cond_tokens(text: &str, at: &Location) -> Result<Vec<CondTok>> {
    const OPS: [&str; 8] = ["&&", "||", "^^", "==", "!=", "(", ")", "!"];
    let bytes = text.as_bytes();
    let mut out = Vec::new();
    let mut i = 0;
    while i < bytes.len() {
        let c = bytes[i] as char;
        if c.is_ascii_whitespace() {
            i += 1;
            continue;
        }
        if c == '"' {
            let rest = &text[i + 1..];
            let Some(end) = rest.find('"') else {
                return Err(Error::at(at.clone(), "an unterminated string in an @if"));
            };
            out.push(CondTok::Str(rest[..end].to_string()));
            i += end + 2;
            continue;
        }
        if let Some(op) = OPS.iter().find(|op| text[i..].starts_with(**op)) {
            out.push(CondTok::Op(op));
            i += op.len();
            continue;
        }
        let start = i;
        while i < bytes.len() && is_ident_byte(bytes[i]) {
            i += 1;
        }
        if i == start {
            return Err(Error::at(
                at.clone(),
                format!("{c:?} does not belong in an @if condition"),
            ));
        }
        out.push(CondTok::Ident(text[start..i].to_string()));
    }
    Ok(out)
}

struct CondParser<'a> {
    tokens: &'a [CondTok],
    at: usize,
    defines: &'a HashMap<String, String>,
    depth: usize,
    max_depth: usize,
}

impl CondParser<'_> {
    fn peek(&self) -> Option<&CondTok> {
        self.tokens.get(self.at)
    }

    fn eat(&mut self, op: &str) -> bool {
        if self.peek() == Some(&CondTok::Op(static_op(op))) {
            self.at += 1;
            return true;
        }
        false
    }

    fn or_expr(&mut self, at: &Location) -> Result<CondValue> {
        let mut left = self.xor_expr(at)?;
        while self.eat("||") {
            let right = self.xor_expr(at)?;
            left = CondValue::Bool(left.as_bool(at)? | right.as_bool(at)?);
        }
        Ok(left)
    }

    fn xor_expr(&mut self, at: &Location) -> Result<CondValue> {
        let mut left = self.and_expr(at)?;
        while self.eat("^^") {
            let right = self.and_expr(at)?;
            left = CondValue::Bool(left.as_bool(at)? ^ right.as_bool(at)?);
        }
        Ok(left)
    }

    fn and_expr(&mut self, at: &Location) -> Result<CondValue> {
        let mut left = self.compare(at)?;
        while self.eat("&&") {
            let right = self.compare(at)?;
            left = CondValue::Bool(left.as_bool(at)? & right.as_bool(at)?);
        }
        Ok(left)
    }

    fn compare(&mut self, at: &Location) -> Result<CondValue> {
        let left = self.primary(at)?;
        if self.eat("==") {
            let right = self.primary(at)?;
            return Ok(CondValue::Bool(left.as_str() == right.as_str()));
        }
        if self.eat("!=") {
            let right = self.primary(at)?;
            return Ok(CondValue::Bool(left.as_str() != right.as_str()));
        }
        Ok(left)
    }

    fn primary(&mut self, at: &Location) -> Result<CondValue> {
        self.depth += 1;
        if self.depth > self.max_depth {
            return Err(Error::at(at.clone(), "an @if condition nests too deep"));
        }
        let value = self.primary_inner(at);
        self.depth -= 1;
        value
    }

    fn primary_inner(&mut self, at: &Location) -> Result<CondValue> {
        if self.eat("!") {
            let inner = self.primary(at)?;
            return Ok(CondValue::Bool(!inner.as_bool(at)?));
        }
        if self.eat("(") {
            let inner = self.or_expr(at)?;
            if !self.eat(")") {
                return Err(Error::at(at.clone(), "a ( in an @if is never closed"));
            }
            return Ok(inner);
        }
        match self.tokens.get(self.at).cloned() {
            Some(CondTok::Str(s)) => {
                self.at += 1;
                Ok(CondValue::Str(s))
            }
            Some(CondTok::Ident(name)) => {
                self.at += 1;
                if name == "defined" {
                    if !self.eat("(") {
                        return Err(Error::at(at.clone(), "defined wants ( after it"));
                    }
                    let Some(CondTok::Ident(arg)) = self.tokens.get(self.at).cloned() else {
                        return Err(Error::at(at.clone(), "defined wants a macro name"));
                    };
                    self.at += 1;
                    if !self.eat(")") {
                        return Err(Error::at(at.clone(), "defined( is never closed"));
                    }
                    return Ok(CondValue::Bool(self.defines.contains_key(&arg)));
                }
                // An undefined macro compares equal to nothing rather than
                // failing: `@if X == "y"` with X unset is simply false.
                Ok(CondValue::Str(
                    self.defines.get(&name).cloned().unwrap_or_default(),
                ))
            }
            _ => Err(Error::at(
                at.clone(),
                "an @if condition ends where a value is needed",
            )),
        }
    }
}

/// The operator table is a fixed set of literals, so a lookup by text can hand
/// back the `'static` one rather than allocating.
fn static_op(op: &str) -> &'static str {
    const OPS: [&str; 8] = ["&&", "||", "^^", "==", "!=", "(", ")", "!"];
    OPS.into_iter().find(|o| *o == op).unwrap_or("")
}

fn split_word(s: &str) -> (&str, &str) {
    let s = s.trim_start();
    match s.find(char::is_whitespace) {
        Some(i) => (&s[..i], &s[i..]),
        None => (s, ""),
    }
}

/// Drop a trailing `#` comment, respecting double quotes so that
/// `@define HASH "#"` survives.
fn strip_comment(s: &str) -> &str {
    let bytes = s.as_bytes();
    let mut quoted = false;
    for (i, &b) in bytes.iter().enumerate() {
        match b {
            b'"' => quoted = !quoted,
            b'#' if !quoted => return &s[..i],
            _ => {}
        }
    }
    s
}

fn unquote(s: &str) -> String {
    let s = s.trim();
    match s.strip_prefix('"').and_then(|r| r.strip_suffix('"')) {
        Some(inner) => inner.to_string(),
        None => s.to_string(),
    }
}

fn is_ident_byte(b: u8) -> bool {
    b.is_ascii_alphanumeric() || b == b'_' || b == b'.'
}

fn is_identifier(s: &str) -> bool {
    !s.is_empty() && !s.as_bytes()[0].is_ascii_digit() && s.bytes().all(is_ident_byte)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn run(files: &[(&str, &str)]) -> Result<Source> {
        let mut loader = MemoryLoader::new();
        for (name, text) in files {
            loader.insert(*name, *text);
        }
        Preprocessor::new(&mut loader).run(Path::new(files[0].0))
    }

    #[test]
    fn a_define_expands() {
        let s = run(&[(
            "a.slaspec",
            "@define ENDIAN \"big\"\ndefine endian=$(ENDIAN);\n",
        )])
        .expect("preprocesses");
        assert_eq!(
            s.text().split_whitespace().collect::<Vec<_>>(),
            ["define", "endian=", "big", ";"]
        );
    }

    #[test]
    fn ifdef_selects_a_branch() {
        let text = "@define X\n@ifdef X\nyes\n@else\nno\n@endif\n";
        let s = run(&[("a.slaspec", text)]).expect("preprocesses");
        assert!(s.text().contains("yes"));
        assert!(!s.text().contains("no"));
    }

    #[test]
    fn elif_chains_pick_one() {
        let text =
            "@define P \"mips\"\n@if P == \"x86\"\na\n@elif P == \"mips\"\nb\n@else\nc\n@endif\n";
        let s = run(&[("a.slaspec", text)]).expect("preprocesses");
        assert!(s.text().contains('b'), "{}", s.text());
        assert!(!s.text().contains('a'));
        assert!(!s.text().contains('c'));
    }

    #[test]
    fn defined_works_inside_an_if() {
        let text = "@define A\n@if defined(A) || (B == \"5\")\nhit\n@endif\n";
        let s = run(&[("a.slaspec", text)]).expect("preprocesses");
        assert!(s.text().contains("hit"));
    }

    #[test]
    fn includes_resolve_next_to_the_including_file() {
        let s = run(&[
            ("d/a.slaspec", "@include \"b.sinc\"\n"),
            ("d/b.sinc", "included\n"),
        ])
        .expect("preprocesses");
        assert!(s.text().contains("included"));
        let at = s.location(0).expect("origin");
        assert_eq!(&*at.file, "d/b.sinc");
        assert_eq!(at.line, 1);
    }

    #[test]
    fn an_unclosed_if_is_reported_without_losing_the_file() {
        let s = run(&[("a.slaspec", "@ifdef X\nbody\n")]).expect("preprocesses");
        assert_eq!(s.warnings().len(), 1, "{:?}", s.warnings());
        assert!(
            s.warnings()[0].contains("never closed"),
            "{:?}",
            s.warnings()
        );
    }

    #[test]
    fn a_condition_may_be_closed_by_a_later_file() {
        let s = run(&[
            (
                "d/a.slaspec",
                "@define X\n@include \"b.sinc\"\nafter\n@endif\n",
            ),
            ("d/b.sinc", "@ifdef X\ninside\n"),
        ])
        .expect("preprocesses");
        assert!(s.warnings().is_empty(), "{:?}", s.warnings());
        assert_eq!(
            s.text().split_whitespace().collect::<Vec<_>>(),
            ["inside", "after"]
        );
    }

    #[test]
    fn a_self_referential_macro_does_not_hang() {
        let e = run(&[("a.slaspec", "@define X \"$(X)\"\nuse $(X)\n")]).unwrap_err();
        assert!(e.message.contains("expands to itself"), "{e}");
    }

    #[test]
    fn two_macros_that_expand_each_other_do_not_hang() {
        let e = run(&[(
            "a.slaspec",
            "@define A \"$(B)\"\n@define B \"$(A)\"\nuse $(A)\n",
        )])
        .unwrap_err();
        assert!(e.message.contains("expansions"), "{e}");
    }

    #[test]
    fn a_macro_may_name_one_defined_later() {
        let s = run(&[(
            "a.slaspec",
            "@define OUTER \"$(INNER)\"\n@define INNER \"4\"\nsize=$(OUTER);\n",
        )])
        .expect("preprocesses");
        assert_eq!(
            s.text().split_whitespace().collect::<Vec<_>>(),
            ["size=", "4", ";"]
        );
    }

    #[test]
    fn a_directive_in_a_dead_branch_is_not_executed() {
        let text = "@ifdef NOPE\n@include \"missing.sinc\"\n@define Y 1\n@endif\nafter\n";
        let s = run(&[("a.slaspec", text)]).expect("preprocesses");
        assert!(s.text().contains("after"));
    }

    #[test]
    fn nested_conditions_track_their_own_state() {
        let text = "@ifdef NOPE\n@ifdef ALSO_NOPE\na\n@else\nb\n@endif\n@else\nc\n@endif\n";
        let s = run(&[("a.slaspec", text)]).expect("preprocesses");
        assert_eq!(s.text().trim(), "c");
    }
}
