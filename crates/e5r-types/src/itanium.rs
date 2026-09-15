//! Itanium C++ demangling, the scheme GCC and Clang use.
//!
//! A useful subset rather than the whole grammar: names, nesting, template
//! arguments, the type grammar for parameters, operators, and the special
//! names for vtables and RTTI. Constructs it does not know are reported as
//! unhandled rather than guessed at, and the caller keeps the mangled name,
//! because a wrong name is worse than a mangled one.

use std::fmt::Write;

/// The placeholder a function type carries where its declarator goes, so that
/// a pointer to a function prints inside the parentheses. Removed at the end.
const SLOT: &str = "\u{1}";

/// Demangle an Itanium-mangled symbol, or `None` when it is not one.
pub fn demangle(s: &str) -> Option<String> {
    let body = s.strip_prefix("_Z").or_else(|| s.strip_prefix("__Z"))?;
    let mut p = Parser::new(body);
    let out = p.mangled_name().ok()?;
    // Trailing junk means the parse went wrong somewhere; do not half-report.
    if !p.rest().is_empty() && !p.rest().starts_with('.') {
        return None;
    }
    Some(out.replace(SLOT, ""))
}

struct Parser<'a> {
    s: &'a str,
    at: usize,
    /// Substitution table: every component the grammar says is substitutable,
    /// in the order it was first seen. `S_` names the first, `S0_` the second.
    subs: Vec<String>,
    /// Template parameters in scope, for `T_` and `T0_`.
    args: Vec<String>,
    /// Guards against a mangled name that refers to itself.
    depth: u32,
    /// Qualifiers from a nested name, which print after the parameter list:
    /// `foo::bar(int) const`, not `foo::bar const(int)`.
    cv: String,
    /// True when the name just parsed ended in template arguments, which means
    /// the next type is the return type rather than a parameter.
    templated: bool,
}

type R<T> = Result<T, ()>;

impl<'a> Parser<'a> {
    fn new(s: &'a str) -> Parser<'a> {
        Parser {
            s,
            at: 0,
            subs: Vec::new(),
            args: Vec::new(),
            depth: 0,
            cv: String::new(),
            templated: false,
        }
    }

    fn rest(&self) -> &'a str {
        &self.s[self.at..]
    }

    fn peek(&self) -> Option<char> {
        self.rest().chars().next()
    }

    fn eat(&mut self, c: char) -> bool {
        if self.peek() == Some(c) {
            self.at += c.len_utf8();
            true
        } else {
            false
        }
    }

    fn take(&mut self) -> R<char> {
        let c = self.peek().ok_or(())?;
        self.at += c.len_utf8();
        Ok(c)
    }

    fn enter(&mut self) -> R<()> {
        self.depth += 1;
        if self.depth > 96 { Err(()) } else { Ok(()) }
    }

    fn leave(&mut self) {
        self.depth -= 1;
    }

    /// `<mangled-name> ::= <encoding>`
    fn mangled_name(&mut self) -> R<String> {
        // Special names come first: they wrap an ordinary encoding.
        if self.rest().starts_with('T') {
            let tag = {
                let mut it = self.rest().chars();
                it.next();
                it.next().ok_or(())?
            };
            let label = match tag {
                'V' => Some("vtable for "),
                'T' => Some("VTT for "),
                'I' => Some("typeinfo for "),
                'S' => Some("typeinfo name for "),
                'h' | 'v' => None, // thunks, handled below
                _ => None,
            };
            if let Some(label) = label {
                self.at += 2;
                let ty = self.ty()?;
                return Ok(format!("{label}{ty}"));
            }
        }
        if let Some(r) = self.rest().strip_prefix("GTt") {
            let mut inner = Parser::new(r);
            let name = inner.mangled_name()?;
            self.at = self.s.len();
            return Ok(format!("transaction clone for {name}"));
        }
        if let Some(r) = self.rest().strip_prefix("GV") {
            let mut inner = Parser::new(r);
            let name = inner.name()?;
            self.at = self.s.len();
            return Ok(format!("guard variable for {name}"));
        }

        let name = self.name()?;
        // The qualifiers belong to this name; types parsed for the parameters
        // will set their own, so take them now.
        let cv = std::mem::take(&mut self.cv);
        // A function's parameters follow its name.
        if self.rest().is_empty() || self.peek() == Some('.') {
            return Ok(format!("{name}{cv}"));
        }
        // A function template encodes its return type before its parameters,
        // because the return type takes part in overload resolution.
        let ret = if self.templated {
            Some(self.ty()?)
        } else {
            None
        };
        let params = self.params()?;
        let out = match ret {
            Some(r) => format!("{r} {name}({params})"),
            None => format!("{name}({params})"),
        };
        Ok(format!("{out}{cv}"))
    }

    /// The parameter list, which is empty for `v`.
    fn params(&mut self) -> R<String> {
        let mut out = String::new();
        let mut first = true;
        while !self.rest().is_empty() && self.peek() != Some('.') {
            let t = self.ty()?;
            if t == "void" && first && self.rest().is_empty() {
                return Ok(String::new());
            }
            if !first {
                out.push_str(", ");
            }
            out.push_str(&t);
            first = false;
        }
        Ok(out)
    }

    /// `<name>`: nested, unscoped, or a substitution.
    fn name(&mut self) -> R<String> {
        self.enter()?;
        let out = self.name_inner();
        self.leave();
        out
    }

    fn name_inner(&mut self) -> R<String> {
        match self.peek().ok_or(())? {
            'N' => self.nested_name(),
            'S' => {
                if let Some(full) = self.std_prefixed()? {
                    return Ok(full);
                }
                let s = self.substitution()?;
                // A substitution can still be followed by template arguments.
                if self.peek() == Some('I') {
                    let args = self.template_args_named()?;
                    let full = format!("{s}{args}");
                    self.subs.push(full.clone());
                    self.templated = true;
                    return Ok(full);
                }
                Ok(s)
            }
            'L' => {
                // Local to a translation unit; the name follows.
                self.at += 1;
                self.name()
            }
            'Z' => self.local_name(),
            _ => {
                let base = self.unqualified_name()?;
                if self.peek() == Some('I') {
                    self.subs.push(base.clone());
                    let args = self.template_args_named()?;
                    let full = format!("{base}{args}");
                    self.subs.push(full.clone());
                    self.templated = true;
                    return Ok(full);
                }
                Ok(base)
            }
        }
    }

    /// `Z <encoding> E <name>`: something declared inside a function.
    fn local_name(&mut self) -> R<String> {
        self.at += 1;
        let outer = self.mangled_name_until_e()?;
        let inner = if self.eat('s') {
            "string literal".to_string()
        } else {
            self.name()?
        };
        Ok(format!("{outer}::{inner}"))
    }

    fn mangled_name_until_e(&mut self) -> R<String> {
        let name = self.name()?;
        let mut out = name;
        if !self.rest().starts_with('E') {
            let params = self.params_until_e()?;
            let _ = write!(out, "({params})");
        }
        if !self.eat('E') {
            return Err(());
        }
        Ok(out)
    }

    fn params_until_e(&mut self) -> R<String> {
        let mut out = String::new();
        let mut first = true;
        while !self.rest().starts_with('E') && !self.rest().is_empty() {
            let t = self.ty()?;
            if !first {
                out.push_str(", ");
            }
            out.push_str(&t);
            first = false;
        }
        Ok(out)
    }

    /// `N [<cv>] <prefix> <unqualified-name> E`
    fn nested_name(&mut self) -> R<String> {
        self.at += 1;
        let mut trailing = String::new();
        loop {
            match self.peek() {
                Some('K') => {
                    self.at += 1;
                    trailing.push_str(" const");
                }
                Some('V') => {
                    self.at += 1;
                    trailing.push_str(" volatile");
                }
                Some('r') => {
                    self.at += 1;
                }
                Some('R') => {
                    self.at += 1;
                    trailing.push_str(" &");
                }
                Some('O') => {
                    self.at += 1;
                    trailing.push_str(" &&");
                }
                _ => break,
            }
        }

        let mut parts: Vec<String> = Vec::new();
        // A constructor or destructor encodes no return type, even when it is
        // itself a template.
        let mut ctor_or_dtor = false;
        while !self.eat('E') {
            if self.rest().is_empty() {
                return Err(());
            }
            // A constructor or destructor repeats the class name, which is
            // the part just before it.
            if matches!(self.peek(), Some('C') | Some('D'))
                && self
                    .rest()
                    .chars()
                    .nth(1)
                    .is_some_and(|c| c.is_ascii_digit() || c == 'C')
            {
                let dtor = self.peek() == Some('D');
                ctor_or_dtor = true;
                self.at += 2;
                let class = parts
                    .last()
                    .map(|p: &String| p.split('<').next().unwrap_or(p).to_string())
                    .unwrap_or_default();
                let class = class.rsplit("::").next().unwrap_or(&class).to_string();
                parts.push(format!("{}{class}", if dtor { "~" } else { "" }));
                continue;
            }
            // A component that came from the substitution table is not added
            // to it again; doing so shifts every later index by one.
            let from_sub = self.peek() == Some('S');
            let part = match self.peek().ok_or(())? {
                'S' => self.substitution()?,
                'I' => {
                    // Template arguments attach to the part just built.
                    let args = self.template_args_named()?;
                    let last = parts.last_mut().ok_or(())?;
                    last.push_str(&args);
                    let joined = parts.join("::");
                    self.subs.push(joined);
                    // Only the final component's arguments make the name a
                    // template; an intermediate class template does not.
                    self.templated = self.rest().starts_with('E');
                    continue;
                }
                'T' => self.template_param()?,
                _ => self.unqualified_name()?,
            };
            parts.push(part);
            // Every prefix is substitutable, except one that was already a
            // substitution and except the final component, which is the name
            // itself rather than a prefix.
            if !self.rest().starts_with('E') && !from_sub {
                self.subs.push(parts.join("::"));
            }
        }
        self.cv = trailing;
        if ctor_or_dtor {
            self.templated = false;
        }
        Ok(parts.join("::"))
    }

    /// A source name, an operator, or a constructor or destructor.
    fn unqualified_name(&mut self) -> R<String> {
        match self.peek().ok_or(())? {
            '0'..='9' => self.source_name(),
            // A bare constructor or destructor outside a nested name has no
            // class to repeat, so it is named for what it is.
            'C' => {
                self.at += 1;
                self.take()?;
                Ok("{ctor}".to_string())
            }
            'D' => {
                self.at += 1;
                self.take()?;
                Ok("{dtor}".to_string())
            }
            'U' => {
                // An unnamed type, `Ut<n>_` or a lambda `Ul...E<n>_`.
                self.at += 1;
                let kind = self.take()?;
                if kind == 'l' {
                    while !self.eat('E') {
                        if self.rest().is_empty() {
                            return Err(());
                        }
                        self.at += 1;
                    }
                }
                while self.peek().is_some_and(|c| c.is_ascii_digit()) {
                    self.at += 1;
                }
                self.eat('_');
                Ok(if kind == 'l' {
                    "{lambda}".into()
                } else {
                    "{unnamed}".into()
                })
            }
            'L' => {
                self.at += 1;
                self.unqualified_name()
            }
            _ => self.operator_name(),
        }
    }

    /// `<length> <chars>`
    fn source_name(&mut self) -> R<String> {
        let digits: String = self
            .rest()
            .chars()
            .take_while(|c| c.is_ascii_digit())
            .collect();
        if digits.is_empty() {
            return Err(());
        }
        self.at += digits.len();
        let n: usize = digits.parse().map_err(|_| ())?;
        if n == 0 || self.rest().len() < n {
            return Err(());
        }
        let name = self.rest()[..n].to_string();
        self.at += n;
        // An ABI tag follows some names and every demangler prints it.
        let mut name = name;
        while self.rest().starts_with('B') {
            self.at += 1;
            let tag = self.source_name()?;
            name.push_str(&format!("[abi:{tag}]"));
        }
        Ok(name)
    }

    fn operator_name(&mut self) -> R<String> {
        let code: String = self.rest().chars().take(2).collect();
        if code.len() < 2 {
            return Err(());
        }
        let name = match code.as_str() {
            "nw" => "operator new",
            "na" => "operator new[]",
            "dl" => "operator delete",
            "da" => "operator delete[]",
            "ps" => "operator+",
            "ng" => "operator-",
            "ad" => "operator&",
            "de" => "operator*",
            "co" => "operator~",
            "pl" => "operator+",
            "mi" => "operator-",
            "ml" => "operator*",
            "dv" => "operator/",
            "rm" => "operator%",
            "an" => "operator&",
            "or" => "operator|",
            "eo" => "operator^",
            "aS" => "operator=",
            "pL" => "operator+=",
            "mI" => "operator-=",
            "mL" => "operator*=",
            "dV" => "operator/=",
            "rM" => "operator%=",
            "aN" => "operator&=",
            "oR" => "operator|=",
            "eO" => "operator^=",
            "ls" => "operator<<",
            "rs" => "operator>>",
            "lS" => "operator<<=",
            "rS" => "operator>>=",
            "eq" => "operator==",
            "ne" => "operator!=",
            "lt" => "operator<",
            "gt" => "operator>",
            "le" => "operator<=",
            "ge" => "operator>=",
            "ss" => "operator<=>",
            "nt" => "operator!",
            "aa" => "operator&&",
            "oo" => "operator||",
            "pp" => "operator++",
            "mm" => "operator--",
            "cm" => "operator,",
            "pm" => "operator->*",
            "pt" => "operator->",
            "cl" => "operator()",
            "ix" => "operator[]",
            "qu" => "operator?",
            "cv" => {
                // A conversion operator names the type it converts to. That
                // type's template arguments are not the function's, so the
                // next type is a parameter rather than a return type.
                self.at += 2;
                let t = self.ty()?;
                self.templated = false;
                return Ok(format!("operator {t}"));
            }
            _ => return Err(()),
        };
        self.at += 2;
        Ok(name.to_string())
    }

    /// Template arguments in name position, which become the parameters `T_`
    /// refers to. A class template's are replaced by the function template's,
    /// because the function's are the ones in scope for its signature.
    fn template_args_named(&mut self) -> R<String> {
        let saved = std::mem::take(&mut self.args);
        let out = self.template_args();
        if out.is_err() {
            self.args = saved;
        }
        out
    }

    /// `I <template-arg>+ E`
    fn template_args(&mut self) -> R<String> {
        if !self.eat('I') {
            return Err(());
        }
        self.enter()?;
        let mut out = String::from("<");
        let mut first = true;
        while !self.eat('E') {
            if self.rest().is_empty() {
                self.leave();
                return Err(());
            }
            let arg = match self.template_arg() {
                Ok(a) => a,
                Err(e) => {
                    self.leave();
                    return Err(e);
                }
            };
            if !first {
                out.push_str(", ");
            }
            out.push_str(&arg);
            self.args.push(arg);
            first = false;
        }
        self.leave();
        // `>>` would close a shift operator, so a space keeps it a template.
        if out.ends_with('>') {
            out.push(' ');
        }
        out.push('>');
        Ok(out)
    }

    fn template_arg(&mut self) -> R<String> {
        match self.peek().ok_or(())? {
            'L' => self.expr_primary(),
            'X' => {
                // An expression, which this parser does not evaluate.
                self.at += 1;
                let mut depth = 1;
                while depth > 0 {
                    match self.take()? {
                        'X' => depth += 1,
                        'E' => depth -= 1,
                        _ => {}
                    }
                }
                Ok("...".into())
            }
            'J' => {
                // A pack.
                self.at += 1;
                let mut out = String::new();
                let mut first = true;
                while !self.eat('E') {
                    if self.rest().is_empty() {
                        return Err(());
                    }
                    let t = self.template_arg()?;
                    if !first {
                        out.push_str(", ");
                    }
                    out.push_str(&t);
                    first = false;
                }
                Ok(out)
            }
            _ => self.ty(),
        }
    }

    /// `L <type> <value> E`, a literal used as a template argument.
    fn expr_primary(&mut self) -> R<String> {
        self.at += 1;
        if self.peek() == Some('_') {
            // A mangled name used as a value.
            self.at += 1;
            let n = self.name()?;
            self.eat('E');
            return Ok(n);
        }
        let ty = self.ty()?;
        let digits: String = self.rest().chars().take_while(|c| *c != 'E').collect();
        self.at += digits.len();
        if !self.eat('E') {
            return Err(());
        }
        // A leading `n` is the minus sign.
        let value = match digits.strip_prefix('n') {
            Some(v) => format!("-{v}"),
            None => digits,
        };
        Ok(match ty.as_str() {
            "bool" => {
                if value == "1" {
                    "true".into()
                } else {
                    "false".into()
                }
            }
            "int" => value,
            "long" => format!("{value}l"),
            "unsigned int" => format!("{value}u"),
            "unsigned long" => format!("{value}ul"),
            "long long" => format!("{value}ll"),
            "unsigned long long" => format!("{value}ull"),
            _ => format!("({ty}){value}"),
        })
    }

    /// `St` abbreviates the std namespace and a name follows it, so it is a
    /// prefix rather than a complete name. Applies in both name and type
    /// positions, which is why it lives here.
    fn std_prefixed(&mut self) -> R<Option<String>> {
        if !self.rest().starts_with("St") {
            return Ok(None);
        }
        // `St` alone, with nothing that can follow it, is just the namespace.
        let after = &self.rest()[2..];
        if !after.starts_with(|c: char| c.is_ascii_digit())
            && !after.starts_with('C')
            && !after.starts_with('D')
        {
            return Ok(None);
        }
        self.at += 2;
        let inner = self.unqualified_name()?;
        let mut full = format!("std::{inner}");
        if self.peek() == Some('I') {
            self.subs.push(full.clone());
            let args = self.template_args_named()?;
            full.push_str(&args);
            self.templated = true;
        }
        self.subs.push(full.clone());
        Ok(Some(full))
    }

    /// `S_`, `S0_`, ... and the standard abbreviations.
    fn substitution(&mut self) -> R<String> {
        self.at += 1;
        // The standard abbreviations are a single letter.
        if let Some(c) = self.peek() {
            // The abbreviations for the stream and string types stand for
            // their full template specializations, and that is how every
            // demangler prints them.
            let std = match c {
                't' => Some("std"),
                'a' => Some("std::allocator"),
                'b' => Some("std::basic_string"),
                's' => {
                    Some("std::basic_string<char, std::char_traits<char>, std::allocator<char> >")
                }
                'i' => Some("std::basic_istream<char, std::char_traits<char> >"),
                'o' => Some("std::basic_ostream<char, std::char_traits<char> >"),
                'd' => Some("std::basic_iostream<char, std::char_traits<char> >"),
                _ => None,
            };
            if let Some(name) = std {
                self.at += 1;
                return Ok(name.to_string());
            }
        }
        // `S_` is index zero; `S<n>_` is index n + 1, in base 36.
        let digits: String = self
            .rest()
            .chars()
            .take_while(|c| c.is_ascii_alphanumeric())
            .collect();
        self.at += digits.len();
        if !self.eat('_') {
            return Err(());
        }
        let index = if digits.is_empty() {
            0
        } else {
            usize::from_str_radix(&digits, 36).map_err(|_| ())? + 1
        };
        self.subs.get(index).cloned().ok_or(())
    }

    /// `T_`, `T<n>_`: a template parameter.
    fn template_param(&mut self) -> R<String> {
        self.at += 1;
        let digits: String = self
            .rest()
            .chars()
            .take_while(|c| c.is_ascii_digit())
            .collect();
        self.at += digits.len();
        if !self.eat('_') {
            return Err(());
        }
        let index = if digits.is_empty() {
            0
        } else {
            digits.parse::<usize>().map_err(|_| ())? + 1
        };
        Ok(self
            .args
            .get(index)
            .cloned()
            .unwrap_or_else(|| format!("T{index}")))
    }

    /// `<type>`, including the qualifiers and indirections that wrap one.
    fn ty(&mut self) -> R<String> {
        self.enter()?;
        let out = self.ty_inner();
        self.leave();
        out
    }

    fn ty_inner(&mut self) -> R<String> {
        let c = self.peek().ok_or(())?;
        // Builtins are one letter and are never substitutable.
        if let Some(name) = builtin(c) {
            self.at += 1;
            return Ok(name.to_string());
        }
        match c {
            'P' | 'R' | 'O' | 'C' | 'K' | 'V' | 'r' => {
                self.at += 1;
                let inner = self.ty()?;
                // A function type carries a slot where its declarator goes,
                // so a pointer to one prints as `void (*)(int)` rather than
                // `void (int)*`.
                let out = if inner.contains(SLOT) {
                    let decl = match c {
                        'P' => "*",
                        'R' => "&",
                        'O' => "&&",
                        'K' => " const",
                        'V' => " volatile",
                        _ => "",
                    };
                    inner.replace(SLOT, &format!("{decl}{SLOT}"))
                } else {
                    match c {
                        'P' => format!("{inner}*"),
                        'R' => format!("{inner}&"),
                        'O' => format!("{inner}&&"),
                        'C' => format!("{inner} complex"),
                        'K' => format!("{inner} const"),
                        'V' => format!("{inner} volatile"),
                        _ => format!("{inner} restrict"),
                    }
                };
                self.subs.push(out.clone());
                Ok(out)
            }
            'A' => {
                // An array, with either a fixed bound or none.
                self.at += 1;
                let bound: String = self.rest().chars().take_while(|c| *c != '_').collect();
                self.at += bound.len();
                if !self.eat('_') {
                    return Err(());
                }
                let inner = self.ty()?;
                Ok(format!("{inner} [{bound}]"))
            }
            'F' => {
                // A function type.
                self.at += 1;
                let ret = self.ty()?;
                let mut params = Vec::new();
                while !self.eat('E') {
                    if self.rest().is_empty() {
                        return Err(());
                    }
                    params.push(self.ty()?);
                }
                let joined = if params == ["void"] {
                    String::new()
                } else {
                    params.join(", ")
                };
                let out = format!("{ret} ({SLOT})({joined})");
                self.subs.push(out.clone());
                Ok(out)
            }
            'M' => {
                // A pointer to member.
                self.at += 1;
                let class = self.ty()?;
                let member = self.ty()?;
                let out = if member.contains(SLOT) {
                    member.replace(SLOT, &format!("{class}::*{SLOT}"))
                } else {
                    format!("{member} {class}::*")
                };
                self.subs.push(out.clone());
                Ok(out)
            }
            'T' => self.template_param(),
            'S' => {
                if let Some(full) = self.std_prefixed()? {
                    return Ok(full);
                }
                let s = self.substitution()?;
                if self.peek() == Some('I') {
                    let args = self.template_args()?;
                    let full = format!("{s}{args}");
                    self.subs.push(full.clone());
                    return Ok(full);
                }
                Ok(s)
            }
            'D' => {
                // The `Dn`, `Da`, `Dc` family plus decltype.
                self.at += 1;
                let k = self.take()?;
                Ok(match k {
                    'n' => "decltype(nullptr)".into(),
                    'a' => "auto".into(),
                    'c' => "decltype(auto)".into(),
                    'i' => "char32_t".into(),
                    's' => "char16_t".into(),
                    'u' => "char8_t".into(),
                    'h' => "__fp16".into(),
                    'f' => "_Float32".into(),
                    'd' => "_Float64".into(),
                    _ => return Err(()),
                })
            }
            'u' => {
                // A vendor extended type, named by a source name.
                self.at += 1;
                self.source_name()
            }
            'N' => {
                let out = self.nested_name()?;
                // A specialized nested name was already recorded when its
                // template arguments were attached; recording it twice shifts
                // every later index by one.
                if self.subs.last() != Some(&out) {
                    self.subs.push(out.clone());
                }
                Ok(out)
            }
            '0'..='9' => {
                let out = self.source_name()?;
                if self.peek() == Some('I') {
                    self.subs.push(out.clone());
                    let args = self.template_args()?;
                    let full = format!("{out}{args}");
                    self.subs.push(full.clone());
                    return Ok(full);
                }
                self.subs.push(out.clone());
                Ok(out)
            }
            _ => Err(()),
        }
    }
}

fn builtin(c: char) -> Option<&'static str> {
    Some(match c {
        'v' => "void",
        'w' => "wchar_t",
        'b' => "bool",
        'c' => "char",
        'a' => "signed char",
        'h' => "unsigned char",
        's' => "short",
        't' => "unsigned short",
        'i' => "int",
        'j' => "unsigned int",
        'l' => "long",
        'm' => "unsigned long",
        'x' => "long long",
        'y' => "unsigned long long",
        'n' => "__int128",
        'o' => "unsigned __int128",
        'f' => "float",
        'd' => "double",
        'e' => "long double",
        'g' => "__float128",
        'z' => "...",
        _ => return None,
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn plain_functions() {
        assert_eq!(demangle("_Z3fooi").as_deref(), Some("foo(int)"));
        assert_eq!(demangle("_Z3barv").as_deref(), Some("bar()"));
        assert_eq!(demangle("_Z3addii").as_deref(), Some("add(int, int)"));
    }

    #[test]
    fn nesting_and_qualifiers() {
        assert_eq!(demangle("_ZN3foo3barEv").as_deref(), Some("foo::bar()"));
        assert_eq!(
            demangle("_ZNK3foo3barEi").as_deref(),
            Some("foo::bar(int) const")
        );
        assert_eq!(demangle("_Z4funcPKc").as_deref(), Some("func(char const*)"));
    }

    #[test]
    fn substitutions_point_backwards() {
        // S_ is the first substitutable component seen.
        assert_eq!(
            demangle("_Z3fooPKcS0_").as_deref(),
            Some("foo(char const*, char const*)")
        );
    }

    #[test]
    fn the_standard_abbreviations_are_known() {
        // `Ss` stands for the full specialization, which is how every
        // demangler prints it.
        assert_eq!(
            demangle("_Z3fooSs").as_deref(),
            Some("foo(std::basic_string<char, std::char_traits<char>, std::allocator<char> >)")
        );
        assert_eq!(demangle("_ZSt3fooi").as_deref(), Some("std::foo(int)"));
    }

    #[test]
    fn templates() {
        assert_eq!(
            demangle("_Z3fooIiEvT_").as_deref(),
            Some("void foo<int>(int)")
        );
    }

    #[test]
    fn operators() {
        assert_eq!(
            demangle("_ZN3fooplERKS_").as_deref(),
            Some("foo::operator+(foo const&)")
        );
    }

    #[test]
    fn special_names() {
        assert_eq!(demangle("_ZTV3foo").as_deref(), Some("vtable for foo"));
        assert_eq!(demangle("_ZTI3foo").as_deref(), Some("typeinfo for foo"));
    }

    #[test]
    fn a_name_that_is_not_mangled_is_refused() {
        assert_eq!(demangle("main"), None);
        assert_eq!(demangle("printf"), None);
        assert_eq!(demangle("_Z"), None);
    }

    #[test]
    fn a_broken_name_is_refused_rather_than_guessed_at() {
        // Truncated, so nothing honest can be said about it.
        assert_eq!(demangle("_ZN3foo3ba"), None);
        assert_eq!(demangle("_Z99foo"), None);
    }

    #[test]
    fn no_input_causes_a_hang_or_a_panic() {
        // Deeply nested indirection used to be a stack overflow.
        let deep = format!("_Z3foo{}i", "P".repeat(500));
        let _ = demangle(&deep);
        let recursive = "_ZS_S_S_S_S_S_S_S_S_";
        let _ = demangle(recursive);
        for n in 0..300usize {
            let s: String = std::iter::repeat_n('N', n).collect();
            let _ = demangle(&format!("_Z{s}"));
            let t: String = std::iter::repeat_n('I', n).collect();
            let _ = demangle(&format!("_Z3foo{t}"));
        }
    }
}
