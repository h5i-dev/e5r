//! Microsoft C++ demangling.
//!
//! The qualified name only. MSVC's type grammar is a second, larger job, and
//! the name is where nearly all the readability is: `?Foo@Bar@@QEAAXXZ`
//! becoming `Bar::Foo` is the difference between a listing you can read and one
//! you cannot. The parameter list is left off rather than guessed at.

/// Demangle the qualified name out of an MSVC symbol.
pub fn demangle(name: &str) -> Option<String> {
    let body = name.strip_prefix('?')?;
    // A leading second `?` marks a special name: an operator or a constructor.
    let (special, body) = match body.strip_prefix('?') {
        Some(rest) => (true, rest),
        None => (false, body),
    };

    let mut parts: Vec<String> = Vec::new();
    let mut rest = body;

    let mut leading = String::new();
    if special {
        let code = rest.chars().next()?;
        rest = &rest[code.len_utf8()..];
        leading = match code {
            '0' => "{ctor}".into(),
            '1' => "{dtor}".into(),
            '2' => "operator new".into(),
            '3' => "operator delete".into(),
            '4' => "operator=".into(),
            '5' => "operator>>".into(),
            '6' => "operator<<".into(),
            '7' => "operator!".into(),
            '8' => "operator==".into(),
            '9' => "operator!=".into(),
            'A' => "operator[]".into(),
            'E' => "operator++".into(),
            'F' => "operator--".into(),
            'G' => "operator-".into(),
            'H' => "operator+".into(),
            'R' => {
                // The `?_R` family: RTTI descriptors.
                let tag = rest.chars().next()?;
                rest = &rest[tag.len_utf8()..];
                format!("RTTI descriptor {tag}")
            }
            _ => format!("{{special {code}}}"),
        };
    }

    // Name components, innermost first, terminated by `@@`.
    loop {
        if rest.starts_with("@@") || rest.is_empty() {
            break;
        }
        let Some(end) = rest.find('@') else { break };
        let part = &rest[..end];
        rest = &rest[end + 1..];
        if part.is_empty() {
            break;
        }
        parts.push(part.to_string());
    }
    if parts.is_empty() && leading.is_empty() {
        return None;
    }

    // The components are innermost first, so the path reads in reverse.
    parts.reverse();
    let mut out = parts.join("::");
    if !leading.is_empty() {
        if leading == "{ctor}" || leading == "{dtor}" {
            // A constructor repeats its class name; a destructor prefixes it.
            let class = parts.last().cloned().unwrap_or_default();
            let prefix = if leading == "{dtor}" { "~" } else { "" };
            if !out.is_empty() {
                out.push_str("::");
            }
            out.push_str(prefix);
            out.push_str(&class);
            return Some(out);
        }
        if out.is_empty() {
            return Some(leading);
        }
        out.push_str("::");
        out.push_str(&leading);
    }
    Some(out)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn a_qualified_name_reads_outermost_first() {
        assert_eq!(demangle("?Foo@Bar@@QEAAXXZ").as_deref(), Some("Bar::Foo"));
        assert_eq!(
            demangle("?value@config@app@@QEAAHXZ").as_deref(),
            Some("app::config::value")
        );
    }

    #[test]
    fn constructors_and_destructors() {
        assert_eq!(
            demangle("??0Widget@@QEAA@XZ").as_deref(),
            Some("Widget::Widget")
        );
        assert_eq!(
            demangle("??1Widget@@UEAA@XZ").as_deref(),
            Some("Widget::~Widget")
        );
    }

    #[test]
    fn operators() {
        assert_eq!(
            demangle("??8Widget@@QEBA_NAEBV0@@Z").as_deref(),
            Some("Widget::operator==")
        );
    }

    #[test]
    fn names_that_are_not_msvc_are_refused() {
        assert_eq!(demangle("main"), None);
        assert_eq!(demangle("_Z3fooi"), None);
        assert_eq!(demangle("?"), None);
    }
}
