//! The agent surface: JSON-RPC over stdin and stdout, in the Model Context
//! Protocol's shape.
//!
//! Written directly rather than through an SDK. The protocol is
//! newline-delimited JSON-RPC 2.0 with three methods that matter, and a
//! dependency here would be larger than the code it replaced.
//!
//! An opened binary is analyzed once and kept, because a tool call that
//! re-analyzed libc every time would make an agent's loop useless.

use std::collections::HashMap;
use std::io::{BufRead, Write};
use std::path::{Path, PathBuf};

use r12e_analysis::{Options, Program};
use r12e_core::Addr;
use r12e_db::Field;
use serde_json::{Value, json};

use crate::addr;
use crate::annotate;

/// The protocol version this speaks.
const PROTOCOL: &str = "2024-11-05";

/// Analyzed binaries, by the path they were opened from.
#[derive(Default)]
struct Session {
    open: HashMap<PathBuf, Program>,
}

impl Session {
    /// Analyze a path, or hand back the analysis already done.
    fn program(&mut self, path: &str) -> Result<&Program, String> {
        let p = PathBuf::from(path);
        if !self.open.contains_key(&p) {
            let data = std::fs::read(&p).map_err(|e| format!("{path}: {e}"))?;
            let object = r12e_format::load(&data, &r12e_format::LoadOptions::default())
                .map_err(|e| format!("{path}: {e}"))?;
            let mut program = r12e_analysis::analyze(object, &Options::default());
            // Names from the log override what the container said, the same
            // way they do on the command line.
            let db = annotate::default_path(&p);
            for (at, name, _) in annotate::names(&program, &db) {
                if let Some(f) = program.functions.get_mut(&at) {
                    f.name = Some(name);
                }
            }
            self.open.insert(p.clone(), program);
        }
        Ok(&self.open[&p])
    }

    fn forget(&mut self, path: &str) {
        self.open.remove(Path::new(path));
    }
}

/// Run the server until stdin closes.
pub fn serve() -> Result<u8, String> {
    let stdin = std::io::stdin();
    let mut out = std::io::stdout();
    let mut session = Session::default();

    for line in stdin.lock().lines() {
        let line = line.map_err(|e| e.to_string())?;
        if line.trim().is_empty() {
            continue;
        }
        let Ok(req): Result<Value, _> = serde_json::from_str(&line) else {
            write(&mut out, &error(Value::Null, -32700, "invalid JSON"))?;
            continue;
        };
        // A notification has no id and gets no reply.
        let id = req.get("id").cloned();
        let method = req.get("method").and_then(Value::as_str).unwrap_or("");
        let params = req.get("params").cloned().unwrap_or(json!({}));

        let reply = match method {
            "initialize" => Some(ok(id.clone(), initialize())),
            "tools/list" => Some(ok(id.clone(), json!({ "tools": tools() }))),
            "tools/call" => Some(match call(&mut session, &params) {
                Ok(v) => ok(id.clone(), v),
                // A failed tool call is a result carrying isError, not a
                // protocol error: the agent needs to read what went wrong.
                Err(e) => ok(
                    id.clone(),
                    json!({
                        "content": [{ "type": "text", "text": e }],
                        "isError": true,
                    }),
                ),
            }),
            "ping" => Some(ok(id.clone(), json!({}))),
            _ if id.is_none() => None,
            _ => Some(error(
                id.clone().unwrap_or(Value::Null),
                -32601,
                &format!("no method {method:?}"),
            )),
        };
        if let (Some(reply), Some(_)) = (reply, id) {
            write(&mut out, &reply)?;
        }
    }
    Ok(crate::exit::OK)
}

fn write(out: &mut impl Write, v: &Value) -> Result<(), String> {
    let s = serde_json::to_string(v).map_err(|e| e.to_string())?;
    writeln!(out, "{s}").map_err(|e| e.to_string())?;
    out.flush().map_err(|e| e.to_string())
}

fn ok(id: Option<Value>, result: Value) -> Value {
    json!({ "jsonrpc": "2.0", "id": id, "result": result })
}

fn error(id: Value, code: i64, message: &str) -> Value {
    json!({ "jsonrpc": "2.0", "id": id, "error": { "code": code, "message": message } })
}

fn initialize() -> Value {
    json!({
        "protocolVersion": PROTOCOL,
        "capabilities": { "tools": {} },
        "serverInfo": { "name": "r12e", "version": env!("CARGO_PKG_VERSION") },
    })
}

/// A required string argument.
fn arg<'a>(params: &'a Value, name: &str) -> Result<&'a str, String> {
    params
        .get(name)
        .and_then(Value::as_str)
        .ok_or_else(|| format!("{name} is required and must be a string"))
}

fn opt_u64(params: &Value, name: &str, default: u64) -> u64 {
    params.get(name).and_then(Value::as_u64).unwrap_or(default)
}

/// Wrap a value as a tool result. The text is the JSON, because an agent reads
/// it and a second encoding of the same facts would be one to keep in step.
fn result(v: Value) -> Value {
    let text = serde_json::to_string_pretty(&v).unwrap_or_else(|_| "{}".into());
    json!({ "content": [{ "type": "text", "text": text }], "isError": false })
}

fn call(session: &mut Session, params: &Value) -> Result<Value, String> {
    let name = arg(params, "name")?.to_string();
    let args = params.get("arguments").cloned().unwrap_or(json!({}));

    match name.as_str() {
        "open" => {
            let path = arg(&args, "path")?.to_string();
            session.forget(&path);
            let p = session.program(&path)?;
            let s = p.stats();
            Ok(result(json!({
                "path": path,
                "format": p.object.format.to_string(),
                "arch": p.object.arch.to_string(),
                "bits": p.object.bits.bytes() * 8,
                "entry": p.object.entry.map(hex),
                "functions": s.functions,
                "complete": s.complete,
                "instructions": s.insns,
                "strings": s.strings,
                "warnings": p.object.warnings,
                "decoder": if p.object.arch.has_native_decoder() {
                    "native"
                } else {
                    "none: the container loads, nothing disassembles"
                },
            })))
        }
        "stats" => {
            let p = session.program(arg(&args, "path")?)?;
            let s = p.stats();
            Ok(result(json!({
                "functions": s.functions,
                "complete": s.complete,
                "noreturn": s.noreturn,
                "blocks": s.blocks,
                "instructions": s.insns,
                "jump_tables": s.tables,
                "unresolved_indirect": s.indirect,
                "xrefs": s.xrefs,
                "strings": s.strings,
            })))
        }
        "list_functions" => {
            let p = session.program(arg(&args, "path")?)?;
            let contains = args.get("contains").and_then(Value::as_str);
            let limit = opt_u64(&args, "limit", 200) as usize;
            let offset = opt_u64(&args, "offset", 0) as usize;
            let all: Vec<&r12e_analysis::Function> = p
                .functions_by_address()
                .filter(|f| {
                    contains
                        .is_none_or(|c| f.display_name().to_lowercase().contains(&c.to_lowercase()))
                })
                .collect();
            let total = all.len();
            let items: Vec<Value> = all
                .into_iter()
                .skip(offset)
                .take(limit)
                .map(|f| {
                    json!({
                        "addr": hex(f.entry),
                        "name": f.display_name(),
                        "size": f.cfg.covered_bytes(),
                        "blocks": f.cfg.blocks.len(),
                        "complete": f.is_complete(),
                        "evidence": f.provenance.best.as_str(),
                        "strength": f.provenance.strength().as_str(),
                    })
                })
                .collect();
            Ok(result(json!({ "total": total, "functions": items })))
        }
        "disassemble" => {
            let p = session.program(arg(&args, "path")?)?;
            let target = arg(&args, "target")?;
            let at = addr::resolve(p, target)
                .ok_or_else(|| format!("{target:?} is not an address or a symbol"))?;
            let f = p
                .function(at)
                .or_else(|| p.function_at(at))
                .ok_or_else(|| format!("no function covers {at}"))?;
            if !p.object.arch.has_native_decoder() {
                return Err(format!(
                    "no decoder for {}; the container loads but nothing disassembles",
                    p.object.arch
                ));
            }
            let insns: Vec<Value> = p
                .instructions(f)
                .iter()
                .map(|i| {
                    json!({
                        "addr": hex(i.addr),
                        "text": r12e_arch::format(&p.object.arch, i, false).replace('\t', " "),
                        "target": i.flow.target().map(hex),
                    })
                })
                .collect();
            Ok(result(json!({
                "function": f.display_name(),
                "addr": hex(f.entry),
                "complete": f.is_complete(),
                "instructions": insns,
            })))
        }
        "xrefs" => {
            let p = session.program(arg(&args, "path")?)?;
            let target = arg(&args, "target")?;
            let at = addr::resolve(p, target)
                .ok_or_else(|| format!("{target:?} is not an address or a symbol"))?;
            let from = args
                .get("direction")
                .and_then(Value::as_str)
                .is_some_and(|d| d == "from");
            let refs = if from {
                p.xrefs.from(at)
            } else {
                p.xrefs.to(at)
            };
            let items: Vec<Value> = refs
                .iter()
                .map(|x| {
                    let other = if from { x.to } else { x.from };
                    json!({
                        "addr": hex(other),
                        "kind": format!("{:?}", x.kind).to_lowercase(),
                        "function": p.function_at(other).map(|f| f.display_name()),
                    })
                })
                .collect();
            Ok(result(json!({ "target": hex(at), "references": items })))
        }
        "strings" => {
            let p = session.program(arg(&args, "path")?)?;
            let contains = args.get("contains").and_then(Value::as_str);
            let limit = opt_u64(&args, "limit", 200) as usize;
            let items: Vec<Value> = p
                .strings
                .iter()
                .filter(|s| contains.is_none_or(|c| s.text.contains(c)))
                .take(limit)
                .map(|s| json!({ "addr": hex(s.addr), "text": s.text }))
                .collect();
            Ok(result(json!({ "strings": items })))
        }
        "annotate" => {
            let path = arg(&args, "path")?.to_string();
            let field = match arg(&args, "field")? {
                "name" => Field::Name,
                "comment" => Field::Comment,
                "type" => Field::Type,
                other => {
                    return Err(format!(
                        "field must be name, comment or type, not {other:?}"
                    ));
                }
            };
            let target = arg(&args, "target")?.to_string();
            let value = args
                .get("value")
                .and_then(Value::as_str)
                .map(|s| s.to_string());
            let db = annotate::default_path(Path::new(&path));
            let p = session.program(&path)?;
            let at = addr::resolve(p, &target)
                .ok_or_else(|| format!("{target:?} is not an address or a symbol"))?;
            let anchor =
                annotate::anchor_for(p, at).ok_or_else(|| format!("no function covers {at}"))?;
            let mut log = annotate::load(&db)?;
            log.assert(anchor, field, value.clone(), "mcp");
            annotate::save(&db, &log)?;
            // The name is now stale in the cached analysis.
            session.forget(&path);
            Ok(result(json!({
                "addr": hex(at),
                "field": field.to_string(),
                "value": value,
                "log": db.display().to_string(),
            })))
        }
        "read_annotations" => {
            let path = arg(&args, "path")?.to_string();
            let db = annotate::default_path(Path::new(&path));
            let p = session.program(&path)?;
            let log = annotate::load(&db)?;
            let items: Vec<Value> = log
                .apply(&annotate::index(p))
                .into_iter()
                .map(|a| {
                    json!({
                        "addr": hex(a.addr),
                        "field": a.field.to_string(),
                        "value": a.value,
                        "match": a.resolution.to_string(),
                        "confident": a.resolution.is_confident(),
                        "by": a.who,
                    })
                })
                .collect();
            Ok(result(json!({ "annotations": items })))
        }
        other => Err(format!("no tool {other:?}")),
    }
}

fn hex(a: Addr) -> String {
    format!("{:#x}", a.get())
}

/// A string argument in a tool's schema.
fn s(desc: &str) -> Value {
    json!({ "type": "string", "description": desc })
}

fn n(desc: &str) -> Value {
    json!({ "type": "integer", "description": desc })
}

fn tool(name: &str, desc: &str, props: Value, required: &[&str]) -> Value {
    json!({
        "name": name,
        "description": desc,
        "inputSchema": {
            "type": "object",
            "properties": props,
            "required": required,
        },
    })
}

fn tools() -> Vec<Value> {
    let path = s("Path to the binary.");
    vec![
        tool(
            "open",
            "Load and analyze a binary, and report what was found. Re-analyzes \
             if it was already open. Every other tool takes the same path and \
             reuses this analysis.",
            json!({ "path": path }),
            &["path"],
        ),
        tool(
            "stats",
            "Counts for an analyzed binary: functions, how many analyzed \
             completely, blocks, instructions, jump tables resolved, and how \
             many functions still hold an unresolved indirect branch.",
            json!({ "path": path }),
            &["path"],
        ),
        tool(
            "list_functions",
            "Recovered functions with the evidence for each. `evidence` says \
             what claimed the function and `strength` how good that claim is, \
             so a symbol-table entry is distinguishable from a prologue guess.",
            json!({
                "path": path,
                "contains": s("Only functions whose name contains this."),
                "limit": n("How many to return. Default 200."),
                "offset": n("Where to start, for paging."),
            }),
            &["path"],
        ),
        tool(
            "disassemble",
            "Disassemble one function. The target is an address, a symbol \
             name, or an expression like `main+0x20`.",
            json!({ "path": path, "target": s("Address, symbol, or expression.") }),
            &["path", "target"],
        ),
        tool(
            "xrefs",
            "What references an address, or what an address references. \
             Direction is `to` (the default) or `from`.",
            json!({
                "path": path,
                "target": s("Address, symbol, or expression."),
                "direction": s("`to` or `from`."),
            }),
            &["path", "target"],
        ),
        tool(
            "strings",
            "Strings found in the binary's data.",
            json!({
                "path": path,
                "contains": s("Only strings containing this."),
                "limit": n("How many to return. Default 200."),
            }),
            &["path"],
        ),
        tool(
            "annotate",
            "Write a name, comment or type into the annotation log, which is a \
             text file beside the binary that git can merge. Omit `value` to \
             clear the field. The annotation is keyed to a content anchor, so \
             it survives a rebuild of the binary.",
            json!({
                "path": path,
                "field": s("`name`, `comment` or `type`."),
                "target": s("Address, symbol, or expression."),
                "value": s("What to set. Omit to clear."),
            }),
            &["path", "field", "target"],
        ),
        tool(
            "read_annotations",
            "Everything the annotation log says about this binary, resolved \
             against the current analysis. `match` says how confidently each \
             annotation was placed.",
            json!({ "path": path }),
            &["path"],
        ),
    ]
}
