//! Loopback dashboard. All analysis and coordination comes from library APIs.
use crate::{annotate, out::Out, patch};
use e5r_db::work::{Draft, Store};
use serde::Deserialize;
use serde_json::{Value, json};
use std::io::Read;
use std::path::Path;
use tiny_http::{Header, Method, Request, Response, Server, StatusCode};

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct Edit {
    content: Draft,
    author: String,
    revision: Option<u64>,
}

fn header(name: &str, value: &str) -> Header {
    Header::from_bytes(name.as_bytes(), value.as_bytes()).expect("constant HTTP header")
}

fn respond(request: Request, code: u16, kind: &str, body: String) {
    let response = Response::from_string(body).with_status_code(StatusCode(code))
        .with_header(header("Content-Type", kind))
        .with_header(header("Cache-Control", "no-store"))
        .with_header(header("X-Content-Type-Options", "nosniff"))
        .with_header(header("Content-Security-Policy", "default-src 'self'; script-src 'self'; style-src 'self'; object-src 'none'; frame-ancestors 'none'; base-uri 'none'"));
    let _ = request.respond(response);
}

fn field<'a>(request: &'a Request, name: &'static str) -> Option<&'a str> {
    request
        .headers()
        .iter()
        .find(|h| h.field.equiv(name))
        .map(|h| h.value.as_str())
}

fn trusted(request: &Request, host: &str) -> bool {
    field(request, "Host") == Some(host)
        && field(request, "Origin").is_none_or(|origin| origin == format!("http://{host}"))
}

fn edit(request: &mut Request) -> Result<Edit, String> {
    if field(request, "X-E5R-Client") != Some("dashboard") {
        return Err("missing dashboard client header".into());
    }
    if field(request, "Content-Type") != Some("application/json") {
        return Err("expected application/json".into());
    }
    const CAP: usize = 128 * 1024;
    if request.body_length().is_some_and(|n| n > CAP) {
        return Err("request exceeds 128 KiB".into());
    }
    let mut data = Vec::new();
    request
        .as_reader()
        .take((CAP + 1) as u64)
        .read_to_end(&mut data)
        .map_err(|e| e.to_string())?;
    if data.len() > CAP {
        return Err("request exceeds 128 KiB".into());
    }
    let change: Edit = serde_json::from_slice(&data).map_err(|e| e.to_string())?;
    if change.author.trim().is_empty() {
        return Err("a writer name is required".into());
    }
    Ok(change)
}

pub fn serve(project_path: &Path, port: u16, binary: Option<&Path>) -> Result<u8, String> {
    let project = patch::project_read(project_path)?;
    let binary = binary.unwrap_or_else(|| Path::new(&project.binary.path));
    let file = std::fs::File::open(binary).map_err(|e| format!("{}: {e}", binary.display()))?;
    let data = crate::map_file(&file).map_err(|e| e.to_string())?;
    let verdict = project.verify_at(&binary.to_string_lossy(), &data);
    if !verdict.is_usable() {
        return Err(verdict.to_string());
    }
    let mut options = e5r_analysis::Options::default();
    for (key, value) in &project.analysis {
        let boolean = || {
            value
                .parse::<bool>()
                .map_err(|_| format!("{key} needs true or false"))
        };
        match key.as_str() {
            "scan_gaps" => options.scan_gaps = boolean()?,
            "follow_calls" => options.follow_calls = boolean()?,
            "strings" => options.strings = boolean()?,
            "xrefs" => options.xrefs = boolean()?,
            "noreturn" => options.noreturn = boolean()?,
            "data" => options.data = boolean()?,
            "threads" => {
                options.threads = Some(value.parse().map_err(|_| "threads needs a number")?)
            }
            _ => {
                return Err(format!(
                    "dashboard does not understand project option {key:?}"
                ));
            }
        }
    }
    let load = e5r_format::LoadOptions {
        base: project.load.base,
        arch: project.load.arch.clone(),
        ..Default::default()
    };
    let mut object = e5r_format::load(&data, &load).map_err(|e| e.to_string())?;
    if project
        .load
        .readers
        .iter()
        .any(|reader| reader != object.format.as_str())
    {
        return Err("dashboard does not yet support custom project readers".into());
    }
    e5r_api::apply_relative_relocations(&mut object);
    annotate::load_pdb(&mut object, binary);
    eprintln!("Analyzing {} for the workspace…", binary.display());
    let mut program = e5r_analysis::analyze(object, &options);
    let db = project
        .log
        .as_ref()
        .map(std::path::PathBuf::from)
        .unwrap_or_else(|| annotate::default_path(binary));
    annotate::load(&db)?; // Refuse a damaged annotation log before opening.
    for (at, name, _) in annotate::names(&program, &db) {
        if let Some(f) = program.functions.get_mut(&at) {
            f.name = Some(name);
        }
    }
    let declared = annotate::declarations(&program, &db);
    let comments = annotate::comments(&program, &db);
    let store = Store::new(e5r_db::work::beside(project_path));
    let server = Server::http((std::net::Ipv4Addr::LOCALHOST, port)).map_err(|e| e.to_string())?;
    let host = server.server_addr().to_string();
    eprintln!(
        "Project workspace: http://{host}\nCtrl-C stops it. Binary and annotations are a startup snapshot."
    );
    for mut request in server.incoming_requests() {
        if !trusted(&request, &host) {
            respond(
                request,
                403,
                "application/json",
                json!({"error":"untrusted host or origin"}).to_string(),
            );
            continue;
        }
        let path = request.url().to_string();
        if request.method() == &Method::Get {
            let asset = match path.as_str() {
                "/" => Some((
                    "text/html; charset=utf-8",
                    include_str!("dashboard/index.html"),
                )),
                "/app.js" => Some((
                    "text/javascript; charset=utf-8",
                    include_str!("dashboard/app.js"),
                )),
                "/style.css" => Some((
                    "text/css; charset=utf-8",
                    include_str!("dashboard/style.css"),
                )),
                _ => None,
            };
            if let Some((kind, body)) = asset {
                respond(request, 200, kind, body.into());
                continue;
            }
        }
        let result: Result<Value, String> = (|| {
            match (request.method(), path.as_str()) {
                (&Method::Get, "/api/project") => Ok(
                    json!({ "schema":"e5r.workspace.v1", "project":project_path.display().to_string(), "binary":binary.display().to_string(), "hash":format!("{:016x}", project.binary.hash), "info":crate::json::info(&program.object), "author":crate::whoami(), "snapshot":true, "log":db.display().to_string(), "base":project.load.base.map(|a| a.to_string()), "arch":project.load.arch.as_ref().map(|a| a.name()), "no_scan":!options.scan_gaps, "threads":options.threads }),
                ),
                (&Method::Get, "/api/tasks") => {
                    serde_json::to_value(store.board()?).map_err(|e| e.to_string())
                }
                (&Method::Get, "/api/functions") => {
                    serde_json::to_value(crate::json::funcs(&program)).map_err(|e| e.to_string())
                }
                (&Method::Post, "/api/tasks") => {
                    let change = edit(&mut request)?;
                    if change.revision.is_some() {
                        return Err("new tasks do not take a revision".into());
                    }
                    serde_json::to_value(store.create(change.content, &change.author)?)
                        .map_err(|e| e.to_string())
                }
                _ if request.method() == &Method::Post && path.starts_with("/api/tasks/") => {
                    let change = edit(&mut request)?;
                    serde_json::to_value(store.update(
                        &path[11..],
                        change.revision.ok_or("revision is required")?,
                        change.content,
                        &change.author,
                    )?)
                    .map_err(|e| e.to_string())
                }
                _ if request.method() == &Method::Get => {
                    let (kind, target) = path
                        .strip_prefix("/api/")
                        .and_then(|s| s.split_once('/'))
                        .ok_or("route not found")?;
                    // A pane asks about one recovered function, never an unbounded 'all'.
                    let at = crate::addr::parse_number(target)
                        .map(e5r_core::Addr)
                        .ok_or("expected a function address")?;
                    if program.function(at).is_none() {
                        return Err("function not found".into());
                    }
                    let mut output = Out::buffer();
                    let limits = crate::print::Limits {
                        budget: crate::budget::Budget::new(Some(10.0), Some(1)),
                        progress: false,
                        declared: &declared,
                        comments: &comments,
                    };
                    match kind {
                        "decompile" => {
                            crate::print::decompile(&mut output, &program, target, true, limits)?;
                        }
                        "disas" => {
                            crate::print::disas(&mut output, &program, target, true, true, limits)?;
                        }
                        "xrefs" => {
                            crate::print::xrefs(&mut output, &program, target, false, true)?;
                        }
                        _ => return Err("route not found".into()),
                    }
                    serde_json::from_str(&output.take()).map_err(|e| e.to_string())
                }
                _ => Err("route not found".into()),
            }
        })();
        match result {
            Ok(value) => respond(request, 200, "application/json", value.to_string()),
            Err(error) => {
                let code =
                    if error.contains("revision conflict") || error.starts_with("cannot lock") {
                        409
                    } else if error.contains("not found") {
                        404
                    } else {
                        400
                    };
                respond(
                    request,
                    code,
                    "application/json",
                    json!({"error":error}).to_string(),
                );
            }
        }
    }
    Ok(0)
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn cross_origin_and_rebound_hosts_are_rejected() {
        let good: Request = tiny_http::TestRequest::new()
            .with_header(header("Host", "127.0.0.1:7879"))
            .into();
        assert!(trusted(&good, "127.0.0.1:7879"));
        let bad: Request = tiny_http::TestRequest::new()
            .with_header(header("Host", "attacker.example:7879"))
            .into();
        assert!(!trusted(&bad, "127.0.0.1:7879"));
        let bad: Request = tiny_http::TestRequest::new()
            .with_header(header("Host", "127.0.0.1:7879"))
            .with_header(header("Origin", "https://attacker.example"))
            .into();
        assert!(!trusted(&bad, "127.0.0.1:7879"));
    }
}
