//! Loopback collection and project workspaces backed by the library APIs.
use crate::{annotate, out::Out, patch};
use e5r_db::{
    project::Project,
    registry::{self, Registry},
    work::{Draft, Store},
};
use serde::Deserialize;
use serde_json::{Value, json};
use std::io::Read;
use std::path::{Path, PathBuf};
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

fn body<T: serde::de::DeserializeOwned>(request: &mut Request) -> Result<T, String> {
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
    serde_json::from_slice(&data).map_err(|e| e.to_string())
}

fn edit(request: &mut Request) -> Result<Edit, String> {
    let change: Edit = body(request)?;
    if change.author.trim().is_empty() {
        return Err("a writer name is required".into());
    }
    Ok(change)
}

#[derive(Clone)]
struct Workspace {
    path: PathBuf,
    project: Project,
    binary: PathBuf,
    name: Option<String>,
}

impl Workspace {
    fn new(path: &Path, binary: Option<&Path>, name: Option<String>) -> Result<Self, String> {
        let mut project = patch::project_read(path)?;
        registry::normalize(
            &mut project,
            &std::env::current_dir().map_err(|e| e.to_string())?,
        )?;
        let binary = binary
            .map(Path::to_path_buf)
            .unwrap_or_else(|| PathBuf::from(&project.binary.path));
        Ok(Self {
            path: path.into(),
            project,
            binary,
            name,
        })
    }
    fn object(&self) -> Result<e5r_format::Object, String> {
        let file = std::fs::File::open(&self.binary)
            .map_err(|e| format!("{}: {e}", self.binary.display()))?;
        let data = crate::map_file(&file).map_err(|e| e.to_string())?;
        let verdict = self
            .project
            .verify_at(&self.binary.to_string_lossy(), &data);
        if !verdict.is_usable() {
            return Err(verdict.to_string());
        }
        let load = e5r_format::LoadOptions {
            base: self.project.load.base,
            arch: self.project.load.arch.clone(),
            ..Default::default()
        };
        let object = e5r_format::load(&data, &load).map_err(|e| e.to_string())?;
        if self
            .project
            .load
            .readers
            .iter()
            .any(|reader| reader != object.format.as_str())
        {
            return Err("dashboard does not yet support custom project readers".into());
        }
        Ok(object)
    }
    fn options(&self) -> Result<e5r_analysis::Options, String> {
        let mut options = e5r_analysis::Options::default();
        for (key, value) in &self.project.analysis {
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
        Ok(options)
    }
    fn store(&self) -> Store {
        Store::new(e5r_db::work::beside(&self.path))
    }
    fn metadata(&self) -> Value {
        let (info, binary_error) = match self.object() {
            Ok(object) => (Some(crate::json::info(&object)), None),
            Err(error) => (None, Some(error)),
        };
        let options = self.options();
        json!({ "schema":"e5r.workspace.v1", "project":self.path.display().to_string(), "name":self.name, "collection":self.name.is_some(), "binary":self.binary.display().to_string(), "hash":format!("{:016x}", self.project.binary.hash), "info":info, "binary_error":binary_error, "author":crate::whoami(), "snapshot":true, "log":self.project.log, "base":self.project.load.base.map(|a| a.to_string()), "arch":self.project.load.arch.as_ref().map(|a| a.name()), "no_scan":options.as_ref().is_ok_and(|o| !o.scan_gaps), "threads":options.as_ref().ok().and_then(|o| o.threads) })
    }
}

struct Analysis {
    key: String,
    program: e5r_analysis::Program,
    declared: std::collections::BTreeMap<e5r_core::Addr, String>,
    comments: std::collections::BTreeMap<e5r_core::Addr, String>,
}

impl Analysis {
    fn load(workspace: &Workspace, key: String) -> Result<Self, String> {
        let options = workspace.options()?;
        let mut object = workspace.object()?;
        e5r_api::apply_relative_relocations(&mut object);
        annotate::load_pdb(&mut object, &workspace.binary);
        eprintln!("Analyzing {}…", workspace.binary.display());
        let mut program = e5r_analysis::analyze(object, &options);
        let db = workspace
            .project
            .log
            .as_ref()
            .map(PathBuf::from)
            .unwrap_or_else(|| annotate::default_path(&workspace.binary));
        annotate::load(&db)?;
        for (at, name, _) in annotate::names(&program, &db) {
            if let Some(f) = program.functions.get_mut(&at) {
                f.name = Some(name);
            }
        }
        let declared = annotate::declarations(&program, &db);
        let comments = annotate::comments(&program, &db);
        Ok(Self {
            key,
            program,
            declared,
            comments,
        })
    }
    fn answer(&self, kind: &str, target: Option<&str>) -> Result<Value, String> {
        if kind == "functions" {
            return serde_json::to_value(crate::json::funcs(&self.program))
                .map_err(|e| e.to_string());
        }
        let target = target.ok_or("expected a function address")?;
        let at = crate::addr::parse_number(target)
            .map(e5r_core::Addr)
            .ok_or("expected a function address")?;
        if self.program.function(at).is_none() {
            return Err("function not found".into());
        }
        let mut output = Out::buffer();
        let limits = crate::print::Limits {
            budget: crate::budget::Budget::new(Some(10.0), Some(1)),
            progress: false,
            declared: &self.declared,
            comments: &self.comments,
        };
        match kind {
            "decompile" => {
                crate::print::decompile(&mut output, &self.program, target, true, limits)?;
            }
            "disas" => {
                crate::print::disas(&mut output, &self.program, target, true, true, limits)?;
            }
            "xrefs" => {
                crate::print::xrefs(&mut output, &self.program, target, false, true)?;
            }
            _ => return Err("route not found".into()),
        }
        serde_json::from_str(&output.take()).map_err(|e| e.to_string())
    }
}

fn answer(request: Request, result: Result<Value, String>) {
    match result {
        Ok(value) => respond(request, 200, "application/json", value.to_string()),
        Err(error) => {
            let code = if error.contains("revision conflict") || error.starts_with("cannot lock") {
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

struct Job {
    request: Request,
    workspace: Workspace,
    kind: String,
    target: Option<String>,
}

fn worker() -> std::sync::mpsc::SyncSender<Job> {
    let (sender, receiver) = std::sync::mpsc::sync_channel::<Job>(16);
    std::thread::spawn(move || {
        let mut cached: Option<Analysis> = None;
        for job in receiver {
            let result = (|| {
                let key = format!(
                    "{}\n{}\n{}",
                    job.workspace.path.display(),
                    job.workspace.project.to_text(),
                    job.workspace.binary.display()
                );
                if cached.as_ref().is_none_or(|a| a.key != key) {
                    // Drop the old analysis before loading another: one resident
                    // program keeps a global collection affordable on this host.
                    cached = None;
                    cached = Some(Analysis::load(&job.workspace, key)?);
                }
                cached
                    .as_ref()
                    .ok_or("analysis unavailable")?
                    .answer(&job.kind, job.target.as_deref())
            })();
            answer(job.request, result);
        }
    });
    sender
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct NewProject {
    name: String,
    binary: PathBuf,
}

fn register(request: &mut Request, registry: &Registry) -> Result<Value, String> {
    let create: NewProject = body(request)?;
    registry::validate_name(&create.name)?;
    if !create.binary.is_absolute() {
        return Err("enter an absolute binary path".into());
    }
    let file = std::fs::File::open(&create.binary).map_err(|e| e.to_string())?;
    let data = crate::map_file(&file).map_err(|e| e.to_string())?;
    let object =
        e5r_format::load(&data, &e5r_format::LoadOptions::default()).map_err(|e| e.to_string())?;
    let project = patch::make_project(&create.binary, &object, &data, &[], None)?;
    let path = registry.create(&create.name, &project, None)?;
    Ok(json!({"name":create.name,"project":path.display().to_string()}))
}

pub fn serve(project_path: &Path, port: u16, binary: Option<&Path>) -> Result<u8, String> {
    let workspace = Workspace::new(project_path, binary, None)?;
    // Single-project mode keeps its existing early refusal of a wrong binary.
    workspace.object()?;
    serve_inner(port, Some(workspace), None)
}

pub fn serve_all(port: u16) -> Result<u8, String> {
    serve_inner(port, None, Some(Registry::new(registry::root()?)))
}

fn serve_inner(
    port: u16,
    single: Option<Workspace>,
    registry: Option<Registry>,
) -> Result<u8, String> {
    let server = Server::http((std::net::Ipv4Addr::LOCALHOST, port)).map_err(|e| e.to_string())?;
    let host = server.server_addr().to_string();
    let analysis = worker();
    eprintln!(
        "{}: http://{host}\nCtrl-C stops it. Analysis loads on demand; tasks stay live.",
        if single.is_some() {
            "Project workspace"
        } else {
            "Project collection"
        }
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
                "/" if single.is_some() => Some((
                    "text/html; charset=utf-8",
                    include_str!("dashboard/index.html"),
                )),
                "/" => Some((
                    "text/html; charset=utf-8",
                    include_str!("dashboard/projects.html"),
                )),
                "/app.js" => Some((
                    "text/javascript; charset=utf-8",
                    include_str!("dashboard/app.js"),
                )),
                "/projects.js" => Some((
                    "text/javascript; charset=utf-8",
                    include_str!("dashboard/projects.js"),
                )),
                "/style.css" => Some((
                    "text/css; charset=utf-8",
                    include_str!("dashboard/style.css"),
                )),
                _ if registry.is_some()
                    && path
                        .strip_prefix("/p/")
                        .and_then(|s| s.strip_suffix('/'))
                        .is_some_and(|name| registry::validate_name(name).is_ok()) =>
                {
                    Some((
                        "text/html; charset=utf-8",
                        include_str!("dashboard/index.html"),
                    ))
                }
                _ => None,
            };
            if let Some((kind, body)) = asset {
                respond(request, 200, kind, body.into());
                continue;
            }
        }
        if let Some(registry) = &registry {
            if path == "/api/projects" {
                let result = match *request.method() {
                    Method::Get => registry.list().map(|projects| json!({"schema":"e5r.projects.v1","root":registry.root().display().to_string(),"projects":projects})),
                    Method::Post => register(&mut request,registry),
                    _ => Err("route not found".into()),
                };
                answer(request, result);
                continue;
            }
        }
        let resolved = if let Some(workspace) = &single {
            Ok((workspace.clone(), path.clone()))
        } else {
            (|| {
                let (name, tail) = path
                    .strip_prefix("/p/")
                    .and_then(|s| s.split_once('/'))
                    .ok_or("route not found")?;
                let registry = registry.as_ref().ok_or("route not found")?;
                let workspace = Workspace::new(&registry.path(name)?, None, Some(name.into()))?;
                Ok((workspace, format!("/{tail}")))
            })()
        };
        let (workspace, route) = match resolved {
            Ok(value) => value,
            Err(e) => {
                answer(request, Err(e));
                continue;
            }
        };
        if request.method() == &Method::Get {
            let analysis_route = route
                .strip_prefix("/api/")
                .and_then(|s| s.split_once('/'))
                .map(|(kind, target)| (kind, Some(target)))
                .or_else(|| (route == "/api/functions").then_some(("functions", None)));
            if let Some((kind, target)) = analysis_route
                .filter(|(kind, _)| matches!(*kind, "functions" | "decompile" | "disas" | "xrefs"))
            {
                if target.is_some_and(|target| crate::addr::parse_number(target).is_none()) {
                    answer(request, Err("expected a function address".into()));
                    continue;
                }
                let job = Job {
                    request,
                    workspace,
                    kind: kind.into(),
                    target: target.map(str::to_string),
                };
                if let Err(error) = analysis.try_send(job) {
                    let job = match error {
                        std::sync::mpsc::TrySendError::Full(job)
                        | std::sync::mpsc::TrySendError::Disconnected(job) => job,
                    };
                    respond(
                        job.request,
                        503,
                        "application/json",
                        json!({"error":"analysis queue is busy; retry shortly"}).to_string(),
                    );
                }
                continue;
            }
        }
        let result = (|| match (request.method(), route.as_str()) {
            (&Method::Get, "/api/project") => Ok(workspace.metadata()),
            (&Method::Get, "/api/tasks") => {
                serde_json::to_value(workspace.store().board()?).map_err(|e| e.to_string())
            }
            (&Method::Post, "/api/tasks") => {
                let change = edit(&mut request)?;
                if change.revision.is_some() {
                    return Err("new tasks do not take a revision".into());
                }
                serde_json::to_value(workspace.store().create(change.content, &change.author)?)
                    .map_err(|e| e.to_string())
            }
            _ if request.method() == &Method::Post && route.starts_with("/api/tasks/") => {
                let change = edit(&mut request)?;
                serde_json::to_value(workspace.store().update(
                    &route[11..],
                    change.revision.ok_or("revision is required")?,
                    change.content,
                    &change.author,
                )?)
                .map_err(|e| e.to_string())
            }
            _ => Err("route not found".into()),
        })();
        answer(request, result);
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
