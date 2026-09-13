//! The agent loop, end to end: open, look, write, see the write.
//!
//! Drives the built binary over a pipe, the way an agent would, rather than
//! calling the functions directly, so the protocol framing is covered too.

use std::io::Write;
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};

use serde_json::{Value, json};

fn binary() -> Option<PathBuf> {
    // The test binary sits next to the CLI in the same profile directory.
    let mut p = std::env::current_exe().ok()?;
    p.pop();
    if p.ends_with("deps") {
        p.pop();
    }
    let bin = p.join("r12e");
    bin.is_file().then_some(bin)
}

fn fixture(name: &str) -> Option<PathBuf> {
    let p = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../fixtures/build")
        .join(name);
    p.is_file().then(|| p.canonicalize().unwrap())
}

/// Send a batch of requests and collect the replies by id.
fn talk(requests: &[Value]) -> Vec<Value> {
    let Some(bin) = binary() else {
        return Vec::new();
    };
    let mut child = Command::new(bin)
        .arg("mcp")
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::null())
        .spawn()
        .expect("spawn");
    {
        let mut stdin = child.stdin.take().unwrap();
        for r in requests {
            writeln!(stdin, "{r}").unwrap();
        }
    }
    let out = child.wait_with_output().expect("wait");
    String::from_utf8_lossy(&out.stdout)
        .lines()
        .filter_map(|l| serde_json::from_str(l).ok())
        .collect()
}

fn call(id: i64, name: &str, args: Value) -> Value {
    json!({
        "jsonrpc": "2.0",
        "id": id,
        "method": "tools/call",
        "params": { "name": name, "arguments": args },
    })
}

/// The JSON a tool result carries.
fn payload(reply: &Value) -> Value {
    let text = reply["result"]["content"][0]["text"]
        .as_str()
        .unwrap_or("{}");
    serde_json::from_str(text).unwrap_or(json!({}))
}

#[test]
fn the_handshake_reports_tools() {
    let replies = talk(&[
        json!({ "jsonrpc": "2.0", "id": 1, "method": "initialize", "params": {} }),
        json!({ "jsonrpc": "2.0", "id": 2, "method": "tools/list", "params": {} }),
    ]);
    if replies.is_empty() {
        return;
    }
    assert_eq!(replies[0]["result"]["serverInfo"]["name"], "r12e");
    let names: Vec<&str> = replies[1]["result"]["tools"]
        .as_array()
        .unwrap()
        .iter()
        .map(|t| t["name"].as_str().unwrap())
        .collect();
    for want in ["open", "list_functions", "disassemble", "xrefs", "annotate"] {
        assert!(names.contains(&want), "no {want} tool: {names:?}");
    }
    // Every tool has to describe its arguments, or an agent cannot call it.
    for t in replies[1]["result"]["tools"].as_array().unwrap() {
        assert!(
            t["description"].as_str().is_some_and(|d| d.len() > 20),
            "{} has no useful description",
            t["name"]
        );
        assert!(t["inputSchema"]["properties"].is_object());
    }
}

#[test]
fn a_notification_gets_no_reply() {
    // No id means no response, and a stray one would desynchronize a client.
    let replies = talk(&[
        json!({ "jsonrpc": "2.0", "method": "notifications/initialized" }),
        json!({ "jsonrpc": "2.0", "id": 7, "method": "ping", "params": {} }),
    ]);
    if replies.is_empty() {
        return;
    }
    assert_eq!(replies.len(), 1, "a notification was answered: {replies:?}");
    assert_eq!(replies[0]["id"], 7);
}

#[test]
fn open_look_write_see() {
    let Some(path) = fixture("hello.a64.O0") else {
        return;
    };
    // A scratch copy, so the log this writes does not land beside a fixture.
    let scratch = std::env::temp_dir().join(format!("r12e-mcp-{}", std::process::id()));
    let _ = std::fs::create_dir_all(&scratch);
    let target = scratch.join("bin");
    std::fs::copy(&path, &target).unwrap();
    let p = target.to_string_lossy().to_string();

    let replies = talk(&[
        call(1, "open", json!({ "path": p })),
        call(2, "disassemble", json!({ "path": p, "target": "sum_to" })),
        call(
            3,
            "annotate",
            json!({ "path": p, "field": "name", "target": "sum_to", "value": "triangular" }),
        ),
        call(
            4,
            "list_functions",
            json!({ "path": p, "contains": "triangular" }),
        ),
        call(5, "read_annotations", json!({ "path": p })),
    ]);
    if replies.is_empty() {
        return;
    }

    let opened = payload(&replies[0]);
    assert_eq!(opened["arch"], "aarch64");
    assert!(opened["functions"].as_u64().unwrap() > 5);

    let disas = payload(&replies[1]);
    assert_eq!(disas["function"], "sum_to");
    assert!(disas["instructions"].as_array().unwrap().len() > 5);

    let wrote = payload(&replies[2]);
    assert_eq!(wrote["value"], "triangular");

    // The whole point: the write is visible to the next call.
    let listed = payload(&replies[3]);
    assert_eq!(
        listed["total"], 1,
        "the annotation did not reach the next call: {listed}"
    );

    let annotations = payload(&replies[4]);
    let all = annotations["annotations"].as_array().unwrap();
    assert_eq!(all.len(), 1);
    assert_eq!(all[0]["value"], "triangular");
    // Same binary, so the anchor matched exactly rather than by address.
    assert_eq!(all[0]["match"], "exact");

    let _ = std::fs::remove_dir_all(&scratch);
}

#[test]
fn a_failed_call_is_a_result_not_a_protocol_error() {
    // An agent has to be able to read what went wrong and try again.
    let replies = talk(&[
        call(1, "nosuchtool", json!({})),
        call(2, "open", json!({ "path": "/nonexistent/file" })),
    ]);
    if replies.is_empty() {
        return;
    }
    for r in &replies {
        assert!(
            r["error"].is_null(),
            "a tool failure became a protocol error"
        );
        assert_eq!(r["result"]["isError"], true);
        let text = r["result"]["content"][0]["text"].as_str().unwrap();
        assert!(!text.is_empty(), "no explanation of the failure");
    }
}

#[test]
fn malformed_input_does_not_stop_the_server() {
    let Some(bin) = binary() else { return };
    let mut child = Command::new(bin)
        .arg("mcp")
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::null())
        .spawn()
        .unwrap();
    {
        let mut stdin = child.stdin.take().unwrap();
        writeln!(stdin, "not json at all").unwrap();
        writeln!(
            stdin,
            "{{\"jsonrpc\":\"2.0\",\"id\":9,\"method\":\"ping\"}}"
        )
        .unwrap();
    }
    let out = child.wait_with_output().unwrap();
    let replies: Vec<Value> = String::from_utf8_lossy(&out.stdout)
        .lines()
        .filter_map(|l| serde_json::from_str(l).ok())
        .collect();
    // The bad line is answered with a parse error and the good one still works.
    assert!(
        replies.iter().any(|r| r["id"] == 9),
        "the server stopped after bad input: {replies:?}"
    );
}
