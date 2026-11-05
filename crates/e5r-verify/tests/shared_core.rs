//! Real pinned-kernel controls. These test the generic checker independently of
//! either backend's semantics, then exercise provenance and source relocation.
use e5r_verify::core::{
    artifact::Identity,
    process::{self, Limits},
    workspace::{ProjectLock, Workspace},
};
use std::path::{Path, PathBuf};
use std::process::Command;
use std::time::Duration;

fn common() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../verification/common")
        .canonicalize()
        .unwrap()
}
fn pinned_lean_available() -> bool {
    let mut command = Command::new("lean");
    command.current_dir(common()).arg("--version");
    let available = process::run(command, Limits::new(Duration::from_secs(10), 512))
        .is_ok_and(|r| r.success && r.output.contains("version 4.35.0"));
    assert!(
        available || std::env::var_os("E5R_REQUIRE_LEAN").is_none(),
        "pinned Lean 4.35.0 is required for these controls"
    );
    if !available {
        eprintln!("pinned Lean 4.35.0 unavailable: skipping Lean-dependent controls");
    }
    available
}
fn run(
    project: &Path,
    program: impl AsRef<std::ffi::OsStr>,
    args: &[&str],
    path: Option<&Path>,
) -> process::Run {
    let mut c = Command::new(program);
    c.current_dir(project)
        .args(args)
        .env("LEAN_NUM_THREADS", "1");
    if let Some(p) = path {
        c.env("LEAN_PATH", p);
    }
    process::run(c, Limits::new(Duration::from_secs(120), 4096)).unwrap()
}
#[test]
fn generic_checker_rejects_wrong_statements_axioms_imports_and_kernel_bypass() {
    if !pinned_lean_available() {
        return;
    }
    let project = common();
    assert!(run(&project, "lake", &["build", "-q", "proofcheck"], None).success);
    let work = Workspace::new(None).unwrap();
    let dir = work.path();
    let compile = |name: &str, text: &str| {
        std::fs::write(dir.join(format!("{name}.lean")), text).unwrap();
        let source = dir.join(format!("{name}.lean"));
        let output = dir.join(format!("{name}.olean"));
        run(
            &project,
            "lean",
            &[
                "--root",
                dir.to_str().unwrap(),
                "-o",
                output.to_str().unwrap(),
                source.to_str().unwrap(),
            ],
            Some(dir),
        )
    };
    assert!(compile("Subject", "def subject : Prop := True\n").success);
    assert!(
        !compile(
            "Extra",
            "theorem bad : NoSuchNamespace.subject := by trivial\n"
        )
        .success
    ); // Missing Subject import must actually fail.
    assert!(compile("Extra", "import Subject\naxiom extra : subject\n").success);
    let checker = project.join(".lake/build/bin/proofcheck");
    let check = || {
        run(
            &project,
            &checker,
            &[
                "exact",
                "Subject",
                "Candidate",
                "Candidate.correct",
                "subject",
                "Init",
                "Lean",
                "Std",
                "Extra",
            ],
            Some(dir),
        )
    };
    for (name, source, accept, reason) in [
        (
            "correct",
            "import Subject\ntheorem Candidate.correct : subject := True.intro\n",
            true,
            "exact_generated_statement",
        ),
        (
            "weaker",
            "import Subject\ntheorem Candidate.correct : True := True.intro\n",
            false,
            "does not state subject",
        ),
        (
            "sorry",
            "import Subject\ntheorem Candidate.correct : subject := sorry\n",
            false,
            "sorryAx",
        ),
        (
            "unused axiom",
            "import Subject\naxiom unused : True\ntheorem Candidate.correct : subject := True.intro\n",
            false,
            "declares the axiom",
        ),
        (
            "transitive axiom",
            "import Subject\nimport Extra\ntheorem Candidate.correct : subject := extra\n",
            false,
            "extra",
        ),
        (
            "import",
            "import Subject\nimport Lake\ntheorem Candidate.correct : subject := True.intro\n",
            false,
            "only the statement module",
        ),
        (
            "kernel bypass",
            "import Subject\nimport Lean\nopen Lean Elab Command\nset_option debug.skipKernelTC true\nrun_cmd liftTermElabM do\n  addDecl (.thmDecl { name := `Candidate.correct, levelParams := [], type := mkConst `subject, value := mkConst ``Nat.zero })\n",
            false,
            "kernel rejects",
        ),
        (
            "wrong owner",
            "import Subject\ntheorem other : subject := True.intro\n",
            false,
            "no theorem",
        ),
    ] {
        let compiled = compile("Candidate", source);
        assert!(
            compiled.success,
            "control {name} must elaborate before independent replay: {}",
            compiled.output
        );
        let r = check();
        assert_eq!(r.success, accept, "{name}: {r:?}: {}", r.output);
        assert!(r.output.contains(reason), "{name}: {r:?}: {}", r.output);
    }
}
#[test]
fn provenance_detects_program_spec_model_dependency_additions_and_tool_policy() {
    if !pinned_lean_available() {
        return;
    }
    let project = common();
    let work = Workspace::new(None).unwrap();
    let root = work.path();
    let model = root.join("Model.lean");
    let program = root.join("program.bin");
    let spec = root.join("spec.json");
    for (p, t) in [
        (&model, b"model".as_slice()),
        (&program, b"program"),
        (&spec, b"spec"),
    ] {
        std::fs::write(p, t).unwrap();
    }
    let id = Identity::capture(
        &[root.to_path_buf()],
        &[program.clone(), spec.clone()],
        &project,
    )
    .unwrap();
    assert!(id.stale(&project).unwrap().is_empty());
    for p in [&program, &spec, &model] {
        let old = std::fs::read(p).unwrap();
        std::fs::write(p, b"changed").unwrap();
        assert!(!id.stale(&project).unwrap().is_empty(), "{}", p.display());
        std::fs::write(p, old).unwrap();
    }
    let added = root.join("Dependency.lean");
    std::fs::write(&added, b"new").unwrap();
    assert!(!id.stale(&project).unwrap().is_empty());
    std::fs::remove_file(&added).unwrap();
    let mut forged = id.clone();
    forged
        .toolchain
        .insert("lean_sha256".into(), "wrong".into());
    assert!(!forged.stale(&project).unwrap().is_empty());
    std::fs::remove_file(&spec).unwrap();
    assert!(id.stale(&project).is_err());
}
#[test]
fn owned_workspaces_and_os_locks_do_not_leak_or_overlap() {
    let p;
    {
        let w = Workspace::new(None).unwrap();
        p = w.path().to_path_buf();
        let lock = ProjectLock::acquire(&p).unwrap();
        assert!(ProjectLock::acquire(&p).is_err());
        drop(lock);
        assert!(ProjectLock::acquire(&p).is_ok());
    }
    assert!(!p.exists());
}

#[cfg(target_os = "linux")]
#[test]
fn cli_interrupts_reap_their_subprocess_groups() {
    use std::time::Instant;
    for signal in ["-INT", "-TERM", "-HUP"] {
        let work = Workspace::new(None).unwrap();
        let file = work.path().join("pid");
        let mut child = Command::new(env!("CARGO_BIN_EXE_e5r"))
            .args([
                "exec",
                "--timeout",
                "20",
                "--memory-mib",
                "128",
                "--",
                "sh",
                "-c",
                "sleep 20 & echo $$ $! > \"$E5R_TEST_PID\"; wait",
            ])
            .env("E5R_TEST_PID", &file)
            .stdout(std::process::Stdio::null())
            .stderr(std::process::Stdio::null())
            .spawn()
            .unwrap();
        let start = Instant::now();
        while !file.exists() && start.elapsed() < Duration::from_secs(5) {
            std::thread::sleep(Duration::from_millis(20));
        }
        let ids = std::fs::read_to_string(&file).unwrap();
        let ids: Vec<_> = ids.split_whitespace().collect();
        assert_eq!(ids.len(), 2);
        assert!(
            Command::new("kill")
                .args([signal, &child.id().to_string()])
                .status()
                .unwrap()
                .success()
        );
        let deadline = Instant::now();
        while child.try_wait().unwrap().is_none() && deadline.elapsed() < Duration::from_secs(5) {
            std::thread::sleep(Duration::from_millis(20));
        }
        // Cleanup even if a regression leaves this test's own process group alive.
        let running = std::fs::read_to_string(format!("/proc/{}/stat", ids[1]))
            .is_ok_and(|s| !s.rsplit_once(") ").is_some_and(|(_, s)| s.starts_with('Z')));
        let _ = Command::new("kill")
            .args(["-KILL", "--", &format!("-{}", ids[0])])
            .stdout(std::process::Stdio::null())
            .stderr(std::process::Stdio::null())
            .status();
        let _ = child.kill();
        let status = child.wait().unwrap();
        assert!(!running, "{signal} left a live descendant");
        assert!(!status.success());
    }
}
