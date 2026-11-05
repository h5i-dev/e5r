//! Bounded command execution. Linux RSS is sampled across the process group,
//! not a hard cgroup bound: allocations between samples can exceed the cap.
//! Process groups handle cooperative descendants, not hostile sandbox escapes.
use serde::{Deserialize, Serialize};
use std::fs::{File, OpenOptions};
use std::io::{Read, Seek, SeekFrom};
use std::path::PathBuf;
use std::process::{Child, Command, Stdio};
use std::sync::atomic::{AtomicBool, AtomicU64, Ordering};
use std::sync::{Arc, OnceLock};
use std::time::{Duration, Instant};

static CANCELLED: OnceLock<Arc<AtomicBool>> = OnceLock::new();
fn cancellation_flag() -> &'static Arc<AtomicBool> {
    CANCELLED.get_or_init(|| Arc::new(AtomicBool::new(false)))
}
pub fn cancellation_requested() -> bool {
    cancellation_flag().load(Ordering::Relaxed)
}
/// CLI initialization only; embedding applications can supply their own token.
/// The signal handler performs only an atomic store. Cleanup happens in run().
pub fn install_signal_handlers() -> Result<(), String> {
    static INSTALLED: OnceLock<Result<(), String>> = OnceLock::new();
    INSTALLED
        .get_or_init(|| {
            for signal in [
                signal_hook::consts::SIGINT,
                signal_hook::consts::SIGTERM,
                signal_hook::consts::SIGHUP,
            ] {
                signal_hook::flag::register(signal, Arc::clone(cancellation_flag()))
                    .map_err(|e| e.to_string())?;
            }
            Ok(())
        })
        .clone()
}

#[derive(Clone, Copy, Debug)]
pub struct Limits {
    pub timeout: Duration,
    pub rss_mib: u64,
    pub log_bytes: u64,
}
impl Limits {
    pub fn new(timeout: Duration, rss_mib: u64) -> Self {
        Self {
            timeout,
            rss_mib,
            log_bytes: 8 * 1024 * 1024,
        }
    }
}
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum Exhaustion {
    Time,
    Memory,
    Output,
}
#[derive(Debug, Serialize)]
pub struct Run {
    pub success: bool,
    pub cancelled: bool,
    pub cleanup_complete: bool,
    pub code: Option<i32>,
    pub exhaustion: Option<Exhaustion>,
    pub output: String,
    pub seconds: f64,
    pub peak_rss_mib: u64,
    pub memory_monitor: &'static str,
}
struct Guard {
    child: Child,
    terminated: bool,
    cleanup_complete: bool,
}
impl Guard {
    fn terminate(&mut self) {
        if self.terminated {
            return;
        }
        self.terminated = true;
        #[cfg(unix)]
        {
            // The group was created by Command::process_group. Never target a
            // caller's group or a PID obtained from external input.
            let _ = Command::new("kill")
                .args(["-KILL", "--", &format!("-{}", self.child.id())])
                .stdout(Stdio::null())
                .stderr(Stdio::null())
                .status();
        }
        let _ = self.child.kill();
        let _ = self.child.wait();
        #[cfg(target_os = "linux")]
        {
            let start = Instant::now();
            loop {
                self.cleanup_complete =
                    group_has_live_members(self.child.id()).is_ok_and(|live| !live);
                if self.cleanup_complete || start.elapsed() >= Duration::from_secs(1) {
                    break;
                }
                std::thread::sleep(Duration::from_millis(10));
            }
        }
    }
}
impl Drop for Guard {
    fn drop(&mut self) {
        self.terminate();
    }
}
struct LogCleanup(PathBuf);
impl Drop for LogCleanup {
    fn drop(&mut self) {
        let _ = std::fs::remove_file(&self.0);
    }
}
static NEXT: AtomicU64 = AtomicU64::new(0);
fn log_file() -> std::io::Result<(PathBuf, File)> {
    loop {
        let path = std::env::temp_dir().join(format!(
            "e5r-run-{}-{}.log",
            std::process::id(),
            NEXT.fetch_add(1, Ordering::Relaxed)
        ));
        match OpenOptions::new()
            .read(true)
            .write(true)
            .create_new(true)
            .open(&path)
        {
            Ok(f) => return Ok((path, f)),
            Err(e) if e.kind() == std::io::ErrorKind::AlreadyExists => continue,
            Err(e) => return Err(e),
        }
    }
}
#[cfg(target_os = "linux")]
fn group_has_live_members(group: u32) -> std::io::Result<bool> {
    for entry in std::fs::read_dir("/proc")?.flatten() {
        let Ok(stat) = std::fs::read_to_string(entry.path().join("stat")) else {
            continue;
        };
        let Some((_, fields)) = stat.rsplit_once(") ") else {
            continue;
        };
        let mut fields = fields.split_whitespace();
        let state = fields.next();
        let pgrp = fields.nth(1).and_then(|s| s.parse::<u32>().ok());
        if pgrp == Some(group) && !matches!(state, Some("Z" | "X")) {
            return Ok(true);
        }
    }
    Ok(false)
}

#[cfg(target_os = "linux")]
fn group_rss(group: u32) -> std::io::Result<u64> {
    let mut kb = 0;
    for entry in std::fs::read_dir("/proc")?.flatten() {
        if !entry
            .file_name()
            .to_string_lossy()
            .bytes()
            .all(|b| b.is_ascii_digit())
        {
            continue;
        }
        let Ok(stat) = std::fs::read_to_string(entry.path().join("stat")) else {
            continue;
        };
        let Some((_, fields)) = stat.rsplit_once(") ") else {
            continue;
        };
        // fields start at stat field 3 (state); field 5 is process group.
        if fields
            .split_whitespace()
            .nth(2)
            .and_then(|s| s.parse::<u32>().ok())
            != Some(group)
        {
            continue;
        }
        let Ok(status) = std::fs::read_to_string(entry.path().join("status")) else {
            continue;
        };
        kb += status
            .lines()
            .find_map(|s| s.strip_prefix("VmRSS:"))
            .and_then(|s| s.split_whitespace().next()?.parse::<u64>().ok())
            .unwrap_or(0);
    }
    Ok(kb.div_ceil(1024))
}

pub fn run(cmd: Command, limits: Limits) -> Result<Run, String> {
    run_with_cancel(cmd, limits, cancellation_flag())
}
pub fn run_with_cancel(
    mut cmd: Command,
    limits: Limits,
    cancellation: &AtomicBool,
) -> Result<Run, String> {
    if cancellation.load(Ordering::Relaxed) {
        return Err("execution cancelled before start".into());
    }
    if limits.timeout.is_zero() || limits.rss_mib == 0 || limits.log_bytes == 0 {
        return Err("execution limits must be positive".into());
    }
    #[cfg(not(target_os = "linux"))]
    return Err("bounded verification requires Linux /proc RSS monitoring".into());
    #[cfg(target_os = "linux")]
    {
        use std::os::unix::process::CommandExt;
        // Validate the monitor before starting work. Missing /proc is an error.
        if !Command::new("kill")
            .args(["-0", &std::process::id().to_string()])
            .stdout(Stdio::null())
            .stderr(Stdio::null())
            .status()
            .is_ok_and(|s| s.success())
        {
            return Err("process-group cleanup requires a working kill executable".into());
        }
        group_rss(std::process::id()).map_err(|e| format!("RSS monitor: {e}"))?;
        let (path, mut log) = log_file().map_err(|e| format!("log: {e}"))?;
        let _log_cleanup = LogCleanup(path.clone());
        let child = cmd
            .process_group(0)
            .stdin(Stdio::null())
            .stdout(Stdio::from(log.try_clone().map_err(|e| e.to_string())?))
            .stderr(Stdio::from(log.try_clone().map_err(|e| e.to_string())?))
            .spawn();
        let child = match child {
            Ok(c) => c,
            Err(e) => {
                let _ = std::fs::remove_file(path);
                return Err(format!("cannot start command: {e}"));
            }
        };
        let mut guard = Guard {
            child,
            terminated: false,
            cleanup_complete: false,
        };
        let start = Instant::now();
        let mut peak = 0;
        let mut exhaustion = None;
        let mut cancelled = false;
        let status = loop {
            if cancellation.load(Ordering::Relaxed) {
                cancelled = true;
                guard.terminate();
                break None;
            }
            peak = peak.max(group_rss(guard.child.id()).map_err(|e| format!("RSS monitor: {e}"))?);
            exhaustion = if start.elapsed() >= limits.timeout {
                Some(Exhaustion::Time)
            } else if peak > limits.rss_mib {
                Some(Exhaustion::Memory)
            } else if log.metadata().map_err(|e| e.to_string())?.len() > limits.log_bytes {
                Some(Exhaustion::Output)
            } else {
                exhaustion
            };
            if exhaustion.is_some() {
                guard.terminate();
                break None;
            }
            if let Some(s) = guard.child.try_wait().map_err(|e| format!("wait: {e}"))? {
                break Some(s);
            }
            std::thread::sleep(Duration::from_millis(50));
        };
        // Kill remaining group members even after a successful parent exit.
        guard.terminate();
        let len = log.metadata().map_err(|e| e.to_string())?.len();
        log.seek(SeekFrom::Start(len.saturating_sub(limits.log_bytes)))
            .map_err(|e| e.to_string())?;
        let mut bytes = Vec::new();
        log.take(limits.log_bytes)
            .read_to_end(&mut bytes)
            .map_err(|e| e.to_string())?;
        Ok(Run {
            success: status.is_some_and(|s| s.success()) && guard.cleanup_complete,
            cleanup_complete: guard.cleanup_complete,
            cancelled,
            code: status.and_then(|s| s.code()),
            exhaustion,
            output: String::from_utf8_lossy(&bytes).into_owned()
                + if cancelled {
                    "\nerror: execution cancelled"
                } else if !guard.cleanup_complete {
                    "\nerror: process group cleanup incomplete"
                } else {
                    ""
                },
            seconds: start.elapsed().as_secs_f64(),
            peak_rss_mib: peak,
            memory_monitor: "linux_process_group_rss_sampled_50ms",
        })
    }
}

#[cfg(all(test, target_os = "linux"))]
mod tests {
    use super::*;
    fn shell(script: &str, limits: Limits) -> Run {
        let mut c = Command::new("sh");
        c.args(["-c", script]);
        run(c, limits).unwrap()
    }
    fn limits() -> Limits {
        Limits::new(Duration::from_secs(5), 256)
    }
    fn stopped(pid: &str) -> bool {
        std::fs::read_to_string(format!("/proc/{pid}/stat")).map_or(true, |s| {
            s.rsplit_once(") ").is_some_and(|(_, s)| s.starts_with('Z'))
        })
    }
    #[test]
    fn captures_both_streams_and_nonzero_exit() {
        let r = shell("echo stdout; echo stderr >&2; exit 7", limits());
        assert!(!r.success);
        assert_eq!(r.code, Some(7));
        assert!(r.output.contains("stdout") && r.output.contains("stderr"));
        assert_eq!(r.exhaustion, None);
    }
    #[test]
    fn timeout_kills_descendants_and_preserves_unrelated_process() {
        let mut unrelated = Command::new("sleep").arg("20").spawn().unwrap();
        let mut l = limits();
        l.timeout = Duration::from_millis(200);
        let r = shell("sleep 20 & echo $!; wait", l);
        let pid = r.output.trim();
        assert!(pid.parse::<u32>().is_ok());
        assert_eq!(r.exhaustion, Some(Exhaustion::Time));
        assert!(stopped(pid));
        assert!(unrelated.try_wait().unwrap().is_none());
        unrelated.kill().unwrap();
        unrelated.wait().unwrap();
        assert!(r.seconds < 3.0);
    }
    #[test]
    fn successful_parent_does_not_leave_background_child() {
        let r = shell("sleep 20 & echo $!", limits());
        assert!(r.success);
        assert!(stopped(r.output.trim()));
        assert!(r.seconds < 3.0);
    }
    #[test]
    fn memory_is_sampled_across_descendants() {
        let mut l = limits();
        l.rss_mib = 24;
        let r = shell(
            "python3 -c 'import time; x=bytearray(80*1024*1024); time.sleep(5)' & wait",
            l,
        );
        assert_eq!(r.exhaustion, Some(Exhaustion::Memory), "{r:?}");
        assert!(r.peak_rss_mib > 24);
    }
    #[test]
    fn output_limit_and_non_utf8_are_reported() {
        let mut l = limits();
        l.log_bytes = 1024;
        let r = shell(
            "python3 -c 'import sys,time; sys.stdout.buffer.write(bytes([255])*4096); sys.stdout.flush(); time.sleep(5)'",
            l,
        );
        assert_eq!(r.exhaustion, Some(Exhaustion::Output));
        assert!(r.output.len() <= 3072); // UTF-8 replacement can expand bytes threefold.
    }
    #[test]
    fn spawn_errors_and_invalid_limits_are_errors() {
        assert!(run(Command::new("/e5r/no-such-command"), limits()).is_err());
        let mut l = limits();
        l.rss_mib = 0;
        assert!(run(Command::new("true"), l).is_err());
    }
}

#[cfg(all(test, target_os = "linux"))]
mod cancellation_tests {
    use super::*;
    #[test]
    fn caller_cancellation_stops_the_group_without_claiming_resource_exhaustion() {
        let cancellation = Arc::new(AtomicBool::new(false));
        let flag = Arc::clone(&cancellation);
        let cancel = std::thread::spawn(move || {
            std::thread::sleep(Duration::from_millis(150));
            flag.store(true, Ordering::Relaxed);
        });
        let mut command = Command::new("sh");
        command.args(["-c", "sleep 20 & echo $!; wait"]);
        let r = run_with_cancel(
            command,
            Limits::new(Duration::from_secs(5), 128),
            &cancellation,
        )
        .unwrap();
        cancel.join().unwrap();
        assert!(r.cancelled && !r.success);
        assert_eq!(r.exhaustion, None);
        assert!(r.seconds < 3.0);
        let pid = r.output.lines().next().unwrap();
        assert!(
            std::fs::read_to_string(format!("/proc/{pid}/stat")).map_or(true, |s| s
                .rsplit_once(") ")
                .is_some_and(|(_, s)| s.starts_with('Z')))
        );
    }
}
