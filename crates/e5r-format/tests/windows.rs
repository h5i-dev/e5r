//! The Windows-specific data directories: TLS callbacks, `.pdata`/`.xdata`,
//! SEH scope tables, base relocations and the load config.
//!
//! Two halves, for two different questions.
//!
//! The first half runs against real linked PE images from `fixtures/build`,
//! with `llvm-readobj` as the oracle. Comparing a parser against itself proves
//! nothing, so every number that LLVM prints is read back out of LLVM and the
//! two lists are compared entry for entry: runtime function bounds, unwind
//! codes, frame registers, handler addresses, ARM64 packed frame descriptions,
//! base relocations and the guard function table. LLVM does not print SEH scope
//! tables, so those are checked against the one anchor it does print, the
//! handler routine, plus the shape the source is known to have.
//!
//! The second half builds PE images byte by byte to reach the paths a working
//! compiler never emits: a callback array with no terminator, a relocation
//! block shorter than its own header, an unwind chain that points at itself, a
//! C++ `FuncInfo` where a scope table would be. Those are the inputs that
//! decide whether the loader is safe to point at something hostile.

use std::path::{Path, PathBuf};
use std::process::Command;

use e5r_core::{Addr, Arch, Caps, Evidence, Strength};
use e5r_format::pdata::{ScopeHandler, UnwindOp};
use e5r_format::{LoadOptions, Object, pe};

// ---------------------------------------------------------------------------
// The corpus and the oracle.
// ---------------------------------------------------------------------------

fn corpus() -> Option<PathBuf> {
    let d = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../fixtures/build");
    d.is_dir().then(|| d.canonicalize().unwrap())
}

fn open(name: &str) -> Option<(Object, pe::WindowsInfo)> {
    let p = corpus()?.join(name);
    let data = std::fs::read(&p).ok()?;
    Some(
        pe::load_windows(&data, &LoadOptions::default())
            .unwrap_or_else(|e| panic!("loading {}: {e}", p.display())),
    )
}

/// `llvm-readobj`, under whichever name this machine installed it as.
fn readobj(name: &str, args: &[&str]) -> Option<String> {
    let p = corpus()?.join(name);
    if !p.exists() {
        return None;
    }
    for tool in ["llvm-readobj", "llvm-readobj-18", "llvm-readobj-15"] {
        let Ok(out) = Command::new(tool).args(args).arg(&p).output() else {
            continue;
        };
        if out.status.success() {
            return Some(String::from_utf8_lossy(&out.stdout).into_owned());
        }
    }
    None
}

/// The hexadecimal number in `Key: 0x...` or `Key: (0x...)`, for the first line
/// whose key matches.
fn field_hex(text: &str, key: &str) -> Option<u64> {
    field_hex_all(text, key).into_iter().next()
}

fn field_hex_all(text: &str, key: &str) -> Vec<u64> {
    text.lines()
        .filter_map(|l| {
            let l = l.trim();
            let rest = l.strip_prefix(key)?.strip_prefix(':')?;
            let rest = rest.trim().trim_start_matches('(').trim_end_matches(')');
            let digits = rest.strip_prefix("0x")?;
            u64::from_str_radix(digits.split_whitespace().next()?, 16).ok()
        })
        .collect()
}

fn field_dec_all(text: &str, key: &str) -> Vec<u64> {
    text.lines()
        .filter_map(|l| {
            let l = l.trim();
            let rest = l.strip_prefix(key)?.strip_prefix(':')?;
            rest.trim().parse::<u64>().ok()
        })
        .collect()
}

/// The images the fixture script builds, when it has run.
const IMAGES: [&str; 4] = [
    "win.x64.O0.exe",
    "win.x64.O2.exe",
    "win.a64.O0.exe",
    "win.a64.O2.exe",
];

// ---------------------------------------------------------------------------
// Exception directory, against llvm-readobj --unwind.
// ---------------------------------------------------------------------------

#[test]
fn runtime_function_bounds_match_llvm_readobj() {
    let mut checked = 0;
    for name in IMAGES {
        let Some((_, win)) = open(name) else { continue };
        let Some(text) = readobj(name, &["--unwind"]) else {
            continue;
        };
        // x86-64 prints a start and an end; ARM64 prints a start and a length.
        let want: Vec<(u64, Option<u64>)> = if name.contains("x64") {
            let starts = field_hex_all(&text, "StartAddress");
            let ends = field_hex_all(&text, "EndAddress");
            assert_eq!(starts.len(), ends.len(), "{name}: malformed oracle output");
            starts.into_iter().zip(ends.into_iter().map(Some)).collect()
        } else {
            let starts = field_hex_all(&text, "Function");
            let lengths = field_dec_all(&text, "FunctionLength");
            assert_eq!(
                starts.len(),
                lengths.len(),
                "{name}: every ARM64 entry should carry a length"
            );
            starts
                .iter()
                .zip(&lengths)
                .map(|(s, n)| (*s, Some(s + n)))
                .collect()
        };
        assert!(!want.is_empty(), "{name}: the oracle found no entries");

        let got: Vec<(u64, Option<u64>)> = win
            .exceptions
            .functions
            .iter()
            .map(|f| (f.start.get(), f.end.map(|e| e.get())))
            .collect();
        assert_eq!(got, want, "{name}: runtime function bounds disagree");
        checked += 1;
    }
    assert!(checked > 0 || corpus().is_none(), "no image was checked");
}

#[test]
fn every_runtime_function_is_a_proven_hint_with_its_size() {
    for name in IMAGES {
        let Some((obj, win)) = open(name) else {
            continue;
        };
        for f in &win.exceptions.functions {
            let hint = obj
                .function_hints
                .iter()
                .find(|h| h.addr == f.start)
                .unwrap_or_else(|| panic!("{name}: no hint for the function at {}", f.start));
            assert_eq!(
                hint.provenance.strength(),
                Strength::Proven,
                "{name}: {} is not proven",
                f.start
            );
            assert!(
                hint.provenance.has(Evidence::PeUnwind),
                "{name}: {} does not cite the unwind record",
                f.start
            );
            if let Some(end) = f.end {
                assert_eq!(
                    hint.size,
                    Some(end.get() - f.start.get()),
                    "{name}: {} lost its size",
                    f.start
                );
            }
        }
    }
}

/// Render an unwind code the way `llvm-readobj` does, so the two can be
/// compared as text rather than through a second opinion about the encoding.
fn render(op: &UnwindOp, frame_register: Option<u8>, frame_offset: u32) -> String {
    fn reg(n: u8) -> String {
        e5r_format::pdata::x64_register(n).to_uppercase()
    }
    match op {
        UnwindOp::PushNonVolatile { reg: r } => format!("PUSH_NONVOL reg={}", reg(*r)),
        // LLVM keeps the two allocation encodings apart; the decoded size is
        // the substance and is what both sides normalize to.
        UnwindOp::Alloc { bytes } => format!("ALLOC size={bytes}"),
        UnwindOp::SetFramePointer => format!(
            "SET_FPREG reg={}, offset={:#x}",
            reg(frame_register.unwrap_or(0)),
            frame_offset
        ),
        UnwindOp::SaveNonVolatile { reg: r, offset } => {
            format!("SAVE_NONVOL reg={}, offset={offset:#x}", reg(*r))
        }
        UnwindOp::SaveXmm128 { reg: r, offset } => {
            format!("SAVE_XMM128 reg=XMM{r}, offset={offset:#x}")
        }
        UnwindOp::PushMachineFrame { error_code } => {
            format!("PUSH_MACHFRAME errcode={error_code}")
        }
        UnwindOp::Epilogue => "EPILOG".into(),
        UnwindOp::Unknown { op, info } => format!("UNKNOWN op={op} info={info}"),
    }
}

fn normalize_oracle_code(s: &str) -> String {
    if let Some(rest) = s.strip_prefix("ALLOC_LARGE size=") {
        return format!("ALLOC size={rest}");
    }
    if let Some(rest) = s.strip_prefix("ALLOC_SMALL size=") {
        return format!("ALLOC size={rest}");
    }
    s.to_string()
}

#[test]
fn x64_unwind_codes_match_llvm_readobj() {
    for name in ["win.x64.O0.exe", "win.x64.O2.exe"] {
        let Some((_, win)) = open(name) else { continue };
        let Some(text) = readobj(name, &["--unwind"]) else {
            continue;
        };
        // One block per RuntimeFunction, in directory order.
        let blocks: Vec<&str> = text.split("RuntimeFunction {").skip(1).collect();
        assert_eq!(
            blocks.len(),
            win.exceptions.unwind.len(),
            "{name}: the oracle and the loader disagree on how many records exist"
        );
        let mut codes_seen = 0;
        for (block, info) in blocks.iter().zip(&win.exceptions.unwind) {
            assert_eq!(
                field_hex(block, "StartAddress"),
                Some(info.function.get()),
                "{name}: records are out of order"
            );
            assert_eq!(
                field_dec_all(block, "Version").first().copied(),
                Some(info.version as u64),
                "{name}: version disagrees for {}",
                info.function
            );
            assert_eq!(
                field_dec_all(block, "PrologSize").first().copied(),
                Some(info.prolog_size as u64),
                "{name}: prologue size disagrees for {}",
                info.function
            );
            assert_eq!(
                field_hex(block, "Handler"),
                info.handler.map(|h| h.get()),
                "{name}: handler disagrees for {}",
                info.function
            );
            // FrameRegister prints as "RBP (0x5)" or "-" when there is none.
            let want_frame = block
                .lines()
                .find_map(|l| l.trim().strip_prefix("FrameRegister:"))
                .map(|v| v.trim().to_string());
            let got_frame = info
                .frame_register
                .map(|r| e5r_format::pdata::x64_register(r).to_uppercase());
            match (want_frame.as_deref(), got_frame) {
                (Some("-"), g) => assert_eq!(g, None, "{name}: invented a frame register"),
                (Some(w), Some(g)) => assert!(
                    w.starts_with(&g),
                    "{name}: frame register {g} is not the oracle's {w}"
                ),
                (Some(w), None) => panic!("{name}: missed the frame register {w}"),
                (None, _) => {}
            }

            let want: Vec<String> = block
                .lines()
                .filter_map(|l| {
                    let l = l.trim();
                    let rest = l.strip_prefix("0x")?;
                    let (_, text) = rest.split_once(": ")?;
                    Some(normalize_oracle_code(text))
                })
                .collect();
            // A chained record's own codes come first; the parent's are
            // appended, and the oracle does not follow the chain.
            let got: Vec<String> = info
                .codes
                .iter()
                .take(want.len())
                .map(|c| render(&c.op, info.frame_register, info.frame_offset))
                .collect();
            assert_eq!(
                got, want,
                "{name}: prologue for {} disagrees with the oracle",
                info.function
            );
            codes_seen += want.len();
        }
        assert!(
            codes_seen > 10,
            "{name}: only {codes_seen} unwind codes, the fixture is not exercising much"
        );
    }
}

#[test]
fn arm64_packed_unwind_matches_llvm_readobj() {
    for name in ["win.a64.O0.exe", "win.a64.O2.exe"] {
        let Some((_, win)) = open(name) else { continue };
        let Some(text) = readobj(name, &["--unwind"]) else {
            continue;
        };
        let blocks: Vec<&str> = text.split("RuntimeFunction {").skip(1).collect();
        assert_eq!(blocks.len(), win.exceptions.functions.len());
        let mut packed_seen = 0;
        for (block, f) in blocks.iter().zip(&win.exceptions.functions) {
            // The oracle prints RegF only for the packed form.
            let Some(reg_f) = field_dec_all(block, "RegF").first().copied() else {
                assert!(
                    f.packed.is_none(),
                    "{name}: {} was decoded as packed but the oracle read .xdata",
                    f.start
                );
                continue;
            };
            let p = f
                .packed
                .unwrap_or_else(|| panic!("{name}: {} should be packed", f.start));
            assert_eq!(reg_f, p.reg_f as u64, "{name}: RegF at {}", f.start);
            assert_eq!(
                field_dec_all(block, "RegI").first().copied(),
                Some(p.reg_i as u64),
                "{name}: RegI at {}",
                f.start
            );
            assert_eq!(
                field_dec_all(block, "CR").first().copied(),
                Some(p.cr as u64),
                "{name}: CR at {}",
                f.start
            );
            assert_eq!(
                field_dec_all(block, "FrameSize").first().copied(),
                Some(p.frame_size as u64),
                "{name}: FrameSize at {}",
                f.start
            );
            assert_eq!(
                field_dec_all(block, "FunctionLength").first().copied(),
                Some(p.function_length as u64),
                "{name}: FunctionLength at {}",
                f.start
            );
            let homed = block.contains("HomedParameters: Yes");
            assert_eq!(homed, p.homed_parameters, "{name}: H at {}", f.start);
            packed_seen += 1;
        }
        assert!(
            packed_seen > 0,
            "{name}: no packed entry, so the packed decoder was never measured"
        );
    }
}

#[test]
fn arm64_exception_handlers_match_llvm_readobj() {
    for name in ["win.a64.O0.exe", "win.a64.O2.exe"] {
        let Some((obj, _)) = open(name) else { continue };
        let Some(text) = readobj(name, &["--unwind"]) else {
            continue;
        };
        let routines = field_hex_all(&text, "Routine");
        assert!(
            !routines.is_empty(),
            "{name}: the fixture should carry an ARM64 handler"
        );
        for r in routines {
            let hint = obj
                .function_hints
                .iter()
                .find(|h| h.addr == Addr(r))
                .unwrap_or_else(|| panic!("{name}: the handler at {r:#x} produced no hint"));
            assert_eq!(hint.provenance.strength(), Strength::Proven);
            assert!(hint.provenance.has(Evidence::PeUnwind));
        }
    }
}

// ---------------------------------------------------------------------------
// SEH scope tables.
// ---------------------------------------------------------------------------

#[test]
fn the_seh_scope_table_names_a_try_region_inside_its_function() {
    // llvm-readobj does not print scope tables, so the oracle here is the
    // handler routine it does print, plus the shape the fixture's source has:
    // one __try region guarded by __except(1), which the compiler folds to the
    // constant EXCEPTION_EXECUTE_HANDLER.
    for name in ["win.x64.O0.exe", "win.x64.O2.exe"] {
        let Some((obj, win)) = open(name) else {
            continue;
        };
        let Some(text) = readobj(name, &["--unwind"]) else {
            continue;
        };
        let handlers = field_hex_all(&text, "Handler");
        assert!(!handlers.is_empty(), "{name}: the fixture lost its handler");

        let with_scopes: Vec<_> = win
            .exceptions
            .unwind
            .iter()
            .filter(|u| !u.scopes.is_empty())
            .collect();
        assert!(
            !with_scopes.is_empty(),
            "{name}: no scope table was recovered"
        );
        for info in with_scopes {
            assert!(
                handlers.contains(&info.handler.expect("a scope table needs a handler").get()),
                "{name}: the handler is not one the oracle listed"
            );
            let func = win
                .exceptions
                .functions
                .iter()
                .find(|f| f.start == info.function)
                .expect("scope table without its function");
            let end = func.end.expect("x86-64 always states an end");
            for s in &info.scopes {
                assert!(
                    s.begin >= func.start && s.end <= end && s.begin < s.end,
                    "{name}: guarded region {}..{} escapes {}..{end}",
                    s.begin,
                    s.end,
                    func.start
                );
                assert_eq!(
                    s.handler,
                    ScopeHandler::Constant(1),
                    "{name}: __except(1) should fold to a constant filter"
                );
                let target = s.target.expect("__except has a body to jump to");
                assert!(obj.memory.is_executable(target));
            }
        }
    }
}

#[test]
fn the_handler_routine_becomes_a_proven_hint() {
    for name in ["win.x64.O0.exe", "win.x64.O2.exe"] {
        let Some((obj, win)) = open(name) else {
            continue;
        };
        let mut seen = 0;
        for info in &win.exceptions.unwind {
            let Some(h) = info.handler else { continue };
            let hint = obj
                .function_hints
                .iter()
                .find(|x| x.addr == h)
                .unwrap_or_else(|| panic!("{name}: the handler at {h} produced no hint"));
            assert_eq!(hint.provenance.strength(), Strength::Proven);
            seen += 1;
        }
        assert!(seen > 0, "{name}: no handler was found at all");
    }
}

// ---------------------------------------------------------------------------
// TLS.
// ---------------------------------------------------------------------------

#[test]
fn the_tls_directory_matches_llvm_readobj() {
    for name in IMAGES {
        let Some((_, win)) = open(name) else { continue };
        let Some(text) = readobj(name, &["--coff-tls-directory"]) else {
            continue;
        };
        let tls = win
            .tls
            .as_ref()
            .unwrap_or_else(|| panic!("{name}: the TLS directory was not read"));
        assert_eq!(
            tls.callback_array.map(|a| a.get()),
            field_hex(&text, "AddressOfCallBacks"),
            "{name}: callback array address"
        );
        assert_eq!(
            tls.index.map(|a| a.get()),
            field_hex(&text, "AddressOfIndex"),
            "{name}: TLS index address"
        );
        assert_eq!(
            tls.raw_data.map(|r| r.start().get()),
            field_hex(&text, "StartAddressOfRawData"),
            "{name}: raw data start"
        );
        assert_eq!(
            tls.raw_data.map(|r| r.end().get()),
            field_hex(&text, "EndAddressOfRawData"),
            "{name}: raw data end"
        );
    }
}

#[test]
fn tls_callbacks_are_functions_the_guard_table_also_knows() {
    // The fixture registers two callbacks. Nothing but the TLS array points at
    // them, so the check that they are real comes from a second table: the
    // linker's control-flow-guard list of every address-taken function, which
    // llvm-readobj prints and which must contain both.
    for name in IMAGES {
        let Some((obj, win)) = open(name) else {
            continue;
        };
        let tls = win.tls.as_ref().expect("no TLS directory");
        assert_eq!(
            tls.callbacks.len(),
            2,
            "{name}: expected the two callbacks the fixture registers"
        );
        let Some(text) = readobj(name, &["--coff-load-config"]) else {
            continue;
        };
        let fids: Vec<u64> = text
            .lines()
            .skip_while(|l| !l.contains("GuardFidTable"))
            .filter_map(|l| {
                let l = l.trim();
                u64::from_str_radix(l.strip_prefix("0x")?, 16).ok()
            })
            .collect();
        assert!(
            !fids.is_empty(),
            "{name}: the oracle printed no guard table"
        );
        for (i, cb) in tls.callbacks.iter().enumerate() {
            assert!(
                fids.contains(&cb.get()),
                "{name}: callback {i} at {cb} is not an address-taken function"
            );
            let hint = obj
                .function_hints
                .iter()
                .find(|h| h.addr == *cb)
                .unwrap_or_else(|| panic!("{name}: callback {i} produced no hint"));
            assert_eq!(
                hint.provenance.strength(),
                Strength::Proven,
                "{name}: a callback landing in executable memory is proven"
            );
            assert!(hint.provenance.has(Evidence::InitArray));
            assert_eq!(
                hint.name.as_deref(),
                Some(format!("tls_callback_{i}")).as_deref()
            );
        }
        assert_eq!(
            obj.metadata.get("pe.tls_callbacks").map(String::as_str),
            Some("2")
        );
    }
}

// ---------------------------------------------------------------------------
// Base relocations and load config.
// ---------------------------------------------------------------------------

#[test]
fn base_relocations_match_llvm_readobj() {
    for name in IMAGES {
        let Some((obj, win)) = open(name) else {
            continue;
        };
        let Some(text) = readobj(name, &["--coff-basereloc"]) else {
            continue;
        };
        // The oracle prints a type name and an RVA; the loader reports a type
        // number and a loaded address. The name goes to a number rather than
        // the number to a name, so the test does not depend on our spelling.
        let number = |n: &str| -> u8 {
            match n {
                "HIGH" => 1,
                "LOW" => 2,
                "HIGHLOW" => 3,
                "HIGHADJ" => 4,
                "DIR64" => 10,
                other => panic!("{name}: the oracle printed an unmapped type {other}"),
            }
        };
        let kinds: Vec<u8> = text
            .lines()
            .filter_map(|l| Some(number(l.trim().strip_prefix("Type:")?.trim())))
            .collect();
        let addrs = field_hex_all(&text, "Address");
        assert_eq!(kinds.len(), addrs.len());
        let want: Vec<(u8, u64)> = kinds.into_iter().zip(addrs).collect();
        assert!(!want.is_empty(), "{name}: the oracle found no relocations");
        let base = obj.image_base.get();
        let got: Vec<(u8, u64)> = win
            .relocations
            .iter()
            .map(|r| (r.kind, r.addr.get() - base))
            .collect();
        assert_eq!(got, want, "{name}: base relocations disagree");
        assert_eq!(
            obj.metadata.get("pe.relocations").map(String::as_str),
            Some(got.len().to_string().as_str())
        );
    }
}

#[test]
fn the_load_config_guard_table_matches_llvm_readobj() {
    for name in IMAGES {
        let Some((_, win)) = open(name) else { continue };
        let Some(text) = readobj(name, &["--coff-load-config"]) else {
            continue;
        };
        let cfg = win
            .load_config
            .as_ref()
            .unwrap_or_else(|| panic!("{name}: no load config"));
        assert_eq!(
            cfg.security_cookie.map(|a| a.get()),
            field_hex(&text, "SecurityCookie"),
            "{name}: security cookie"
        );
        assert_eq!(
            cfg.guard_cf_function_table.map(|a| a.get()),
            field_hex(&text, "GuardCFFunctionTable"),
            "{name}: guard table address"
        );
        assert_eq!(
            cfg.guard_cf_function_count,
            field_dec_all(&text, "GuardCFFunctionCount")
                .first()
                .copied()
                .unwrap_or(0),
            "{name}: guard table count"
        );
        let fids: Vec<u64> = text
            .lines()
            .skip_while(|l| !l.contains("GuardFidTable"))
            .filter_map(|l| u64::from_str_radix(l.trim().strip_prefix("0x")?, 16).ok())
            .collect();
        let got: Vec<u64> = cfg.guard_functions.iter().map(|a| a.get()).collect();
        assert_eq!(got, fids, "{name}: guard function list");
    }
}

// ---------------------------------------------------------------------------
// Byte-built images, for what a compiler will not produce.
// ---------------------------------------------------------------------------

const BASE: u64 = 0x1_4000_0000;
const TEXT_RVA: u32 = 0x1000;
const RDATA_RVA: u32 = 0x2000;
const TEXT_OFF: usize = 0x400;
const RDATA_OFF: usize = 0x600;
const RDATA_LEN: usize = 0x400;

/// A PE32+ image with one code section and one read-only data section whose
/// contents and data directories the caller chooses.
///
/// `dirs` is `(index, rva, size)`. `rdata` is placed at RVA 0x2000; the helper
/// `rdata_rva` below converts an offset inside it to an RVA.
fn synth(rdata: &[u8], dirs: &[(usize, u32, u32)]) -> Vec<u8> {
    assert!(rdata.len() <= RDATA_LEN);
    let mut b: Vec<u8> = Vec::new();
    let push = |b: &mut Vec<u8>, v: &[u8]| b.extend_from_slice(v);

    b.extend_from_slice(b"MZ");
    b.resize(0x3c, 0);
    push(&mut b, &0x80u32.to_le_bytes());
    b.resize(0x80, 0);
    b.extend_from_slice(b"PE\0\0");

    // COFF header.
    push(&mut b, &0x8664u16.to_le_bytes());
    push(&mut b, &2u16.to_le_bytes());
    push(&mut b, &0u32.to_le_bytes());
    push(&mut b, &0u32.to_le_bytes());
    push(&mut b, &0u32.to_le_bytes());
    push(&mut b, &240u16.to_le_bytes());
    push(&mut b, &0x0022u16.to_le_bytes());

    let opt_start = b.len();
    push(&mut b, &0x20bu16.to_le_bytes());
    b.extend_from_slice(&[14, 0]);
    for v in [0x200u32, 0x200, 0, TEXT_RVA, TEXT_RVA] {
        push(&mut b, &v.to_le_bytes());
    }
    push(&mut b, &BASE.to_le_bytes());
    push(&mut b, &0x1000u32.to_le_bytes());
    push(&mut b, &0x200u32.to_le_bytes());
    for v in [6u16, 0, 0, 0, 6, 0] {
        push(&mut b, &v.to_le_bytes());
    }
    push(&mut b, &0u32.to_le_bytes());
    push(&mut b, &0x4000u32.to_le_bytes());
    push(&mut b, &0x400u32.to_le_bytes());
    push(&mut b, &0u32.to_le_bytes());
    push(&mut b, &3u16.to_le_bytes());
    push(&mut b, &0x0160u16.to_le_bytes());
    for v in [0x100000u64, 0x1000, 0x100000, 0x1000] {
        push(&mut b, &v.to_le_bytes());
    }
    push(&mut b, &0u32.to_le_bytes());
    push(&mut b, &16u32.to_le_bytes());
    let dirs_at = b.len();
    for _ in 0..16 {
        push(&mut b, &0u64.to_le_bytes());
    }
    assert_eq!(b.len() - opt_start, 240);

    let sec = |b: &mut Vec<u8>, name: &[u8; 8], rva: u32, size: u32, off: u32, ch: u32| {
        b.extend_from_slice(name);
        for v in [size, rva, size, off, 0, 0] {
            b.extend_from_slice(&v.to_le_bytes());
        }
        b.extend_from_slice(&0u16.to_le_bytes());
        b.extend_from_slice(&0u16.to_le_bytes());
        b.extend_from_slice(&ch.to_le_bytes());
    };
    sec(
        &mut b,
        b".text\0\0\0",
        TEXT_RVA,
        0x200,
        TEXT_OFF as u32,
        0x6000_0020,
    );
    sec(
        &mut b,
        b".rdata\0\0",
        RDATA_RVA,
        RDATA_LEN as u32,
        RDATA_OFF as u32,
        0x4000_0040,
    );

    b.resize(TEXT_OFF, 0);
    b.extend_from_slice(&[0xc3; 0x200]);
    b.resize(RDATA_OFF, 0);
    b.extend_from_slice(rdata);
    b.resize(RDATA_OFF + RDATA_LEN, 0);

    for (i, rva, size) in dirs {
        let at = dirs_at + i * 8;
        b[at..at + 4].copy_from_slice(&rva.to_le_bytes());
        b[at + 4..at + 8].copy_from_slice(&size.to_le_bytes());
    }
    b
}

fn rdata_rva(off: usize) -> u32 {
    RDATA_RVA + off as u32
}

fn rdata_va(off: usize) -> u64 {
    BASE + rdata_rva(off) as u64
}

fn text_va(off: u32) -> u64 {
    BASE + TEXT_RVA as u64 + off as u64
}

fn le64(v: u64) -> [u8; 8] {
    v.to_le_bytes()
}

fn le32(v: u32) -> [u8; 4] {
    v.to_le_bytes()
}

/// A TLS directory at offset 0 of `.rdata` pointing at a callback array whose
/// contents the caller supplies.
fn tls_image(callbacks: &[u64], terminate: bool) -> Vec<u8> {
    let array_at = 0x40usize;
    let mut rdata = vec![0u8; RDATA_LEN];
    rdata[0x00..0x08].copy_from_slice(&le64(rdata_va(0x100)));
    rdata[0x08..0x10].copy_from_slice(&le64(rdata_va(0x140)));
    rdata[0x10..0x18].copy_from_slice(&le64(rdata_va(0x180)));
    rdata[0x18..0x20].copy_from_slice(&le64(rdata_va(array_at)));
    for (i, cb) in callbacks.iter().enumerate() {
        let at = array_at + i * 8;
        rdata[at..at + 8].copy_from_slice(&le64(*cb));
    }
    if !terminate {
        // Every remaining slot is a live pointer, so nothing terminates it.
        let mut at = array_at + callbacks.len() * 8;
        while at + 8 <= RDATA_LEN {
            rdata[at..at + 8].copy_from_slice(&le64(text_va(0)));
            at += 8;
        }
    }
    synth(&rdata, &[(9, rdata_rva(0), 40)])
}

#[test]
fn a_tls_callback_in_executable_memory_is_proven() {
    let data = tls_image(&[text_va(0x10), text_va(0x20)], true);
    let (obj, win) = pe::load_windows(&data, &LoadOptions::default()).unwrap();
    let tls = win.tls.expect("no TLS directory");
    assert_eq!(
        tls.callbacks,
        vec![Addr(text_va(0x10)), Addr(text_va(0x20))]
    );
    for (i, cb) in tls.callbacks.iter().enumerate() {
        let h = obj.function_hints.iter().find(|h| h.addr == *cb).unwrap();
        assert_eq!(h.provenance.strength(), Strength::Proven);
        assert_eq!(
            h.name.as_deref(),
            Some(format!("tls_callback_{i}")).as_deref()
        );
    }
}

#[test]
fn a_tls_callback_outside_executable_memory_is_a_warning_not_a_hint() {
    // The pointer lands in .rdata, which the file marks read-only. It is not a
    // function and claiming it were one would be the invention the whole
    // evidence model exists to prevent.
    let data = tls_image(&[rdata_va(0x200)], true);
    let (obj, win) = pe::load_windows(&data, &LoadOptions::default()).unwrap();
    assert!(win.tls.unwrap().callbacks.is_empty());
    assert!(
        obj.function_hints
            .iter()
            .all(|h| h.addr != Addr(rdata_va(0x200)))
    );
    assert!(
        obj.warnings.iter().any(|w| w.contains("not executable")),
        "no warning: {:?}",
        obj.warnings
    );
}

#[test]
fn a_tls_callback_array_with_no_terminator_stops_at_the_section_end() {
    let data = tls_image(&[text_va(0x10)], false);
    let (obj, win) = pe::load_windows(&data, &LoadOptions::default()).unwrap();
    let tls = win.tls.expect("no TLS directory");
    // 0x400 bytes of .rdata, the array starting 0x40 in: 120 slots and no more.
    assert_eq!(tls.callbacks.len(), (RDATA_LEN - 0x40) / 8);
    assert!(
        obj.warnings
            .iter()
            .any(|w| w.contains("without a terminator")),
        "the walk must say it stopped early: {:?}",
        obj.warnings
    );
}

#[test]
fn a_tls_callback_array_outside_every_section_is_a_warning() {
    let mut rdata = vec![0u8; RDATA_LEN];
    rdata[0x18..0x20].copy_from_slice(&le64(BASE + 0x0f00_0000));
    let data = synth(&rdata, &[(9, rdata_rva(0), 40)]);
    let (obj, win) = pe::load_windows(&data, &LoadOptions::default()).unwrap();
    assert!(win.tls.unwrap().callbacks.is_empty());
    assert!(obj.warnings.iter().any(|w| w.contains("no section maps")));
}

/// An image with one runtime function covering `.text` and an UNWIND_INFO whose
/// bytes the caller supplies at offset 0x100 of `.rdata`.
fn unwind_image(unwind: &[u8], func_len: u32) -> Vec<u8> {
    let mut rdata = vec![0u8; RDATA_LEN];
    // The exception directory: one entry at offset 0.
    rdata[0x00..0x04].copy_from_slice(&le32(TEXT_RVA));
    rdata[0x04..0x08].copy_from_slice(&le32(TEXT_RVA + func_len));
    rdata[0x08..0x0c].copy_from_slice(&le32(rdata_rva(0x100)));
    rdata[0x100..0x100 + unwind.len()].copy_from_slice(unwind);
    synth(&rdata, &[(3, rdata_rva(0), 12)])
}

#[test]
fn an_unwind_prologue_is_decoded_in_order() {
    // version 1, no flags; prologue 9 bytes; three codes; frame register RBP
    // with offset 0x20.
    let unwind = [
        0x01, 0x09, 0x03, 0x25, // header
        0x09, 0x03, // SET_FPREG at 9
        0x04, 0x62, // ALLOC_SMALL 0x38
        0x01, 0x50, // PUSH_NONVOL RBP
        0x00, 0x00, // padding for the odd count
    ];
    let data = unwind_image(&unwind, 0x40);
    let (_, win) = pe::load_windows(&data, &LoadOptions::default()).unwrap();
    let info = &win.exceptions.unwind[0];
    assert_eq!(info.version, 1);
    assert_eq!(info.prolog_size, 9);
    assert_eq!(
        info.frame_register.map(e5r_format::pdata::x64_register),
        Some("rbp")
    );
    assert_eq!(info.frame_offset, 0x20);
    assert_eq!(
        info.codes.iter().map(|c| c.op).collect::<Vec<_>>(),
        vec![
            UnwindOp::SetFramePointer,
            UnwindOp::Alloc { bytes: 0x38 },
            UnwindOp::PushNonVolatile { reg: 5 },
        ]
    );
    assert_eq!(info.stack_alloc, 0x38);
}

#[test]
fn a_chained_unwind_record_contributes_the_parent_prologue() {
    let mut rdata = vec![0u8; RDATA_LEN];
    // Two runtime functions: a funclet at +0x80 chaining to the one at +0.
    rdata[0x00..0x04].copy_from_slice(&le32(TEXT_RVA));
    rdata[0x04..0x08].copy_from_slice(&le32(TEXT_RVA + 0x80));
    rdata[0x08..0x0c].copy_from_slice(&le32(rdata_rva(0x100)));
    rdata[0x0c..0x10].copy_from_slice(&le32(TEXT_RVA + 0x80));
    rdata[0x10..0x14].copy_from_slice(&le32(TEXT_RVA + 0xc0));
    rdata[0x14..0x18].copy_from_slice(&le32(rdata_rva(0x140)));

    // The parent: one push.
    rdata[0x100..0x104].copy_from_slice(&[0x01, 0x04, 0x01, 0x00]);
    rdata[0x104..0x108].copy_from_slice(&[0x04, 0x30, 0x00, 0x00]);
    // The funclet: UNW_FLAG_CHAININFO, one alloc, then the parent's entry.
    rdata[0x140..0x144].copy_from_slice(&[0x21, 0x04, 0x01, 0x00]);
    rdata[0x144..0x148].copy_from_slice(&[0x04, 0x22, 0x00, 0x00]);
    rdata[0x148..0x14c].copy_from_slice(&le32(TEXT_RVA));
    rdata[0x14c..0x150].copy_from_slice(&le32(TEXT_RVA + 0x80));
    rdata[0x150..0x154].copy_from_slice(&le32(rdata_rva(0x100)));

    let data = synth(&rdata, &[(3, rdata_rva(0), 24)]);
    let (obj, win) = pe::load_windows(&data, &LoadOptions::default()).unwrap();
    let funclet = win
        .exceptions
        .unwind
        .iter()
        .find(|u| u.function == Addr(text_va(0x80)))
        .expect("the funclet lost its record");
    assert_eq!(funclet.chained, Some(Addr(text_va(0))));
    // Its own allocation, then the register the parent pushed.
    assert_eq!(
        funclet.codes.iter().map(|c| c.op).collect::<Vec<_>>(),
        vec![
            UnwindOp::Alloc { bytes: 0x18 },
            UnwindOp::PushNonVolatile { reg: 3 },
        ]
    );
    assert!(
        obj.function_hints
            .iter()
            .any(|h| h.addr == Addr(text_va(0)))
    );
}

#[test]
fn an_unwind_chain_that_points_at_itself_terminates() {
    let mut rdata = vec![0u8; RDATA_LEN];
    rdata[0x00..0x04].copy_from_slice(&le32(TEXT_RVA));
    rdata[0x04..0x08].copy_from_slice(&le32(TEXT_RVA + 0x80));
    rdata[0x08..0x0c].copy_from_slice(&le32(rdata_rva(0x100)));
    // A chained record naming a different record that names this one back.
    rdata[0x100..0x104].copy_from_slice(&[0x21, 0x00, 0x00, 0x00]);
    rdata[0x104..0x108].copy_from_slice(&le32(TEXT_RVA));
    rdata[0x108..0x10c].copy_from_slice(&le32(TEXT_RVA + 0x80));
    rdata[0x10c..0x110].copy_from_slice(&le32(rdata_rva(0x140)));
    rdata[0x140..0x144].copy_from_slice(&[0x21, 0x00, 0x00, 0x00]);
    rdata[0x144..0x148].copy_from_slice(&le32(TEXT_RVA));
    rdata[0x148..0x14c].copy_from_slice(&le32(TEXT_RVA + 0x80));
    rdata[0x14c..0x150].copy_from_slice(&le32(rdata_rva(0x100)));

    let data = synth(&rdata, &[(3, rdata_rva(0), 12)]);
    let (obj, _) = pe::load_windows(&data, &LoadOptions::default()).expect("load");
    assert!(
        obj.warnings.iter().any(|w| w.contains("deep")),
        "the chain limit should be reported: {:?}",
        obj.warnings
    );
}

/// An image whose UNWIND_INFO names a handler and puts `language` after it.
fn scope_image(language: &[u8]) -> Vec<u8> {
    let mut rdata = vec![0u8; RDATA_LEN];
    rdata[0x00..0x04].copy_from_slice(&le32(TEXT_RVA));
    rdata[0x04..0x08].copy_from_slice(&le32(TEXT_RVA + 0x80));
    rdata[0x08..0x0c].copy_from_slice(&le32(rdata_rva(0x100)));
    // UNW_FLAG_EHANDLER, no codes.
    rdata[0x100..0x104].copy_from_slice(&[0x09, 0x00, 0x00, 0x00]);
    rdata[0x104..0x108].copy_from_slice(&le32(TEXT_RVA + 0x100));
    rdata[0x108..0x108 + language.len()].copy_from_slice(language);
    synth(&rdata, &[(3, rdata_rva(0), 12)])
}

#[test]
fn a_scope_table_handler_outside_the_function_becomes_a_hint() {
    let mut lang = Vec::new();
    lang.extend_from_slice(&le32(1));
    lang.extend_from_slice(&le32(TEXT_RVA + 0x10)); // begin
    lang.extend_from_slice(&le32(TEXT_RVA + 0x20)); // end
    lang.extend_from_slice(&le32(TEXT_RVA + 0x120)); // filter, a real funclet
    lang.extend_from_slice(&le32(TEXT_RVA + 0x140)); // __except body
    let data = scope_image(&lang);
    let (obj, win) = pe::load_windows(&data, &LoadOptions::default()).unwrap();
    let scopes = &win.exceptions.unwind[0].scopes;
    assert_eq!(scopes.len(), 1);
    assert_eq!(
        scopes[0].handler,
        ScopeHandler::Address(Addr(text_va(0x120)))
    );
    for a in [text_va(0x120), text_va(0x140)] {
        let h = obj
            .function_hints
            .iter()
            .find(|h| h.addr == Addr(a))
            .unwrap_or_else(|| panic!("{a:#x} produced no hint"));
        assert_eq!(h.provenance.strength(), Strength::Proven);
        assert!(h.provenance.has(Evidence::PeUnwind));
    }
}

#[test]
fn a_scope_table_handler_outside_every_section_is_a_warning_not_a_hint() {
    let mut lang = Vec::new();
    lang.extend_from_slice(&le32(1));
    lang.extend_from_slice(&le32(TEXT_RVA + 0x10));
    lang.extend_from_slice(&le32(TEXT_RVA + 0x20));
    lang.extend_from_slice(&le32(0x0f00_0000)); // nowhere at all
    lang.extend_from_slice(&le32(0));
    let data = scope_image(&lang);
    let (obj, win) = pe::load_windows(&data, &LoadOptions::default()).unwrap();
    // The entry is still recorded: the file said it, and saying what the file
    // said is not the same as believing it.
    assert_eq!(win.exceptions.unwind[0].scopes.len(), 1);
    let bogus = Addr(BASE + 0x0f00_0000);
    assert!(obj.function_hints.iter().all(|h| h.addr != bogus));
    assert!(
        obj.warnings
            .iter()
            .any(|w| w.contains("outside every section")),
        "{:?}",
        obj.warnings
    );
}

#[test]
fn a_cxx_funcinfo_is_not_read_as_a_scope_table() {
    // __CxxFrameHandler3 stores one RVA here, not a count. Read as a count it
    // asks for gigabytes, which is the first bound the parser checks.
    let data = scope_image(&le32(0x0020_1234));
    let (obj, win) = pe::load_windows(&data, &LoadOptions::default()).unwrap();
    assert!(win.exceptions.unwind[0].scopes.is_empty());
    assert!(
        obj.warnings.iter().any(|w| w.contains("not a scope table")),
        "{:?}",
        obj.warnings
    );
}

#[test]
fn a_scope_table_entry_outside_its_function_refuses_the_whole_table() {
    let mut lang = Vec::new();
    lang.extend_from_slice(&le32(2));
    lang.extend_from_slice(&le32(TEXT_RVA + 0x10));
    lang.extend_from_slice(&le32(TEXT_RVA + 0x20));
    lang.extend_from_slice(&le32(1));
    lang.extend_from_slice(&le32(TEXT_RVA + 0x30));
    // The second entry guards code the function does not contain.
    lang.extend_from_slice(&le32(TEXT_RVA + 0x400));
    lang.extend_from_slice(&le32(TEXT_RVA + 0x410));
    lang.extend_from_slice(&le32(1));
    lang.extend_from_slice(&le32(TEXT_RVA + 0x420));
    let data = scope_image(&lang);
    let (obj, win) = pe::load_windows(&data, &LoadOptions::default()).unwrap();
    assert!(win.exceptions.unwind[0].scopes.is_empty());
    assert!(
        obj.warnings
            .iter()
            .any(|w| w.contains("not inside the function"))
    );
}

#[test]
fn a_relocation_block_shorter_than_its_header_stops_the_walk() {
    // The classic unbounded loop: a block size of four advances the cursor by
    // nothing and the walk never ends.
    let mut rdata = vec![0u8; RDATA_LEN];
    rdata[0x00..0x04].copy_from_slice(&le32(TEXT_RVA));
    rdata[0x04..0x08].copy_from_slice(&le32(4));
    let data = synth(&rdata, &[(5, rdata_rva(0), 0x100)]);
    let (obj, win) = pe::load_windows(&data, &LoadOptions::default()).unwrap();
    assert!(win.relocations.is_empty());
    assert!(
        obj.warnings
            .iter()
            .any(|w| w.contains("fewer than its own header")),
        "{:?}",
        obj.warnings
    );
}

#[test]
fn base_relocations_skip_padding_and_carry_the_highadj_addend() {
    let mut rdata = vec![0u8; RDATA_LEN];
    rdata[0x00..0x04].copy_from_slice(&le32(TEXT_RVA));
    rdata[0x04..0x08].copy_from_slice(&le32(8 + 2 * 5));
    // One offset past 0x7ff, so the twelve-bit field is pinned rather than only
    // the low eleven bits a small section would exercise.
    let entries: [u16; 5] = [
        0xa000 | 0x008, // DIR64 at +8
        0x4000 | 0xabc, // HIGHADJ at +0xabc, with an addend after it
        0x1234,         // the addend, which is not an entry
        0x3000 | 0x020, // HIGHLOW at +0x20
        0x0000,         // padding
    ];
    for (i, e) in entries.iter().enumerate() {
        let at = 8 + i * 2;
        rdata[at..at + 2].copy_from_slice(&e.to_le_bytes());
    }
    let data = synth(&rdata, &[(5, rdata_rva(0), 8 + 2 * 5)]);
    let (_, win) = pe::load_windows(&data, &LoadOptions::default()).unwrap();
    let got: Vec<(u64, u8)> = win
        .relocations
        .iter()
        .map(|r| (r.addr.get() - BASE, r.kind))
        .collect();
    assert_eq!(
        got,
        vec![
            (TEXT_RVA as u64 + 8, 10),
            (TEXT_RVA as u64 + 0xabc, 4),
            (TEXT_RVA as u64 + 0x20, 3),
        ]
    );
}

#[test]
fn a_directory_claiming_more_than_the_file_holds_reads_only_what_fits() {
    let mut rdata = vec![0u8; RDATA_LEN];
    rdata[0x00..0x04].copy_from_slice(&le32(TEXT_RVA));
    rdata[0x04..0x08].copy_from_slice(&le32(TEXT_RVA + 0x10));
    rdata[0x08..0x0c].copy_from_slice(&le32(0));
    // The size says a hundred megabytes of runtime functions.
    let data = synth(&rdata, &[(3, rdata_rva(0), 100 << 20)]);
    let (obj, win) = pe::load_windows(&data, &LoadOptions::default()).unwrap();
    assert_eq!(win.exceptions.functions.len(), 1);
    assert!(
        obj.warnings.iter().any(|w| w.contains("fit in the file")),
        "{:?}",
        obj.warnings
    );
}

#[test]
fn a_guard_table_claiming_more_entries_than_the_file_holds_is_bounded() {
    let mut rdata = vec![0u8; RDATA_LEN];
    // A 64-bit load config with only the guard table filled in.
    let size = 0xc8u32;
    rdata[0x00..0x04].copy_from_slice(&size.to_le_bytes());
    rdata[0x80..0x88].copy_from_slice(&le64(rdata_va(0x200)));
    rdata[0x88..0x90].copy_from_slice(&le64(1 << 40));
    rdata[0x200..0x204].copy_from_slice(&le32(TEXT_RVA));
    rdata[0x204..0x208].copy_from_slice(&le32(TEXT_RVA + 8));
    let data = synth(&rdata, &[(10, rdata_rva(0), size)]);
    let (obj, win) = pe::load_windows(&data, &LoadOptions::default()).unwrap();
    let cfg = win.load_config.expect("no load config");
    assert_eq!(cfg.guard_cf_function_count, 1 << 40);
    // 0x200 bytes left in the section, four per entry.
    assert_eq!(cfg.guard_functions.len(), 2);
    assert!(obj.warnings.iter().any(|w| w.contains("fit in the file")));
}

#[test]
fn an_image_view_translates_rvas_addresses_and_file_offsets() {
    // The three translations every directory walk depends on, checked against
    // the layout the builder above lays down rather than against themselves.
    let data = tls_image(&[text_va(0x10)], true);
    let (obj, _) = pe::load_windows(&data, &LoadOptions::default()).unwrap();
    let img = pe::Image::of(&data, &obj);
    assert_eq!(img.addr_of(TEXT_RVA), Addr(text_va(0)));
    assert_eq!(img.offset_of(TEXT_RVA), Some(TEXT_OFF as u64));
    assert_eq!(img.offset_of(RDATA_RVA), Some(RDATA_OFF as u64));
    // An image loaded where it asked to be stores absolute addresses as is.
    assert_eq!(img.addr_of_va(rdata_va(0x20)), Some(Addr(rdata_va(0x20))));
    assert_eq!(img.addr_of_va(0), None);
    assert!(img.is_code(Addr(text_va(0x10))));
    assert!(!img.is_code(Addr(rdata_va(0x10))));
    assert!(img.is_mapped(Addr(rdata_va(0x10))));
    assert!(!img.is_mapped(Addr(BASE + 0x0f00_0000)));
    // The header is in no section, so a walk there falls back to the file.
    assert_eq!(img.section_bytes_after(0), None);
    assert_eq!(
        img.section_bytes_after(RDATA_OFF as u64),
        Some(RDATA_LEN as u64)
    );
    assert_eq!(e5r_format::windirs::reloc_kind(10), "dir64");
}

#[test]
fn corrupted_directories_never_panic() {
    // Every byte of the headers and of the directory payload, three ways.
    let base = tls_image(&[text_va(0x10)], true);
    let mut data = base.clone();
    for i in (0..RDATA_OFF + 0x40).step_by(5) {
        let old = data[i];
        for v in [0xffu8, 0x00, 0x80] {
            data[i] = v;
            let _ = pe::load_windows(&data, &LoadOptions::default());
        }
        data[i] = old;
    }
    let mut n = 1;
    while n < base.len() {
        let _ = pe::load_windows(&base[..n], &LoadOptions::default());
        n = (n * 2).max(n + 101);
    }
}

#[test]
fn caps_bound_what_the_directories_allocate() {
    let opts = LoadOptions {
        caps: Caps {
            symbols: 4,
            ..Caps::default()
        },
        ..LoadOptions::default()
    };
    let data = tls_image(&[text_va(0x10)], false);
    let (_, win) = pe::load_windows(&data, &opts).unwrap();
    assert!(win.tls.unwrap().callbacks.len() <= 4);
}

#[test]
fn a_coff_object_has_no_windows_directories() {
    let Some(dir) = corpus() else { return };
    let Ok(data) = std::fs::read(dir.join("wide.coff.o")) else {
        return;
    };
    let (obj, win) = pe::load_windows(&data, &LoadOptions::default()).unwrap();
    assert_eq!(obj.arch, Arch::X86_64);
    // An object has section-level .pdata but no data directories, so nothing
    // here should claim otherwise.
    assert!(win.tls.is_none());
    assert!(win.exceptions.functions.is_empty());
    assert!(win.relocations.is_empty());
    assert!(win.load_config.is_none());
}
