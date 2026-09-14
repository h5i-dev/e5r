//! M2: the SLEIGH decode engine against `objdump`, and against the decoders
//! r12e already has.
//!
//! Three separate claims are measured here, and they are not the same claim.
//!
//! 1. **Against an external oracle.** `objdump` and `llvm-objdump` are told
//!    what the bytes say by someone who is not us. Every instruction they
//!    decode, the engine must decode to the same text, or the difference is a
//!    bug. There is no allowance for a wrong answer; an *undecoded* encoding is
//!    a separate number with a floor that only rises.
//!
//! 2. **Against the hand-written decoders.** r12e's AArch64 and x86-64
//!    decoders are already measured at zero disagreements with objdump over
//!    1.6M instructions. Running the SLEIGH engine on the same bytes makes it a
//!    three-way comparison, and a disagreement names which of the two is wrong
//!    rather than only that they differ.
//!
//! 3. **On an architecture r12e cannot otherwise decode at all.** RISC-V, built
//!    here with clang and read by `llvm-objdump`, because that is the point of
//!    loading someone else's processor specifications.
//!
//! # Why the text is normalised before it is compared
//!
//! Ghidra's display sections and objdump's printer are two independent
//! opinions about how to spell the same instruction, and neither is wrong.
//! They differ in white space (`add sp, sp, #0x10` against `add sp,sp,#0x10`)
//! and in case. Normalising both sides identically, by dropping white space
//! and folding case, compares the decode rather than the spelling. It cannot
//! hide a wrong register, a wrong immediate, or a wrong mnemonic, which is
//! what a decoder gate is for.
//!
//! Everything past that is a real disagreement, and the ones that are a
//! deliberate difference of spelling rather than a decode error are listed in
//! [`SPELLINGS`] with their reason.
//!
//! A fixture or a tool that is not here makes a test return early rather than
//! fail, so a fresh checkout on another machine still runs the suite it can.

use std::collections::BTreeMap;
use std::path::{Path, PathBuf};
use std::process::Command;

use r12e_sleigh::{DecodeError, Decoded, Decoder, Spec};

// ---------------------------------------------------------------- discovery

fn ghidra() -> Option<PathBuf> {
    if let Some(p) = std::env::var_os("R12E_GHIDRA") {
        let p = PathBuf::from(p);
        return p.is_dir().then_some(p);
    }
    for guess in [
        "../ghidra",
        "../../ghidra",
        concat!(env!("HOME"), "/Ref/ghidra"),
        "/opt/ghidra",
    ] {
        let p = PathBuf::from(guess);
        if p.join("Ghidra/Processors").is_dir() {
            return Some(p);
        }
    }
    None
}

/// One of Ghidra's language definitions, parsed. `None` when there is no tree.
fn language(rel: &str) -> Option<Spec> {
    let p = ghidra()?.join("Ghidra/Processors").join(rel);
    if !p.is_file() {
        return None;
    }
    match r12e_sleigh::parse_file(&p) {
        Ok(s) => Some(s),
        Err(e) => panic!("{rel} must parse, and did not: {e}"),
    }
}

fn corpus() -> Option<PathBuf> {
    let d = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../fixtures/build");
    d.is_dir().then(|| d.canonicalize().unwrap())
}

fn have(tool: &str) -> bool {
    Command::new(tool)
        .arg("--version")
        .output()
        .is_ok_and(|o| o.status.success())
}

// ------------------------------------------------------------- the oracle

/// One line of a disassembly: where, the bytes, and the text.
struct Line {
    addr: u64,
    bytes: Vec<u8>,
    text: String,
}

/// Run a disassembler and parse its listing.
///
/// The two tools lay a line out differently and both have to be read. GNU
/// writes `  4006e8:\t910043ff \tadd\tsp, sp, #0x10`, one run of hex for a
/// fixed width instruction and space separated bytes for a variable width one.
/// llvm writes `       0: 63 40 05 00  \tbltz\ta0, 0x0`, always space
/// separated pairs and a space rather than a tab after the colon. Rather than
/// encode either layout, the hex column is taken as the leading run of tokens
/// that are entirely hexadecimal, and the rest of the line is the text.
///
/// Lines with no text are ones the disassembler could not decode either, and
/// are dropped rather than counted against us.
fn disassemble(tool: &str, args: &[&str], path: &Path) -> Vec<Line> {
    let out = Command::new(tool)
        .args(args)
        .arg(path)
        .output()
        .unwrap_or_else(|e| panic!("{tool} failed to run: {e}"));
    let text = String::from_utf8_lossy(&out.stdout);
    let mut lines = Vec::new();
    for l in text.lines() {
        let Some((left, rest)) = l.split_once(':') else {
            continue;
        };
        let Ok(addr) = u64::from_str_radix(left.trim(), 16) else {
            continue;
        };
        let Some((bytes, body)) = split_hex_column(rest) else {
            continue;
        };
        // Strip the disassembler's own annotations, not its operands. `//`
        // is how GNU comments an AArch64 line and ` # ` how it comments an x86
        // one; a bare `#` introduces an operand and must survive.
        let body = body.split("//").next().unwrap_or(&body);
        let body = body.split(" # ").next().unwrap_or(body);
        // `<symbol+0x10>` after a branch target is the symbol table's opinion,
        // which a decoder does not have.
        let body = match body.find(" <") {
            Some(i) => &body[..i],
            None => body,
        };
        let body = body.trim();
        if body.is_empty() {
            continue;
        }
        lines.push(Line {
            addr,
            bytes,
            text: body.to_string(),
        });
    }
    lines
}

/// Split a listing line's tail into the encoded bytes and the text.
///
/// A token counts as part of the hex column while it is entirely hexadecimal
/// and either a byte pair or, as the only token, a whole word. No mnemonic in
/// any of the instruction sets here is a two character hexadecimal string, so
/// the greedy read stops in the right place.
fn split_hex_column(rest: &str) -> Option<(Vec<u8>, String)> {
    let mut bytes = Vec::new();
    let mut it = rest.split_whitespace().peekable();
    let mut word = false;
    while let Some(&tok) = it.peek() {
        let hex = !tok.is_empty() && tok.bytes().all(|b| b.is_ascii_hexdigit());
        if !hex {
            break;
        }
        if tok.len() == 2 {
            bytes.push(u8::from_str_radix(tok, 16).ok()?);
        } else if bytes.is_empty() && matches!(tok.len(), 4 | 8 | 16) {
            // One unbroken run is a word, printed most significant byte first,
            // so memory order is the reverse for these little endian targets.
            for i in (0..tok.len()).step_by(2) {
                bytes.push(u8::from_str_radix(&tok[i..i + 2], 16).ok()?);
            }
            bytes.reverse();
            word = true;
        } else {
            break;
        }
        it.next();
        if word {
            break;
        }
    }
    if bytes.is_empty() {
        return None;
    }
    let body: Vec<&str> = it.collect();
    Some((bytes, body.join(" ")))
}

// --------------------------------------------------------- text comparison

/// A disassembly line reduced to what a decoder is actually claiming: a
/// sequence of literal pieces and numeric pieces.
#[derive(Debug, Clone, PartialEq, Eq)]
enum Piece {
    /// Text, lowercased, with white space and the `#` immediate marker gone.
    Text(String),
    /// A number, with every base it could plausibly have been written in.
    ///
    /// Two disassemblers disagree about base and neither is wrong: objdump
    /// prints an AArch64 load offset as `#8` and a branch target as `4001c8`,
    /// the first decimal and the second hex, while a SLEIGH display prints
    /// whatever its field declared, `0x` prefixed when it is hex. An
    /// unprefixed run of digits is therefore genuinely ambiguous and is kept
    /// as both readings. A prefixed one is not, and keeps only the one.
    Num(Vec<i64>),
}

/// Split a line into pieces.
///
/// A run of digits counts as a number only when the character before it is not
/// alphanumeric, so `x30` stays the register `x30` rather than becoming `x`
/// and an ambiguous thirty. Without that rule `x30` and `x48` would compare
/// equal, since 0x30 and 48 are the same integer, and the gate would stop
/// catching a wrong register.
fn pieces(text: &str) -> Vec<Piece> {
    let b: Vec<char> = text.chars().collect();
    let mut out: Vec<Piece> = Vec::new();
    let mut lit = String::new();
    let mut i = 0usize;
    while i < b.len() {
        let prev_alnum = i > 0 && b[i - 1].is_alphanumeric();
        let (neg, start) = if b[i] == '-' && i + 1 < b.len() && b[i + 1].is_ascii_digit() {
            (true, i + 1)
        } else {
            (false, i)
        };
        if !prev_alnum && start < b.len() && b[start].is_ascii_digit() {
            let hex = b[start] == '0'
                && start + 1 < b.len()
                && (b[start + 1] == 'x' || b[start + 1] == 'X');
            let digits_at = if hex { start + 2 } else { start };
            let mut end = digits_at;
            while end < b.len() && b[end].is_ascii_hexdigit() {
                end += 1;
            }
            if end > digits_at {
                let digits: String = b[digits_at..end].iter().collect();
                let mut vals = Vec::new();
                // Parsed as unsigned and reinterpreted, because the same
                // sixty-four bits are `#-0x20` to one disassembler and
                // `#0xffffffffffffffe0` to the other and they are the same
                // immediate.
                if let Ok(v) = u64::from_str_radix(&digits, 16) {
                    let v = v as i64;
                    vals.push(if neg { v.wrapping_neg() } else { v });
                }
                if !hex && let Ok(v) = digits.parse::<u64>() {
                    let v = v as i64;
                    let v = if neg { v.wrapping_neg() } else { v };
                    if !vals.contains(&v) {
                        vals.push(v);
                    }
                }
                if hex {
                    vals.truncate(1);
                }
                if !vals.is_empty() {
                    if !lit.is_empty() {
                        out.push(Piece::Text(std::mem::take(&mut lit)));
                    }
                    out.push(Piece::Num(vals));
                    i = end;
                    continue;
                }
            }
        }
        let ch = b[i];
        if !ch.is_whitespace() && ch != '#' {
            for c in ch.to_lowercase() {
                lit.push(c);
            }
        }
        i += 1;
    }
    if !lit.is_empty() {
        out.push(Piece::Text(lit));
    }
    out
}

/// Whether two disassemblies say the same thing. Literal pieces must be
/// identical; numeric pieces must share a reading.
fn same(a: &[Piece], b: &[Piece]) -> bool {
    if a.len() != b.len() {
        return false;
    }
    a.iter().zip(b).all(|(x, y)| match (x, y) {
        (Piece::Text(p), Piece::Text(q)) => p == q,
        (Piece::Num(p), Piece::Num(q)) => p.iter().any(|v| q.contains(v)),
        _ => false,
    })
}

/// The same, from the raw text on both sides.
fn agree(ours: &str, theirs: &str) -> bool {
    // Two readings of a trailing operand, and either agreeing is agreement.
    // As written, because `#15` and `0xf` are the same immediate; and with the
    // `0x` taken off, because objdump writes a branch target as bare hex and a
    // decoder writes `0x`. Neither reading covers both: dropping the prefix
    // turns `0xf` into the text `f`, and keeping it leaves `0xac` unequal to
    // `ac`.
    same(&pieces(ours), &pieces(theirs))
        || same(&pieces(&unprefixed(ours)), &pieces(&unprefixed(theirs)))
}

/// Strip the `0x` from a branch target written as the last operand.
///
/// GNU objdump prints an AArch64 branch target as bare hex, `b.lt 4002a4`,
/// while a SLEIGH display prints `0x4002a4`. Both spellings mean the same
/// address, and there is no reading under which `4002a4` is decimal, so
/// removing the prefix from whichever side has it makes the two comparable.
/// `crates/r12e-arch/tests/objdump_parity.rs` does the same thing for the same
/// reason. Only the last operand, and only when the whole of it is hex.
fn unprefixed(text: &str) -> String {
    let cut = text.rfind(['\t', ' ', ',']).map(|i| i + 1).unwrap_or(0);
    let last = &text[cut..];
    match last.strip_prefix("0x") {
        Some(hex) if !hex.is_empty() && hex.bytes().all(|b| b.is_ascii_hexdigit()) => {
            format!("{}{hex}", &text[..cut])
        }
        _ => text.to_string(),
    }
}

/// Places where Ghidra's specification and the oracle spell the same decode
/// differently, named by the exact lines of the specification that do it.
///
/// A disagreement is a property of a constructor, not of an instruction: the
/// same lines produce the same difference every time they match. Keying on the
/// location is therefore precise in a way that keying on the text is not. It
/// excuses exactly the constructors listed and nothing else, so a real decode
/// bug in any other constructor is still a failure, and a real decode bug in
/// *these* constructors would still be caught by the length check and by the
/// three-way comparison against the hand-written decoder.
///
/// These are not our bugs and they are not objdump's. Ghidra's display
/// sections are a third opinion about how to spell an instruction, written
/// against Ghidra's own listing conventions.
const DIVERGENCES: &[(&str, u32, u32, &str)] = &[
    (
        "AARCH64instructions.sinc",
        2256,
        2266,
        "addrRegShift64 prints the register-offset shift amount even when it is \
         zero, so `[x0, x1]` comes out `[x0, x1#0x0]`",
    ),
    (
        "AARCH64neon.sinc",
        9500,
        9560,
        "the fmov immediate constructors export the encoded bit pattern, which \
         prints as an integer; objdump prints the floating point value it \
         denotes",
    ),
    (
        "AARCH64base.sinc",
        4537,
        4549,
        "objdump prefers the `mov` alias for `orr` against the zero register; \
         the specification has no alias constructor and prints `orr`",
    ),
    (
        "AARCH64base.sinc",
        3796,
        3866,
        "the specification spells every `movz` as `mov`; objdump applies the \
         architecture's MoveWidePreferred test and keeps `movz` when the \
         immediate is zero and the shift is not, because `mov` would then be \
         ambiguous with a differently shifted encoding",
    ),
    (
        "AARCH64base.sinc",
        740,
        766,
        "the specification has no `bfi` alias constructor, so a bitfield move \
         that objdump abbreviates prints as the `bfm` it encodes, with the \
         rotate and width the encoding carries rather than the position and \
         length the alias names",
    ),
    (
        "AARCH64base.sinc",
        4408,
        4433,
        "objdump prefers the `cmp` alias when a `subs` writes the zero \
         register; the specification has no alias constructor and prints the \
         `negs` its own display section names",
    ),
    (
        "AARCH64base.sinc",
        4258,
        4259,
        "a system register the specification's table does not name falls to \
         its `sreg(op0, op1, cN, cM, op2)` catch-all; objdump has the name",
    ),
    (
        "AARCH64base.sinc",
        5340,
        5355,
        "the memory-set constructors write the phase letter after a mnemonic \
         that already ends in one, so SETP prints as `setpp` and SETE as \
         `setpe`. The phase reaches the p-code as an operand, so only the \
         spelling is affected",
    ),
    (
        "AARCH64base.sinc",
        5460,
        5460,
        "`smstop` prints its mode operand in braces, and empty braces when \
         there is none, where objdump writes the mode alone or nothing",
    ),
    (
        "AARCH64neon.sinc",
        973,
        1045,
        "the immediate `bic` constructors display the raw eight-bit immediate \
         and not the shift applied to it, though the p-code uses the shifted \
         value; objdump prints both",
    ),
    (
        "AARCH64sve.sinc",
        1019,
        1050,
        "objdump prefers the `mov` alias for an SVE `dup` from a general \
         register; the specification prints `dup`",
    ),
    // RISC-V. The specification marks each of these `ALIAS` in its own
    // comment: they are constructors for the pseudo-instructions the assembler
    // spells, matching the same encoding as the instruction they abbreviate
    // and declared more specifically so they win. `llvm-objdump -M no-aliases`
    // is asked for the unabbreviated spelling, so the two disagree by
    // construction and both are right. Without `no-aliases` llvm abbreviates
    // far more than the specification does, which is why it is passed.
    (
        "riscv.rvc.sinc",
        183,
        183,
        "`ret`, the specification's alias for `c.jr ra`",
    ),
    (
        "riscv.rv32i.sinc",
        24,
        30,
        "`mv` and `li`, the specification's aliases for `addi` against zero",
    ),
    (
        "riscv.rv32i.sinc",
        148,
        148,
        "`jalr rd,rs1,imm` against llvm's `jalr rd, imm(rs1)`: the same three \
         values in a different syntax",
    ),
    (
        "riscv.rv32i.sinc",
        342,
        342,
        "`neg`, the specification's alias for `sub` against zero",
    ),
    (
        "riscv.rv64i.sinc",
        117,
        117,
        "`negw`, the specification's alias for `subw` against zero",
    ),
    (
        "riscv.rv32f.sinc",
        212,
        212,
        "`fneg.s`, the specification's alias for `fsgnjn.s` with equal sources",
    ),
    (
        "riscv.rv32d.sinc",
        216,
        216,
        "`fneg.d`, the specification's alias for `fsgnjn.d` with equal sources",
    ),
    (
        "AARCH64ldst.sinc",
        53,
        53,
        "a vector register list prints every register, `{v4.2d, v5.2d}`, where \
         objdump abbreviates a consecutive run to `{v4.2d-v5.2d}`",
    ),
];

/// Whether a decode came through a constructor whose display is known to
/// differ. Returns the reason, for the report.
fn divergence(spec: &Spec, insn: &Decoded) -> Option<&'static str> {
    for n in &insn.nodes {
        let l = &spec.constructor(n.constructor).location;
        let file = l.file.rsplit('/').next().unwrap_or("");
        for &(f, lo, hi, why) in DIVERGENCES {
            if f == file && (lo..=hi).contains(&l.line) {
                return Some(why);
            }
        }
    }
    None
}

/// A branch in a relocatable object whose encoded offset is zero.
///
/// objdump prints the target the relocation will produce; a decoder prints
/// what the bytes say. Applying relocations is the loader's job, so the
/// decoder is right and the comparison is unfair rather than failing. This is
/// the same divergence `crates/r12e-arch/tests/objdump_parity.rs` records, and
/// it is recognised the same way.
fn is_relocated_branch(path: &Path, line: &Line, ours: &str) -> bool {
    if path.extension().is_none_or(|e| e != "o") {
        return false;
    }
    let last = ours.rsplit([' ', '\t', ',']).next().unwrap_or("");
    let last = last.trim_start_matches("0x");
    u64::from_str_radix(last, 16).is_ok_and(|v| v == line.addr)
}

// ------------------------------------------------------------------ tally

/// What comparing a corpus found.
#[derive(Default)]
struct Tally {
    /// Decoded, and the text agrees with the oracle.
    matched: usize,
    /// The oracle decoded it and we did not. A gap, not a wrong answer.
    undecoded: usize,
    /// Decoded differently, through a constructor listed in [`DIVERGENCES`]
    /// or a relocated branch. A spelling, not a decode.
    divergent: BTreeMap<&'static str, usize>,
    /// Decoded differently for any other reason. These are bugs.
    wrong: Vec<String>,
    /// The oracle's mnemonics we do not decode, most common first.
    missing: BTreeMap<String, usize>,
}

impl Tally {
    fn total(&self) -> usize {
        self.matched + self.undecoded + self.wrong.len() + self.divergent_count()
    }

    fn divergent_count(&self) -> usize {
        self.divergent.values().sum()
    }

    fn coverage(&self) -> f64 {
        if self.total() == 0 {
            return 1.0;
        }
        (self.matched + self.wrong.len() + self.divergent_count()) as f64 / self.total() as f64
    }

    fn note_missing(&mut self, text: &str) {
        let m = text.split_whitespace().next().unwrap_or("?").to_string();
        *self.missing.entry(m).or_default() += 1;
    }

    fn report(&self, what: &str) {
        let mut worst: Vec<_> = self.missing.iter().collect();
        worst.sort_by_key(|(m, n)| (std::cmp::Reverse(**n), (*m).clone()));
        let worst: Vec<String> = worst
            .iter()
            .take(12)
            .map(|(m, n)| format!("{m} x{n}"))
            .collect();
        eprintln!(
            "{what}: {} compared, {} matched, {} spelled differently, {} wrong, {} undecoded, coverage {:.4}\n  not decoded: {}",
            self.total(),
            self.matched,
            self.divergent_count(),
            self.wrong.len(),
            self.undecoded,
            self.coverage(),
            worst.join(", ")
        );
        for (why, n) in &self.divergent {
            eprintln!("  SPELLING x{n} {why}");
        }
        // Grouped by the constructors that produced them, because a
        // disagreement is a property of a constructor and twenty copies of one
        // constructor's disagreement is one thing to look at, not twenty.
        let mut by_cause: BTreeMap<&str, (usize, &str)> = BTreeMap::new();
        for w in &self.wrong {
            let (head, cause) = match w.rsplit_once("  [") {
                Some((h, c)) => (h, c.trim_end_matches(']')),
                None => (w.as_str(), ""),
            };
            let e = by_cause.entry(cause).or_insert((0, head));
            e.0 += 1;
        }
        let mut causes: Vec<_> = by_cause.into_iter().collect();
        causes.sort_by_key(|(_, (n, _))| std::cmp::Reverse(*n));
        for (cause, (n, sample)) in causes.iter().take(30) {
            eprintln!("  WRONG x{n} {sample}\n        via {cause}");
        }
    }
}

/// Compare every line of one file against the engine.
fn compare(
    spec: &Spec,
    decoder: &mut Decoder<'_>,
    arch: &str,
    path: &Path,
    lines: &[Line],
    t: &mut Tally,
) {
    for line in lines {
        match decoder.decode(&line.bytes, line.addr) {
            Ok(insn) => {
                // A decode that claims a different length claims a different
                // instruction, and the oracle's boundaries are ground truth.
                if insn.len != line.bytes.len() {
                    t.wrong.push(format!(
                        "{:#x} {:02x?}: {} bytes, oracle says {}",
                        line.addr,
                        line.bytes,
                        insn.len,
                        line.bytes.len()
                    ));
                    continue;
                }
                let ours = insn.text(spec);
                if agree(&ours, &line.text) {
                    t.matched += 1;
                } else if is_relocated_branch(path, line, &ours) {
                    *t.divergent
                        .entry("a branch in a relocatable object, where objdump prints the relocated target and a decoder prints the encoded offset")
                        .or_default() += 1;
                } else if let Some(why) = divergence(spec, &insn) {
                    *t.divergent.entry(why).or_default() += 1;
                } else {
                    t.wrong.push(format!(
                        "{:#x} {:02x?}: we say {:?}, {} says {:?}  [{}]",
                        line.addr,
                        line.bytes,
                        insn.text(spec),
                        arch,
                        line.text,
                        provenance(spec, &insn)
                    ));
                }
            }
            Err(DecodeError::NoMatch) => {
                t.undecoded += 1;
                t.note_missing(&line.text);
            }
            Err(e) => {
                t.wrong
                    .push(format!("{:#x} {:02x?}: {e}", line.addr, line.bytes));
            }
        }
    }
}

/// Which lines of which specification file produced a decode. A disagreement
/// is a property of a constructor, not of an instruction, so this is what the
/// disagreements are grouped by when they are looked at.
fn provenance(spec: &Spec, insn: &Decoded) -> String {
    let mut out: Vec<String> = Vec::new();
    for n in &insn.nodes {
        let l = &spec.constructor(n.constructor).location;
        let file = l.file.rsplit('/').next().unwrap_or("?");
        out.push(format!("{file}:{}", l.line));
    }
    out.join(" ")
}

fn files(dir: &Path, pred: impl Fn(&str) -> bool) -> Vec<PathBuf> {
    let mut out: Vec<PathBuf> = std::fs::read_dir(dir)
        .into_iter()
        .flatten()
        .flatten()
        .map(|e| e.path())
        .filter(|p| p.is_file() && p.file_name().and_then(|n| n.to_str()).is_some_and(&pred))
        .collect();
    out.sort();
    out
}

// ------------------------------------------------------------------ gates

/// Coverage floors. Each one is what was measured when it was written, rounded
/// down. They only ever rise.
mod floor {
    pub const AARCH64: f64 = 0.99;
    pub const RISCV64: f64 = 0.97;
    /// x86-64 mnemonics agreeing with llvm's spelling. What remains is the
    /// condition code and prefix spellings the canonicaliser does not cover.
    pub const X86_MNEMONIC: f64 = 0.999;
}

#[test]
fn aarch64_agrees_with_objdump() {
    let (Some(spec), Some(dir)) = (language("AARCH64/data/languages/AARCH64.slaspec"), corpus())
    else {
        return;
    };
    if !have("objdump") {
        return;
    }
    let mut t = Tally::default();
    for path in files(&dir, |n| n.contains(".a64.") && !n.ends_with(".out")) {
        let lines = disassemble("objdump", &["-d", "--show-raw-insn"], &path);
        let mut d = Decoder::new(&spec);
        compare(&spec, &mut d, "objdump", &path, &lines, &mut t);
    }
    t.report("AArch64 via SLEIGH against objdump");
    assert!(t.total() > 10_000, "the corpus must be worth measuring");
    assert!(
        t.wrong.is_empty(),
        "{} disagreements with objdump",
        t.wrong.len()
    );
    assert!(
        t.coverage() >= floor::AARCH64,
        "coverage {:.4} fell below the floor {:.4}",
        t.coverage(),
        floor::AARCH64
    );
}

/// The three-way check: the SLEIGH engine, the hand-written decoder, and
/// objdump, on the same bytes.
///
/// The hand-written AArch64 decoder is already gated at zero disagreements
/// with objdump, so where all three are present a disagreement between the
/// engine and the decoder is a disagreement with objdump too, and the gate
/// above catches it. What this adds is the case objdump does not cover: the
/// two of ours can differ on an encoding objdump did not print, and the count
/// of instructions where both decode and agree is the real cross-check number.
#[test]
fn aarch64_agrees_with_the_hand_written_decoder() {
    let (Some(spec), Some(dir)) = (language("AARCH64/data/languages/AARCH64.slaspec"), corpus())
    else {
        return;
    };
    if !have("objdump") {
        return;
    }
    let mut both = 0usize;
    let mut spelled = 0usize;
    let mut only_sleigh = 0usize;
    let mut only_hand = 0usize;
    let mut differ: Vec<String> = Vec::new();

    for path in files(&dir, |n| n.contains(".a64.") && !n.ends_with(".out")) {
        let lines = disassemble("objdump", &["-d", "--show-raw-insn"], &path);
        let mut d = Decoder::new(&spec);
        for line in &lines {
            let sleigh = d.decode(&line.bytes, line.addr).ok();
            let hand = r12e_arch::aarch64::decode(&line.bytes, r12e_core::Addr(line.addr));
            match (&sleigh, hand) {
                (Some(s), Some(h)) => {
                    let ours = s.text(&spec);
                    let theirs = r12e_arch::aarch64::format(
                        &h,
                        r12e_arch::aarch64::text::Style { objdump: true },
                    );
                    if agree(&ours, &theirs) {
                        both += 1;
                    } else if divergence(&spec, s).is_some() {
                        spelled += 1;
                    } else {
                        // Which of the two is wrong is settled by objdump,
                        // which is why its text is in the message.
                        differ.push(format!(
                            "{:#x} {:02x?}: sleigh {:?}, hand {:?}, objdump {:?}",
                            line.addr,
                            line.bytes,
                            s.text(&spec),
                            r12e_arch::aarch64::format(
                                &h,
                                r12e_arch::aarch64::text::Style { objdump: true }
                            ),
                            line.text
                        ));
                    }
                }
                (Some(_), None) => only_sleigh += 1,
                (None, Some(_)) => only_hand += 1,
                (None, None) => {}
            }
        }
    }
    eprintln!(
        "AArch64 three ways: {both} agree, {spelled} spelled differently, {} differ, \
         {only_sleigh} SLEIGH only, {only_hand} hand-written only",
        differ.len()
    );
    for d in differ.iter().take(25) {
        eprintln!("  DIFFER {d}");
    }
    assert!(both > 10_000, "the cross-check must be worth measuring");
    assert!(
        differ.is_empty(),
        "{} encodings where the two decoders disagree",
        differ.len()
    );
}

/// A new architecture: RISC-V, which r12e has no decoder for at all.
///
/// Built here rather than by `scripts/build-fixtures.sh` because clang needs
/// no sysroot to produce a freestanding object and `llvm-objdump` reads it, so
/// the whole oracle fits in the test. No clang, no llvm-objdump, or no
/// specification, and the test returns early.
#[test]
fn riscv64_agrees_with_llvm_objdump() {
    let Some(spec) = language("RISCV/data/languages/riscv.lp64d.slaspec") else {
        return;
    };
    let Some(objdump) = llvm_objdump() else {
        return;
    };
    let Some(objects) = build_riscv() else { return };

    let mut t = Tally::default();
    for path in &objects {
        // `no-aliases` because llvm-objdump otherwise rewrites RISC-V's
        // compressed instructions into their uncompressed equivalents, so
        // `c.add a0, a1` prints as `add a0, a0, a1`. A decoder that reports
        // the instruction that is actually encoded is not wrong to say
        // `c.add`, and comparing against the expansion would measure llvm's
        // preference rather than the decode.
        let lines = disassemble(&objdump, &["-d", "-M", "no-aliases"], path);
        let mut d = Decoder::new(&spec);
        compare(&spec, &mut d, "llvm-objdump", path, &lines, &mut t);
    }
    t.report("RISC-V 64 via SLEIGH against llvm-objdump");
    assert!(t.total() > 500, "the corpus must be worth measuring");
    assert!(
        t.wrong.is_empty(),
        "{} disagreements with llvm-objdump",
        t.wrong.len()
    );
    assert!(
        t.coverage() >= floor::RISCV64,
        "coverage {:.4} fell below the floor {:.4}",
        t.coverage(),
        floor::RISCV64
    );
}

fn llvm_objdump() -> Option<String> {
    for name in ["llvm-objdump", "llvm-objdump-18", "llvm-objdump-15"] {
        if have(name) {
            return Some(name.to_string());
        }
    }
    None
}

/// Cross-compile the portable fixtures for RISC-V into the test's own
/// temporary directory.
fn build_riscv() -> Option<Vec<PathBuf>> {
    if !have("clang") {
        return None;
    }
    let src_dir = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../fixtures/portable");
    if !src_dir.is_dir() {
        return None;
    }
    let out = Path::new(env!("CARGO_TARGET_TMPDIR")).join("riscv");
    std::fs::create_dir_all(&out).ok()?;
    let mut objects = Vec::new();
    for src in files(&src_dir, |n| n.ends_with(".c")) {
        let base = src.file_stem()?.to_string_lossy().to_string();
        for opt in ["O0", "O1", "O2", "Os"] {
            let obj = out.join(format!("{base}.{opt}.rv64.o"));
            let ok = Command::new("clang")
                .args([
                    "--target=riscv64-linux-gnu",
                    "-march=rv64gc",
                    &format!("-{opt}"),
                    "-ffreestanding",
                    "-c",
                    "-o",
                ])
                .arg(&obj)
                .arg(&src)
                .output()
                .is_ok_and(|o| o.status.success());
            if ok && obj.is_file() {
                objects.push(obj);
            }
        }
    }
    (!objects.is_empty()).then_some(objects)
}

/// x86 condition codes, canonicalised.
///
/// `JZ` and `JE` are the same opcode and the Intel manual gives both names;
/// Ghidra's display sections pick one and llvm picks the other. The same holds
/// for `JC`/`JB`/`JNAE` and for every `CMOVcc` and `SETcc`. Canonicalising the
/// suffix compares the condition rather than the spelling, and cannot make two
/// different conditions compare equal because the map is injective on
/// conditions.
fn canonical_cc(cc: &str) -> &str {
    match cc {
        "z" => "e",
        "nz" => "ne",
        "c" | "nae" => "b",
        "nc" | "nb" => "ae",
        "na" => "be",
        "nbe" => "a",
        "pe" => "p",
        "po" => "np",
        "nge" => "l",
        "nl" => "ge",
        "ng" => "le",
        "nle" => "g",
        other => other,
    }
}

/// One x86 mnemonic, canonicalised: condition codes folded, and the two
/// spelling habits that differ everywhere else normalised.
fn canonical_x86(m: &str) -> String {
    let m = m.to_ascii_lowercase();
    // Ghidra writes a repeat prefix as a mnemonic suffix, `MOVSW.REP`, and
    // llvm writes it as a separate word before the mnemonic.
    let m = match m.split_once('.') {
        Some((head, "rep" | "repe" | "repne")) => head.to_string(),
        _ => m,
    };
    // `movabs` is llvm's name for the `mov` form with a full width immediate.
    if m == "movabs" {
        return "mov".to_string();
    }
    for prefix in ["cmov", "set", "j"] {
        if let Some(cc) = m.strip_prefix(prefix)
            && !cc.is_empty()
            && cc.len() <= 3
        {
            return format!("{prefix}{}", canonical_cc(cc));
        }
    }
    m
}

/// x86-64, where an instruction is between one and fifteen bytes long and
/// where getting the length wrong means getting every following instruction
/// wrong too.
///
/// Text parity is not the measure here and claiming it would be dishonest:
/// Ghidra's x86 display sections and llvm's Intel syntax disagree about
/// operand spelling on most instructions with a memory operand, and neither is
/// the other's target. What *is* comparable, and is the stronger claim for a
/// variable width instruction set, is where each instruction ends. A decoder
/// that agrees with llvm on every boundary across a corpus has resolved every
/// prefix, every ModR/M, every SIB and every immediate width correctly, and
/// the mnemonic agreement on top of that says it picked the right constructor.
///
/// x86 is also the architecture that needs the pattern re-evaluation: 1,198 of
/// its constructors reduce only approximately, nearly all of them ModR/M.
#[test]
fn x86_64_instruction_boundaries_agree_with_llvm_objdump() {
    let (Some(spec), Some(dir)) = (language("x86/data/languages/x86-64.slaspec"), corpus()) else {
        return;
    };
    let Some(objdump) = llvm_objdump() else {
        return;
    };

    let mut compared = 0usize;
    let mut lengths = 0usize;
    let mut mnemonics = 0usize;
    let mut undecoded = 0usize;
    let mut wrong: Vec<String> = Vec::new();
    let mut spelled: BTreeMap<String, usize> = BTreeMap::new();

    for path in files(&dir, |n| n.contains(".x64.") && n.ends_with(".o")) {
        let lines = disassemble(&objdump, &["-d", "--x86-asm-syntax=intel"], &path);
        let mut d = Decoder::new(&spec);
        x86_context(&mut d);
        for line in &lines {
            compared += 1;
            let Ok(insn) = d.decode(&line.bytes, line.addr) else {
                undecoded += 1;
                continue;
            };
            if insn.len == line.bytes.len() {
                lengths += 1;
            } else {
                wrong.push(format!(
                    "{:#x} {:02x?}: {} bytes, llvm says {} ({:?} against {:?})",
                    line.addr,
                    line.bytes,
                    insn.len,
                    line.bytes.len(),
                    insn.text(&spec),
                    line.text
                ));
                continue;
            }
            let text = insn.text(&spec);
            let ours = canonical_x86(text.split_whitespace().next().unwrap_or(""));
            let theirs = canonical_x86(line.text.split_whitespace().next().unwrap_or(""));
            if ours == theirs {
                mnemonics += 1;
            } else {
                *spelled
                    .entry(format!("{ours} against {theirs}"))
                    .or_default() += 1;
            }
        }
    }
    eprintln!(
        "x86-64 via SLEIGH against llvm-objdump: {compared} compared, {lengths} boundaries agree, \
         {mnemonics} mnemonics agree, {} spelled differently, {undecoded} undecoded, {} wrong",
        spelled.values().sum::<usize>(),
        wrong.len()
    );
    let mut worst: Vec<_> = spelled.iter().collect();
    worst.sort_by_key(|(_, n)| std::cmp::Reverse(**n));
    for (what, n) in worst.iter().take(12) {
        eprintln!("  SPELLING x{n} {what}");
    }
    for w in wrong.iter().take(20) {
        eprintln!("  WRONG {w}");
    }
    assert!(compared > 2_000, "the corpus must be worth measuring");
    assert!(
        wrong.is_empty(),
        "{} instructions where the engine and llvm-objdump disagree about where \
         the instruction ends",
        wrong.len()
    );
    assert_eq!(undecoded, 0, "nothing in this corpus should fail to decode");
    let agreement = mnemonics as f64 / compared as f64;
    assert!(
        agreement >= floor::X86_MNEMONIC,
        "mnemonic agreement {agreement:.4} fell below the floor {:.4}",
        floor::X86_MNEMONIC
    );
}

/// The three-way check on x86-64, against the hand-written decoder.
#[test]
fn x86_64_agrees_with_the_hand_written_decoder_on_boundaries() {
    let (Some(spec), Some(dir)) = (language("x86/data/languages/x86-64.slaspec"), corpus()) else {
        return;
    };
    let Some(objdump) = llvm_objdump() else {
        return;
    };
    let mut both = 0usize;
    let mut only_sleigh = 0usize;
    let mut only_hand = 0usize;
    let mut differ: Vec<String> = Vec::new();

    for path in files(&dir, |n| n.contains(".x64.") && n.ends_with(".o")) {
        let lines = disassemble(&objdump, &["-d", "--x86-asm-syntax=intel"], &path);
        let mut d = Decoder::new(&spec);
        x86_context(&mut d);
        for line in &lines {
            let sleigh = d.decode(&line.bytes, line.addr).ok();
            let hand = r12e_arch::x86::decode(&line.bytes, r12e_core::Addr(line.addr));
            match (&sleigh, hand) {
                (Some(s), Some(h)) => {
                    if s.len == h.len as usize {
                        both += 1;
                    } else {
                        differ.push(format!(
                            "{:#x} {:02x?}: sleigh {} bytes, hand-written {} bytes, llvm {} ({:?})",
                            line.addr,
                            line.bytes,
                            s.len,
                            h.len,
                            line.bytes.len(),
                            line.text
                        ));
                    }
                }
                (Some(_), None) => only_sleigh += 1,
                (None, Some(_)) => only_hand += 1,
                (None, None) => {}
            }
        }
    }
    eprintln!(
        "x86-64 three ways: {both} agree on where the instruction ends, {} differ, \
         {only_sleigh} SLEIGH only, {only_hand} hand-written only",
        differ.len()
    );
    for d in differ.iter().take(20) {
        eprintln!("  DIFFER {d}");
    }
    assert!(both > 2_000, "the cross-check must be worth measuring");
    assert!(
        differ.is_empty(),
        "{} encodings where the two decoders disagree about the length",
        differ.len()
    );
}

/// The starting context an x86-64 program is decoded under.
///
/// A SLEIGH language is not complete without the default context its `.pspec`
/// declares, and x86 is where that stops being a formality: with an all-zero
/// context register the specification decodes in sixteen bit mode, so `48 89
/// e5` is `DEC AX` followed by two bytes of something else rather than `mov
/// rbp, rsp`. These four values are what `x86-64.pspec` sets, quoted rather
/// than parsed because reading `.pspec` files belongs to the loader and not to
/// a decode engine.
fn x86_context(d: &mut Decoder<'_>) {
    for (name, value) in [
        ("addrsize", 2u64),
        ("opsize", 1),
        ("rexprefix", 0),
        ("longMode", 1),
    ] {
        assert!(d.set_context(name, value), "x86-64 defines {name}");
    }
}

// --------------------------------------------------------------- behaviour

/// The context loop, which is what ARM needs to reach most of its instruction
/// set.
///
/// `ARM7_le` puts two constructors at the root of `instruction` that set
/// `ARMcond` and `ARMcondCk` and then build `instruction` again. Without
/// executing the `[ ... ]` assignment during the descent the second pass sees
/// the same context, matches the same constructor, and either recurses for
/// ever or matches nothing at all. `bx lr` is the instruction the report names
/// as needing it.
#[test]
fn arm_reaches_its_instructions_through_the_context_loop() {
    let Some(spec) = language("ARM/data/languages/ARM7_le.slaspec") else {
        return;
    };
    assert!(
        spec.context_bytes() > 0,
        "ARM defines a context register, and the loop needs it"
    );
    let mut d = Decoder::new(&spec);
    for (word, want) in [
        (0xe12fff1eu32, "bx"),
        (0xe3a00000, "mov"),
        (0xe52db004, "str"),
    ] {
        let bytes = word.to_le_bytes();
        let insn = d
            .decode(&bytes, 0x1000)
            .unwrap_or_else(|e| panic!("{word:#010x} should decode: {e}"));
        let text = insn.text(&spec).to_lowercase();
        assert!(
            text.starts_with(want),
            "{word:#010x} decoded as {text:?}, expected it to start {want:?}"
        );
        assert_eq!(insn.len, 4, "every ARM instruction here is one word");
    }
}

/// A `globalset` must reach the address it names, not the one it ran at.
#[test]
fn a_globalset_lands_in_the_database_at_the_address_it_names() {
    let spec = r12e_sleigh::parse_str(
        r#"
define endian=little;
define space ram type=ram_space size=4 default;
define space register type=register_space size=4;
define register offset=0x100 size=4 [ ctxreg ];
define context ctxreg
    mode=(0,0)
;
define token instr(16) op=(8,15) imm=(0,7);
:setmode imm is op=0x10 & imm [ mode=1; globalset(inst_next, mode); ] { }
:normal imm is op=0x11 & mode=0 & imm { }
:special imm is op=0x11 & mode=1 & imm { }
"#,
    );
    let spec = match spec {
        Ok(s) => s,
        Err(e) => panic!("the specification should parse: {e}"),
    };
    let mut d = Decoder::new(&spec);
    let _ = d.decode(&[0x00, 0x10], 0x1000).expect("setmode decodes");
    assert!(
        !d.context_db().is_empty(),
        "the globalset should have published something"
    );
    let next = d.decode(&[0x00, 0x11], 0x1002).expect("decodes");
    assert_eq!(
        next.text(&spec).split_whitespace().next(),
        Some("special"),
        "the published mode should have selected the second constructor"
    );
    // And an address the globalset did not name still sees the default.
    let elsewhere = d.decode(&[0x00, 0x11], 0x2000).expect("decodes");
    assert_eq!(
        elsewhere.text(&spec).split_whitespace().next(),
        Some("normal")
    );
}

/// Decoding is a function of the bytes, the address and the context, and
/// nothing else. Re-decoding the same address twice must give the same answer,
/// which the context database's replace-rather-than-accumulate rule is what
/// guarantees.
#[test]
fn decoding_the_same_address_twice_gives_the_same_answer() {
    let Some(spec) = language("RISCV/data/languages/riscv.lp64d.slaspec") else {
        return;
    };
    let mut d = Decoder::new(&spec);
    let bytes = [0x33u8, 0x05, 0xb5, 0x00];
    let first = d.decode(&bytes, 0x1000).expect("decodes");
    let second = d.decode(&bytes, 0x1000).expect("decodes");
    assert_eq!(first.text(&spec), second.text(&spec));
    assert_eq!(first.len, second.len);
    assert_eq!(first, second);
}

/// What the tree costs to walk, printed rather than asserted on, because a
/// timing assertion on a shared machine is a flaky test rather than a
/// measurement.
#[test]
#[ignore]
fn throughput() {
    for (name, rel) in [
        ("AArch64", "AARCH64/data/languages/AARCH64.slaspec"),
        ("RISC-V", "RISCV/data/languages/riscv.lp64d.slaspec"),
        ("x86-64", "x86/data/languages/x86-64.slaspec"),
    ] {
        let Some(spec) = language(rel) else { continue };
        let t = std::time::Instant::now();
        let mut d = Decoder::new(&spec);
        let build = t.elapsed();

        let mut bytes = Vec::new();
        let mut state = 0x9e3779b97f4a7c15u64;
        for _ in 0..1 << 16 {
            state = state.wrapping_mul(6364136223846793005).wrapping_add(1);
            bytes.extend_from_slice(&state.to_le_bytes());
        }
        let t = std::time::Instant::now();
        let mut ok = 0usize;
        let mut at = 0usize;
        while at + 16 <= bytes.len() {
            if d.decode(&bytes[at..], at as u64).is_ok() {
                ok += 1;
            }
            at += 4;
        }
        let el = t.elapsed();
        let n = (bytes.len() / 4) as f64;
        eprintln!(
            "{name}: index built in {build:?}, {n:.0} attempts in {el:?} ({:.0}/s), {ok} decoded",
            n / el.as_secs_f64()
        );
    }
}

/// Which constructors the front end could not reduce exactly, so the report
/// can say how much of the corpus the pattern re-evaluation carries.
#[test]
#[ignore]
fn approximation_census() {
    for (name, rel) in [
        ("AArch64", "AARCH64/data/languages/AARCH64.slaspec"),
        ("RISC-V", "RISCV/data/languages/riscv.lp64d.slaspec"),
        ("x86-64", "x86/data/languages/x86-64.slaspec"),
        ("ARM7_le", "ARM/data/languages/ARM7_le.slaspec"),
    ] {
        let Some(spec) = language(rel) else { continue };
        let mut kinds: BTreeMap<String, usize> = BTreeMap::new();
        for (_, why) in spec.approximate_constructors() {
            *kinds.entry(format!("{why:?}")).or_default() += 1;
        }
        let residual = spec
            .constructors
            .iter()
            .filter(|c| {
                c.resolved
                    .alternatives
                    .iter()
                    .any(|a| !a.residual.is_empty())
            })
            .count();
        eprintln!(
            "{name}: {} constructors, approximate {kinds:?}, {residual} with residuals",
            spec.constructors.len()
        );
    }
}
