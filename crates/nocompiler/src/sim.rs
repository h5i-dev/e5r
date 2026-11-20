//! A simulated performance oracle (spec-v1-refine.md item 8;
//! docs/isa/sim.md): run a statically linked profile binary, count the
//! instructions it executes, and estimate its cycles on a model of a
//! single-issue in-order core. There is no RV64 hardware here and qemu has no
//! timing model, so every number this produces is labelled "simulated".
//!
//! The instruction semantics are those of `lean/NoCompiler/Machine.lean`
//! (RV64IM + Zba + Zbb, misaligned accesses and jumps fault) and the
//! environment those of `Env.lean` (write, read, exit, exit_group), checked
//! against qemu-riscv64 on random programs over every instruction
//! (tests/sim.rs). Not trusted by any proof.

use crate::elf;
use crate::isa::{self, BrOp, IOp, Instr, LdOp, ROp, RWOp, Reg, ShOp, ShWOp, StOp, UOp};
use std::collections::{BTreeMap, HashMap};
use std::io::{Read, Write};

/// The timing model's parameters (docs/isa/sim.md). Latencies are the
/// cycles from issue until the result can be used.
#[derive(Clone, Debug)]
pub struct Model {
    pub name: &'static str,
    pub load_latency: u64,
    pub mul_latency: u64,
    /// Division and remainder: not pipelined; the divider is busy this long.
    pub div_latency: u64,
    pub divw_latency: u64,
    pub mispredict_penalty: u64,
    /// 2-bit counters, indexed by pc / 4.
    pub bht_entries: usize,
    /// Return-address stack depth.
    pub ras_depth: usize,
}

impl Model {
    /// The default: a single-issue, in-order, five-stage RV64 pipeline in the
    /// style of Rocket and the SiFive U54 (docs/isa/sim.md says which numbers
    /// are assumptions).
    pub fn inorder5() -> Model {
        Model {
            name: "inorder5 (single-issue in-order 5-stage, Rocket/U54-style; simulated)",
            load_latency: 2,
            mul_latency: 3,
            div_latency: 65,
            divw_latency: 33,
            mispredict_penalty: 3,
            bht_entries: 512,
            ras_depth: 6,
        }
    }
}

/// What a run produced.
#[derive(Clone, Debug, Default)]
pub struct Report {
    pub instructions: u64,
    pub cycles: u64,
    pub branches: u64,
    pub mispredicts: u64,
    pub loads: u64,
    pub stores: u64,
    pub ecalls: u64,
    /// The exit status, or `None` if the run faulted or ran out of fuel.
    pub exit: Option<u64>,
    /// Why the run stopped, if not by exit.
    pub fault: Option<String>,
    /// Per function (by symbol): (instructions, cycles), inclusive of callees.
    pub inclusive: BTreeMap<String, (u64, u64)>,
    /// Per function: (instructions, cycles) at its own code.
    pub own: BTreeMap<String, (u64, u64)>,
    /// Calls per function.
    pub calls: BTreeMap<String, u64>,
}

struct Mem {
    pages: HashMap<u64, Box<[u8; 4096]>>,
}

impl Mem {
    fn page(&mut self, a: u64) -> &mut [u8; 4096] {
        self.pages
            .entry(a >> 12)
            .or_insert_with(|| Box::new([0; 4096]))
    }
    fn read(&mut self, a: u64, n: u64) -> u64 {
        let mut v = 0u64;
        for k in 0..n {
            let x = a.wrapping_add(k);
            v |= (self.page(x)[(x & 0xfff) as usize] as u64) << (8 * k);
        }
        v
    }
    fn write(&mut self, a: u64, v: u64, n: u64) {
        for k in 0..n {
            let x = a.wrapping_add(k);
            self.page(x)[(x & 0xfff) as usize] = (v >> (8 * k)) as u8;
        }
    }
}

fn sext(v: u64, bits: u32) -> u64 {
    let s = 64 - bits;
    (((v << s) as i64) >> s) as u64
}

fn sext32(v: u64) -> u64 {
    v as u32 as i32 as i64 as u64
}

fn imm(i: isa::Imm) -> u64 {
    i.signed() as u64
}

fn eval_r(op: ROp, x: u64, y: u64) -> u64 {
    use ROp::*;
    let (sx, sy) = (x as i64, y as i64);
    match op {
        Add => x.wrapping_add(y),
        Sub => x.wrapping_sub(y),
        Sll => x << (y & 63),
        Slt => (sx < sy) as u64,
        Sltu => (x < y) as u64,
        Xor => x ^ y,
        Srl => x >> (y & 63),
        Sra => (sx >> (y & 63)) as u64,
        Or => x | y,
        And => x & y,
        Mul => x.wrapping_mul(y),
        Mulh => ((sx as i128 * sy as i128) >> 64) as u64,
        Mulhsu => ((sx as i128 * y as u128 as i128) >> 64) as u64,
        Mulhu => ((x as u128 * y as u128) >> 64) as u64,
        Div => {
            if y == 0 {
                u64::MAX
            } else if sx == i64::MIN && sy == -1 {
                x
            } else {
                (sx / sy) as u64
            }
        }
        Divu => x.checked_div(y).unwrap_or(u64::MAX),
        Rem => {
            if y == 0 {
                x
            } else if sx == i64::MIN && sy == -1 {
                0
            } else {
                (sx % sy) as u64
            }
        }
        Remu => {
            if y == 0 {
                x
            } else {
                x % y
            }
        }
        Sh1add => (x << 1).wrapping_add(y),
        Sh2add => (x << 2).wrapping_add(y),
        Sh3add => (x << 3).wrapping_add(y),
        Andn => x & !y,
        Orn => x | !y,
        Xnor => !(x ^ y),
        Max => {
            if sx < sy {
                y
            } else {
                x
            }
        }
        Maxu => x.max(y),
        Min => {
            if sx < sy {
                x
            } else {
                y
            }
        }
        Minu => x.min(y),
        Rol => x.rotate_left((y & 63) as u32),
        Ror => x.rotate_right((y & 63) as u32),
    }
}

fn eval_rw(op: RWOp, x: u64, y: u64) -> u64 {
    use RWOp::*;
    let (a, b) = (x as u32, y as u32);
    let (sa, sb) = (a as i32, b as i32);
    let z = |v: u64| v & 0xffff_ffff;
    let w = |v: u32| v as i32 as i64 as u64;
    match op {
        Addw => w(a.wrapping_add(b)),
        Subw => w(a.wrapping_sub(b)),
        Sllw => w(a << (b & 31)),
        Srlw => w(a >> (b & 31)),
        Sraw => w((sa >> (b & 31)) as u32),
        Mulw => w(a.wrapping_mul(b)),
        Divw => w(if b == 0 {
            u32::MAX
        } else if sa == i32::MIN && sb == -1 {
            a
        } else {
            (sa / sb) as u32
        }),
        Divuw => w(a.checked_div(b).unwrap_or(u32::MAX)),
        Remw => w(if b == 0 {
            a
        } else if sa == i32::MIN && sb == -1 {
            0
        } else {
            (sa % sb) as u32
        }),
        Remuw => w(if b == 0 { a } else { a % b }),
        Adduw => z(x).wrapping_add(y),
        Sh1adduw => (z(x) << 1).wrapping_add(y),
        Sh2adduw => (z(x) << 2).wrapping_add(y),
        Sh3adduw => (z(x) << 3).wrapping_add(y),
        Rolw => w(a.rotate_left(b & 31)),
        Rorw => w(a.rotate_right(b & 31)),
    }
}

fn eval_u(op: UOp, x: u64) -> u64 {
    use UOp::*;
    match op {
        Clz => x.leading_zeros() as u64,
        Ctz => x.trailing_zeros() as u64,
        Cpop => x.count_ones() as u64,
        Clzw => (x as u32).leading_zeros() as u64,
        Ctzw => (x as u32).trailing_zeros() as u64,
        Cpopw => (x as u32).count_ones() as u64,
        Sextb => x as u8 as i8 as i64 as u64,
        Sexth => x as u16 as i16 as i64 as u64,
        Zexth => x & 0xffff,
        Rev8 => x.swap_bytes(),
        Orcb => {
            let mut r = 0;
            for k in 0..8 {
                if (x >> (8 * k)) & 0xff != 0 {
                    r |= 0xff << (8 * k);
                }
            }
            r
        }
    }
}

/// The registers an instruction reads.
/// A register instruction's result: the register it writes and the value,
/// from the source registers' values (`None` for any other instruction).
pub(crate) fn alu(i: &Instr, rx: &dyn Fn(Reg) -> u64) -> Option<(Reg, u64)> {
    match *i {
        Instr::Lui(rd, im) => Some((rd, sext((im.value as u64) << 12, 32))),
        Instr::IOp(op, rd, rs1, im) => {
            let (v, k) = (rx(rs1), imm(im));
            Some((
                rd,
                match op {
                    IOp::Addi => v.wrapping_add(k),
                    IOp::Slti => ((v as i64) < (k as i64)) as u64,
                    IOp::Sltiu => (v < k) as u64,
                    IOp::Xori => v ^ k,
                    IOp::Ori => v | k,
                    IOp::Andi => v & k,
                },
            ))
        }
        Instr::Addiw(rd, rs1, im) => Some((rd, sext32(rx(rs1).wrapping_add(imm(im))))),
        Instr::Shift(op, rd, rs1, sh) => {
            let (v, n) = (rx(rs1), sh.value);
            Some((
                rd,
                match op {
                    ShOp::Slli => v << n,
                    ShOp::Srli => v >> n,
                    ShOp::Srai => ((v as i64) >> n) as u64,
                    ShOp::Rori => v.rotate_right(n),
                    ShOp::Slliuw => (v & 0xffff_ffff) << n,
                },
            ))
        }
        Instr::ShiftW(op, rd, rs1, sh) => {
            let (v, n) = (rx(rs1) as u32, sh.value);
            Some((
                rd,
                sext32(match op {
                    ShWOp::Slliw => (v << n) as u64,
                    ShWOp::Srliw => (v >> n) as u64,
                    ShWOp::Sraiw => ((v as i32) >> n) as u32 as u64,
                    ShWOp::Roriw => v.rotate_right(n) as u64,
                }),
            ))
        }
        Instr::ROp(op, rd, a, b) => Some((rd, eval_r(op, rx(a), rx(b)))),
        Instr::RWOp(op, rd, a, b) => Some((rd, eval_rw(op, rx(a), rx(b)))),
        Instr::UOp(op, rd, rs1) => Some((rd, eval_u(op, rx(rs1)))),
        _ => None,
    }
}

fn sources(i: &Instr) -> [Option<Reg>; 2] {
    match *i {
        Instr::Jalr(_, a, _)
        | Instr::Load(_, _, a, _)
        | Instr::IOp(_, _, a, _)
        | Instr::Addiw(_, a, _)
        | Instr::Shift(_, _, a, _)
        | Instr::ShiftW(_, _, a, _)
        | Instr::UOp(_, _, a) => [Some(a), None],
        Instr::Branch(_, a, b, _)
        | Instr::Store(_, a, b, _)
        | Instr::ROp(_, _, a, b)
        | Instr::RWOp(_, _, a, b) => [Some(a), Some(b)],
        Instr::Ecall => [Some(Reg(17)), Some(Reg(10))],
        _ => [None, None],
    }
}

fn latency(m: &Model, i: &Instr) -> u64 {
    match *i {
        Instr::Load(..) => m.load_latency,
        Instr::ROp(ROp::Mul | ROp::Mulh | ROp::Mulhsu | ROp::Mulhu, ..)
        | Instr::RWOp(RWOp::Mulw, ..) => m.mul_latency,
        Instr::ROp(ROp::Div | ROp::Divu | ROp::Rem | ROp::Remu, ..) => m.div_latency,
        Instr::RWOp(RWOp::Divw | RWOp::Divuw | RWOp::Remw | RWOp::Remuw, ..) => m.divw_latency,
        _ => 1,
    }
}

const STACK_TOP: u64 = 0x7fff_ff00_0000;

/// Run `bytes` (a static RV64 ELF) from its entry with `stdin` as input,
/// writing what it writes to fd 1 and 2 into `stdout`, for at most `fuel`
/// instructions.
pub fn run(
    bytes: &[u8],
    stdin: &[u8],
    stdout: &mut Vec<u8>,
    m: &Model,
    fuel: u64,
) -> Result<Report, String> {
    let e = elf::Elf::parse(bytes).map_err(|e| e.to_string())?;
    let mut mem = Mem {
        pages: HashMap::new(),
    };
    // Load: every allocated section at its address (NOBITS stay zero).
    for s in &e.sections {
        if s.flags & elf::SHF_ALLOC != 0 && s.kind != elf::SHT_NOBITS {
            for (k, b) in e.bytes(s).iter().enumerate() {
                mem.write(s.addr + k as u64, *b as u64, 1);
            }
        }
    }
    // Functions, for attribution.
    let mut funcs: Vec<(u64, u64, String)> = e
        .functions()
        .iter()
        .map(|f| (f.value, f.value + f.size, f.name.clone()))
        .collect();
    funcs.sort();
    let func_at = |pc: u64| -> Option<&str> {
        let k = funcs.partition_point(|f| f.0 <= pc);
        (k > 0 && pc < funcs[k - 1].1).then(|| funcs[k - 1].2.as_str())
    };
    let mut x = [0u64; 32];
    x[2] = STACK_TOP - 0x1000;
    let mut pc = e.entry;
    let mut r = Report::default();
    // Timing state.
    let mut cycle = 0u64;
    let mut ready = [0u64; 32];
    let mut div_free = 0u64;
    let mut bht = vec![1u8; m.bht_entries.max(1)];
    let mut ras: Vec<u64> = Vec::new();
    let mut btb: HashMap<u64, u64> = HashMap::new();
    // Attribution: the stack of (function, instructions, cycles) at entry.
    let mut frames: Vec<(String, u64, u64, u64)> = Vec::new(); // name, instr at entry, cycle at entry, return address
    let mut input = stdin;
    let mut current = func_at(pc).map(String::from);
    if let Some(f) = &current {
        frames.push((f.clone(), 0, 0, u64::MAX));
        *r.calls.entry(f.clone()).or_default() += 1;
    }
    let close = |frames: &mut Vec<(String, u64, u64, u64)>, r: &mut Report, n: u64, c: u64| {
        if let Some((f, n0, c0, _)) = frames.pop() {
            // Only the outermost activation of a recursive function counts.
            if !frames.iter().any(|g| g.0 == f) {
                let e = r.inclusive.entry(f).or_default();
                e.0 += n - n0;
                e.1 += c - c0;
            }
        }
    };
    loop {
        if r.instructions >= fuel {
            r.fault = Some(format!("out of fuel after {fuel} instructions"));
            break;
        }
        if pc % 4 != 0 {
            r.fault = Some(format!("misaligned pc {pc:#x}"));
            break;
        }
        let w = mem.read(pc, 4) as u32;
        let Some(i) = isa::decode(w) else {
            r.fault = Some(format!("{pc:#x}: {w:#010x} is not in the profile"));
            break;
        };
        // Timing: issue when the sources are ready (and the divider is free).
        let mut issue = cycle;
        for s in sources(&i).into_iter().flatten() {
            if s.0 != 0 {
                issue = issue.max(ready[s.0 as usize]);
            }
        }
        let is_div = matches!(
            i,
            Instr::ROp(ROp::Div | ROp::Divu | ROp::Rem | ROp::Remu, ..)
                | Instr::RWOp(RWOp::Divw | RWOp::Divuw | RWOp::Remw | RWOp::Remuw, ..)
        );
        if is_div {
            issue = issue.max(div_free);
        }
        let c_before = cycle;
        cycle = issue + 1;
        let rx = |reg: Reg| if reg.0 == 0 { 0 } else { x[reg.0 as usize] };
        let mut next = pc.wrapping_add(4);
        let mut dest: Option<(Reg, u64)> = None;
        let mut fault = None;
        match i {
            Instr::Lui(..)
            | Instr::IOp(..)
            | Instr::Addiw(..)
            | Instr::Shift(..)
            | Instr::ShiftW(..)
            | Instr::ROp(..)
            | Instr::RWOp(..)
            | Instr::UOp(..) => dest = alu(&i, &rx),
            Instr::Auipc(rd, im) => {
                dest = Some((rd, pc.wrapping_add(sext((im.value as u64) << 12, 32))))
            }
            Instr::Jal(rd, off) => {
                dest = Some((rd, pc.wrapping_add(4)));
                next = pc.wrapping_add(imm(off));
            }
            Instr::Jalr(rd, rs1, off) => {
                let t = rx(rs1).wrapping_add(imm(off)) & !1;
                dest = Some((rd, pc.wrapping_add(4)));
                // Prediction: returns through the RAS, other jumps through
                // the BTB (the last target seen at this pc).
                let predicted = if rd.0 == 0 && rs1.0 == 1 {
                    ras.pop()
                } else {
                    btb.insert(pc, t)
                };
                if predicted != Some(t) {
                    cycle += m.mispredict_penalty;
                }
                if rd.0 == 1 {
                    ras.push(pc.wrapping_add(4));
                    if ras.len() > m.ras_depth {
                        ras.remove(0);
                    }
                }
                next = t;
            }
            Instr::Branch(op, a, b, off) => {
                let (va, vb) = (rx(a), rx(b));
                let taken = match op {
                    BrOp::Beq => va == vb,
                    BrOp::Bne => va != vb,
                    BrOp::Blt => (va as i64) < (vb as i64),
                    BrOp::Bge => (va as i64) >= (vb as i64),
                    BrOp::Bltu => va < vb,
                    BrOp::Bgeu => va >= vb,
                };
                r.branches += 1;
                let k = ((pc >> 2) as usize) % bht.len();
                if (bht[k] >= 2) != taken {
                    r.mispredicts += 1;
                    cycle += m.mispredict_penalty;
                }
                bht[k] = if taken {
                    (bht[k] + 1).min(3)
                } else {
                    bht[k].saturating_sub(1)
                };
                if taken {
                    next = pc.wrapping_add(imm(off));
                }
            }
            Instr::Load(op, rd, rs1, off) => {
                let a = rx(rs1).wrapping_add(imm(off));
                let n = match op {
                    LdOp::Lb | LdOp::Lbu => 1,
                    LdOp::Lh | LdOp::Lhu => 2,
                    LdOp::Lw | LdOp::Lwu => 4,
                    LdOp::Ld => 8,
                };
                if a % n != 0 {
                    fault = Some(format!("{pc:#x}: misaligned load at {a:#x}"));
                } else {
                    let v = mem.read(a, n);
                    let v = match op {
                        LdOp::Lb => sext(v, 8),
                        LdOp::Lh => sext(v, 16),
                        LdOp::Lw => sext(v, 32),
                        _ => v,
                    };
                    r.loads += 1;
                    dest = Some((rd, v));
                }
            }
            Instr::Store(op, rs1, rs2, off) => {
                let a = rx(rs1).wrapping_add(imm(off));
                let n = match op {
                    StOp::Sb => 1,
                    StOp::Sh => 2,
                    StOp::Sw => 4,
                    StOp::Sd => 8,
                };
                if a % n != 0 {
                    fault = Some(format!("{pc:#x}: misaligned store at {a:#x}"));
                } else {
                    r.stores += 1;
                    mem.write(a, rx(rs2), n);
                }
            }
            Instr::Ecall => {
                r.ecalls += 1;
                match x[17] {
                    64 => {
                        let n = x[12];
                        let mut buf = Vec::with_capacity(n as usize);
                        for k in 0..n {
                            buf.push(mem.read(x[11].wrapping_add(k), 1) as u8);
                        }
                        if x[10] == 1 || x[10] == 2 {
                            stdout.extend_from_slice(&buf);
                        }
                        dest = Some((Reg(10), n));
                    }
                    63 => {
                        let n = (x[12] as usize).min(input.len());
                        for (k, b) in input[..n].iter().enumerate() {
                            mem.write(x[11].wrapping_add(k as u64), *b as u64, 1);
                        }
                        input = &input[n..];
                        dest = Some((Reg(10), n as u64));
                    }
                    93 | 94 => {
                        r.instructions += 1;
                        r.exit = Some(x[10]);
                        break;
                    }
                    n => fault = Some(format!("{pc:#x}: syscall {n} is not modelled")),
                }
            }
        }
        if let Some(f) = fault {
            r.fault = Some(f);
            break;
        }
        r.instructions += 1;
        if let Some((rd, v)) = dest {
            if rd.0 != 0 {
                x[rd.0 as usize] = v;
                ready[rd.0 as usize] = issue + latency(m, &i);
            }
        }
        if is_div {
            div_free = issue + latency(m, &i);
        }
        if next % 4 != 0 && matches!(i, Instr::Jal(..) | Instr::Jalr(..) | Instr::Branch(..)) {
            r.fault = Some(format!("{pc:#x}: jump to misaligned {next:#x}"));
            break;
        }
        // Attribution.
        if let Some(f) = &current {
            let e = r.own.entry(f.clone()).or_default();
            e.0 += 1;
            e.1 += cycle - c_before;
        }
        let call = matches!(i, Instr::Jal(Reg(1), _) | Instr::Jalr(Reg(1), _, _));
        let ret = matches!(i, Instr::Jalr(Reg(0), Reg(1), off) if off.signed() == 0);
        if call {
            if let Some(g) = func_at(next) {
                frames.push((g.to_string(), r.instructions, cycle, pc.wrapping_add(4)));
                *r.calls.entry(g.to_string()).or_default() += 1;
            }
        } else if ret {
            if frames.last().is_some_and(|f| f.3 == next) {
                {
                    let n = r.instructions;
                    close(&mut frames, &mut r, n, cycle);
                }
            }
        } else if matches!(i, Instr::Jalr(Reg(0), Reg(6), _) | Instr::Jal(Reg(0), _)) {
            // A tail call: the caller's activation becomes the callee's.
            if let (Some(g), Some(f)) = (func_at(next), &current) {
                if g != f && func_at(next) != func_at(pc) {
                    let ra = frames.last().map(|f| f.3).unwrap_or(u64::MAX);
                    {
                        let n = r.instructions;
                        close(&mut frames, &mut r, n, cycle);
                    }
                    frames.push((g.to_string(), r.instructions, cycle, ra));
                    *r.calls.entry(g.to_string()).or_default() += 1;
                }
            }
        }
        pc = next;
        current = func_at(pc).map(String::from);
    }
    while !frames.is_empty() {
        {
            let n = r.instructions;
            close(&mut frames, &mut r, n, cycle);
        }
    }
    r.cycles = cycle;
    Ok(r)
}

/// `nocompiler sim` output: the run's counts, then per function.
pub fn report_text(r: &Report, m: &Model, only: Option<&str>) -> String {
    let mut o = String::new();
    use std::fmt::Write as _;
    let _ = writeln!(o, "model        {}", m.name);
    match (&r.exit, &r.fault) {
        (Some(c), _) => {
            let _ = writeln!(o, "exit         {c}");
        }
        (None, Some(f)) => {
            let _ = writeln!(o, "stopped      {f}");
        }
        _ => {}
    }
    let _ = writeln!(o, "instructions {}", r.instructions);
    let _ = writeln!(o, "cycles       {} (simulated)", r.cycles);
    let _ = writeln!(
        o,
        "branches     {} ({} mispredicted)",
        r.branches, r.mispredicts
    );
    let _ = writeln!(
        o,
        "loads        {}  stores {}  ecalls {}",
        r.loads, r.stores, r.ecalls
    );
    let _ = writeln!(
        o,
        "\n{:<40} {:>8} {:>14} {:>14} {:>12} {:>12}",
        "function", "calls", "instr (incl)", "cycles (incl)", "instr (own)", "cycles (own)"
    );
    let mut names: Vec<&String> = r.own.keys().chain(r.inclusive.keys()).collect();
    names.sort();
    names.dedup();
    for f in names {
        if only.is_some_and(|o| o != f) {
            continue;
        }
        let i = r.inclusive.get(f).copied().unwrap_or_default();
        let s = r.own.get(f).copied().unwrap_or_default();
        let _ = writeln!(
            o,
            "{:<40} {:>8} {:>14} {:>14} {:>12} {:>12}",
            f,
            r.calls.get(f).copied().unwrap_or(0),
            i.0,
            i.1,
            s.0,
            s.1
        );
    }
    o
}

pub fn report_json(r: &Report, m: &Model) -> String {
    let q = |s: &str| format!("\"{}\"", s.replace('\\', "\\\\").replace('"', "\\\""));
    let fs: Vec<String> = r.own.keys().chain(r.inclusive.keys()).collect::<std::collections::BTreeSet<_>>().into_iter().map(|f| {
        let i = r.inclusive.get(f).copied().unwrap_or_default();
        let s = r.own.get(f).copied().unwrap_or_default();
        format!("{{\"name\":{},\"calls\":{},\"instructions\":{},\"cycles\":{},\"own_instructions\":{},\"own_cycles\":{}}}",
            q(f), r.calls.get(f).copied().unwrap_or(0), i.0, i.1, s.0, s.1)
    }).collect();
    format!(
        "{{\"model\":{},\"simulated\":true,\"exit\":{},\"fault\":{},\"instructions\":{},\"cycles\":{},\"branches\":{},\"mispredicts\":{},\"loads\":{},\"stores\":{},\"ecalls\":{},\"functions\":[{}]}}",
        q(m.name),
        r.exit
            .map(|c| c.to_string())
            .unwrap_or_else(|| "null".into()),
        r.fault.as_deref().map(q).unwrap_or_else(|| "null".into()),
        r.instructions,
        r.cycles,
        r.branches,
        r.mispredicts,
        r.loads,
        r.stores,
        r.ecalls,
        fs.join(",")
    )
}

/// Read all of a reader (for `--stdin`).
pub fn read_all(mut r: impl Read) -> Vec<u8> {
    let mut v = Vec::new();
    let _ = r.read_to_end(&mut v);
    v
}

/// Write the program's output.
pub fn write_out(b: &[u8]) {
    let _ = std::io::stdout().write_all(b);
}
