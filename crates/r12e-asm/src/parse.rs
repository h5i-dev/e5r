//! Text to [`Insn`], the shape the decoders produce.
//!
//! The grammar is not an assembler's: it is exactly what the two printers in
//! `r12e-arch` emit, so a line copied out of `r12e disas` parses. Anything
//! else that happens to parse is a bonus, never a promise.

use r12e_core::{Addr, Arch};

use r12e_arch::insn::{AddrMode, Cond, Extend, Flow, Insn, MAX_OPERANDS, Mem, Operand, Reg, Shift};

use crate::error::AsmError;
use crate::lex::{Spanned, Tok, lex};
use crate::{aarch64, x86};

/// Parse one instruction for `arch`, sited at `addr`.
///
/// The `len` field is left at zero: only the encoder knows it.
pub fn parse(arch: &Arch, text: &str, addr: Addr) -> Result<Insn, AsmError> {
    let toks = lex(text)?;
    match arch {
        Arch::AArch64 => parse_with(&toks, addr, true),
        Arch::X86_64 => parse_with(&toks, addr, false),
        other => Err(AsmError::UnsupportedArch(format!("{other:?}"))),
    }
}

fn parse_with(toks: &[Spanned<'_>], addr: Addr, a64: bool) -> Result<Insn, AsmError> {
    let mut p = P {
        toks,
        i: 0,
        a64,
        addr,
    };
    p.insn()
}

struct P<'a> {
    toks: &'a [Spanned<'a>],
    i: usize,
    a64: bool,
    addr: Addr,
}

impl<'a> P<'a> {
    fn peek(&self) -> Option<Tok<'a>> {
        self.toks.get(self.i).map(|s| s.tok)
    }

    fn peek_at(&self, n: usize) -> Option<Tok<'a>> {
        self.toks.get(self.i + n).map(|s| s.tok)
    }

    fn bump(&mut self) -> Option<Tok<'a>> {
        let t = self.peek();
        if t.is_some() {
            self.i += 1;
        }
        t
    }

    fn at(&self) -> usize {
        self.toks.get(self.i).map(|s| s.at).unwrap_or(0)
    }

    fn err(&self, what: &str) -> AsmError {
        AsmError::Syntax {
            at: self.at(),
            what: what.to_string(),
        }
    }

    fn eat_punct(&mut self, c: u8) -> bool {
        if self.peek() == Some(Tok::Punct(c)) {
            self.i += 1;
            true
        } else {
            false
        }
    }

    fn expect_punct(&mut self, c: u8) -> Result<(), AsmError> {
        if self.eat_punct(c) {
            Ok(())
        } else {
            Err(self.err(&format!("expected `{}`", c as char)))
        }
    }

    fn ident(&mut self) -> Option<&'a str> {
        match self.peek() {
            Some(Tok::Ident(s)) => {
                self.i += 1;
                Some(s)
            }
            _ => None,
        }
    }

    /// An unsigned magnitude with an optional sign in front of it.
    fn signed(&mut self) -> Result<i64, AsmError> {
        let neg = self.eat_punct(b'-');
        if !neg {
            self.eat_punct(b'+');
        }
        match self.bump() {
            Some(Tok::Num(v)) => Ok(if neg {
                (v as i64).wrapping_neg()
            } else {
                v as i64
            }),
            _ => Err(self.err("expected a number")),
        }
    }

    /// The whole instruction.
    fn insn(&mut self) -> Result<Insn, AsmError> {
        let mut prefix: Option<&'static str> = None;
        if !self.a64 {
            // `lock`, `rep` and `repne` print ahead of the mnemonic.
            while let Some(Tok::Ident(w)) = self.peek() {
                let p = match w {
                    "lock" => "lock",
                    "rep" | "repe" => "rep",
                    "repne" | "repnz" => "repne",
                    _ => break,
                };
                // A bare `rep` with nothing after it is the mnemonic itself.
                if self.peek_at(1).is_none() {
                    break;
                }
                self.i += 1;
                prefix = Some(p);
            }
        }
        let name = match self.ident() {
            Some(n) => n,
            None => return Err(AsmError::Empty),
        };
        let mnemonic = if self.a64 {
            aarch64::intern(name)
        } else {
            x86::intern(name)
        }
        .ok_or_else(|| AsmError::UnknownMnemonic(name.to_string()))?;

        let mut ops: Vec<Operand> = Vec::new();
        if self.peek().is_some() {
            loop {
                if ops.len() >= MAX_OPERANDS {
                    return Err(AsmError::UnsupportedForm {
                        mnemonic: mnemonic.to_string(),
                        detail: "more operands than any encoding takes",
                    });
                }
                if self.a64 {
                    self.a64_operand(&mut ops)?;
                } else {
                    let o = self.x86_operand(mnemonic)?;
                    ops.push(o);
                }
                if !self.eat_punct(b',') {
                    break;
                }
            }
        }
        if self.i != self.toks.len() {
            return Err(self.err("trailing text after the operands"));
        }

        retarget(mnemonic, &mut ops);
        let mut i = Insn::new(self.addr, 0, mnemonic, Flow::Next);
        i.prefix = prefix;
        for o in ops {
            i.push(o);
        }
        Ok(i)
    }

    // ------------------------------------------------------------ AArch64

    /// One AArch64 operand, plus the shift or extend that rides behind it.
    fn a64_operand(&mut self, ops: &mut Vec<Operand>) -> Result<(), AsmError> {
        let base = self.a64_atom()?;
        // `x2, lsl #2` and `#0x1, lsl #12` both spell the qualifier as a
        // comma-separated word, so it is read here rather than by the loop.
        if self.peek() == Some(Tok::Punct(b','))
            && let Some(Tok::Ident(w)) = self.peek_at(1)
            && let Some(q) = qualifier(w)
        {
            self.i += 2;
            let amount = if self.peek() == Some(Tok::Punct(b'#')) {
                self.i += 1;
                let v = self.signed()?;
                u8::try_from(v).map_err(|_| AsmError::Range {
                    what: "shift amount",
                    value: v,
                    low: 0,
                    high: 63,
                })?
            } else {
                0
            };
            match (base, q) {
                (Operand::Reg(r), Qual::Shift(s)) => ops.push(Operand::Shifted(r, s, amount)),
                (Operand::Reg(r), Qual::Extend(e)) => ops.push(Operand::Extended(r, e, amount)),
                (other, Qual::Shift(s)) => {
                    ops.push(other);
                    ops.push(Operand::ShiftOp(s, amount));
                }
                (_, Qual::Extend(_)) => return Err(self.err("an extend needs a register")),
            }
            return Ok(());
        }
        ops.push(base);
        Ok(())
    }

    fn a64_atom(&mut self) -> Result<Operand, AsmError> {
        match self.peek() {
            Some(Tok::Punct(b'#')) => {
                self.i += 1;
                let v = self.signed()?;
                Ok(Operand::Imm(v))
            }
            Some(Tok::Punct(b'[')) => self.a64_mem(),
            Some(Tok::Num(_)) | Some(Tok::Punct(b'-')) => {
                // A bare number in A64 text is only ever a branch or literal
                // target, since every immediate carries a `#`.
                let v = self.signed()?;
                Ok(Operand::Addr(Addr(v as u64)))
            }
            Some(Tok::Ident(w)) => {
                self.i += 1;
                if let Some(r) = aarch64::register(w) {
                    return Ok(Operand::Reg(r));
                }
                if let Some(c) = aarch64::condition(w) {
                    return Ok(Operand::Cond(Cond(c)));
                }
                if let Some(n) = aarch64::name(w) {
                    return Ok(Operand::Name(n));
                }
                // A lane spelling is a SIMD operand, which this crate declines
                // rather than half-encodes. Saying so beats "unknown register",
                // which reads like a typo the user could fix.
                if w.contains('.') && w.starts_with('v') {
                    return Err(AsmError::UnsupportedForm {
                        mnemonic: w.to_string(),
                        detail: "Advanced SIMD and floating point are not encoded",
                    });
                }
                Err(AsmError::UnknownRegister(w.to_string()))
            }
            Some(Tok::Punct(b'{')) => Err(AsmError::UnsupportedForm {
                mnemonic: "a SIMD register list".to_string(),
                detail: "Advanced SIMD and floating point are not encoded",
            }),
            _ => Err(self.err("expected an operand")),
        }
    }

    fn a64_mem(&mut self) -> Result<Operand, AsmError> {
        self.expect_punct(b'[')?;
        let base = match self.ident().and_then(aarch64::register) {
            Some(r) => r,
            None => return Err(self.err("a memory operand needs a base register")),
        };
        let mut disp = 0i64;
        let mut index: Option<(Reg, Extend, u8)> = None;
        if self.eat_punct(b',') {
            if self.eat_punct(b'#') {
                disp = self.signed()?;
            } else {
                let ix = match self.ident().and_then(aarch64::register) {
                    Some(r) => r,
                    None => return Err(self.err("expected an index register or `#`")),
                };
                let mut ext = Extend::Lsl;
                let mut amount = 0u8;
                if self.eat_punct(b',') {
                    let w = self.ident().ok_or_else(|| self.err("expected an extend"))?;
                    ext = match qualifier(w) {
                        Some(Qual::Extend(e)) => e,
                        Some(Qual::Shift(Shift::Lsl)) => Extend::Lsl,
                        _ => return Err(self.err("an index takes lsl, uxtw, sxtw or sxtx")),
                    };
                    if self.eat_punct(b'#') {
                        let v = self.signed()?;
                        amount = u8::try_from(v).map_err(|_| AsmError::Range {
                            what: "index shift",
                            value: v,
                            low: 0,
                            high: 4,
                        })?;
                        // `lsl #0` is written out only where the scale bit is
                        // set, and the decoder spells that LslZero.
                        if ext == Extend::Lsl && amount == 0 {
                            ext = Extend::LslZero;
                        }
                    }
                }
                index = Some((ix, ext, amount));
            }
        }
        self.expect_punct(b']')?;
        let mut mode = AddrMode::Offset;
        if self.eat_punct(b'!') {
            mode = AddrMode::PreIndex;
        } else if self.peek() == Some(Tok::Punct(b',')) && self.peek_at(1) == Some(Tok::Punct(b'#'))
        {
            // `[sp], #16`: the only thing that follows a closed bracket.
            self.i += 2;
            disp = self.signed()?;
            mode = AddrMode::PostIndex;
        }
        Ok(Operand::Mem(Mem {
            seg: None,
            base: Some(base),
            index,
            disp,
            mode,
            // The transfer size comes from the mnemonic, which the encoder
            // knows and the text does not.
            size: 0,
        }))
    }

    // ---------------------------------------------------------------- x86

    fn x86_operand(&mut self, mnemonic: &'static str) -> Result<Operand, AsmError> {
        // A size keyword, then `ptr`, then optionally a segment override.
        let mut size = 0u64;
        if let Some(Tok::Ident(w)) = self.peek()
            && let Some(n) = size_keyword(w)
            && self.peek_at(1) == Some(Tok::Ident("ptr"))
        {
            self.i += 2;
            size = n;
        }
        let mut seg = None;
        if let Some(Tok::Ident(w)) = self.peek()
            && self.peek_at(1) == Some(Tok::Punct(b':'))
            && let Some(s) = x86::segment(w)
        {
            self.i += 2;
            seg = Some(s);
        }
        if self.peek() == Some(Tok::Punct(b'[')) {
            return self.x86_mem(seg, size);
        }
        if size != 0 || seg.is_some() {
            return Err(self.err("a size or segment prefix needs a memory operand"));
        }
        match self.peek() {
            Some(Tok::Ident(w)) => {
                self.i += 1;
                if let Some(r) = x86::register(w) {
                    return Ok(Operand::Reg(r));
                }
                if let Some(n) = x86::name(w) {
                    return Ok(Operand::Name(n));
                }
                Err(AsmError::UnknownRegister(w.to_string()))
            }
            Some(Tok::Num(_)) | Some(Tok::Punct(b'-')) | Some(Tok::Punct(b'+')) => {
                let v = self.signed()?;
                let _ = mnemonic;
                Ok(Operand::Imm(v))
            }
            _ => Err(self.err("expected an operand")),
        }
    }

    fn x86_mem(&mut self, seg: Option<Reg>, size: u64) -> Result<Operand, AsmError> {
        self.expect_punct(b'[')?;
        let mut base: Option<Reg> = None;
        let mut index: Option<(Reg, Extend, u8)> = None;
        let mut disp: i64 = 0;
        let mut sign = 1i64;
        let mut first = true;
        loop {
            if self.peek() == Some(Tok::Punct(b']')) {
                break;
            }
            if !first {
                match self.bump() {
                    Some(Tok::Punct(b'+')) => sign = 1,
                    Some(Tok::Punct(b'-')) => sign = -1,
                    _ => return Err(self.err("expected `+`, `-` or `]`")),
                }
            }
            first = false;
            match self.peek() {
                Some(Tok::Ident(w)) => {
                    self.i += 1;
                    let r = x86::register(w).ok_or(AsmError::UnknownRegister(w.to_string()))?;
                    let scale = if self.eat_punct(b'*') {
                        let v = self.signed()?;
                        scale_shift(v).ok_or(AsmError::Range {
                            what: "index scale",
                            value: v,
                            low: 1,
                            high: 8,
                        })?
                    } else {
                        u8::MAX
                    };
                    if scale != u8::MAX || base.is_some() {
                        if index.is_some() {
                            return Err(self.err("a memory operand has one index register"));
                        }
                        index = Some((r, Extend::Lsl, if scale == u8::MAX { 0 } else { scale }));
                    } else {
                        base = Some(r);
                    }
                }
                Some(Tok::Num(v)) => {
                    self.i += 1;
                    // `4*rcx` writes the scale first, which is how the
                    // printer spells it.
                    if self.eat_punct(b'*') {
                        let shift = scale_shift(v as i64).ok_or(AsmError::Range {
                            what: "index scale",
                            value: v as i64,
                            low: 1,
                            high: 8,
                        })?;
                        let w = self
                            .ident()
                            .ok_or_else(|| self.err("expected a register"))?;
                        let r = x86::register(w).ok_or(AsmError::UnknownRegister(w.to_string()))?;
                        if index.is_some() {
                            return Err(self.err("a memory operand has one index register"));
                        }
                        index = Some((r, Extend::Lsl, shift));
                    } else {
                        disp = disp.wrapping_add(sign.wrapping_mul(v as i64));
                    }
                }
                _ => return Err(self.err("expected a register or a number")),
            }
        }
        self.expect_punct(b']')?;
        Ok(Operand::Mem(Mem {
            seg,
            base,
            index,
            disp,
            mode: AddrMode::Offset,
            size,
        }))
    }
}

/// A trailing register qualifier.
enum Qual {
    Shift(Shift),
    Extend(Extend),
}

fn qualifier(w: &str) -> Option<Qual> {
    Some(match w {
        "lsl" => Qual::Shift(Shift::Lsl),
        "lsr" => Qual::Shift(Shift::Lsr),
        "asr" => Qual::Shift(Shift::Asr),
        "ror" => Qual::Shift(Shift::Ror),
        "msl" => Qual::Shift(Shift::Msl),
        "uxtb" => Qual::Extend(Extend::Uxtb),
        "uxth" => Qual::Extend(Extend::Uxth),
        "uxtw" => Qual::Extend(Extend::Uxtw),
        "uxtx" => Qual::Extend(Extend::Uxtx),
        "sxtb" => Qual::Extend(Extend::Sxtb),
        "sxth" => Qual::Extend(Extend::Sxth),
        "sxtw" => Qual::Extend(Extend::Sxtw),
        "sxtx" => Qual::Extend(Extend::Sxtx),
        _ => return None,
    })
}

fn size_keyword(w: &str) -> Option<u64> {
    Some(match w {
        "byte" => 1,
        "word" => 2,
        "dword" => 4,
        "qword" => 8,
        "tbyte" => 10,
        "xmmword" => 16,
        _ => return None,
    })
}

fn scale_shift(v: i64) -> Option<u8> {
    Some(match v {
        1 => 0,
        2 => 1,
        4 => 2,
        8 => 3,
        _ => return None,
    })
}

/// Turn the immediate a direct branch carries into the address it is.
///
/// The printers emit an absolute target for these, and analysis expects
/// [`Operand::Addr`], so a parsed instruction has to carry the same shape.
fn retarget(mnemonic: &str, ops: &mut [Operand]) {
    let branch = matches!(
        mnemonic,
        "b" | "bl" | "cbz" | "cbnz" | "tbz" | "tbnz" | "adr" | "adrp"
    ) || mnemonic.starts_with("b.")
        || matches!(mnemonic, "jmp" | "call")
        || (mnemonic.starts_with('j') && mnemonic.len() >= 2)
        || matches!(mnemonic, "loop" | "loope" | "loopne");
    if !branch {
        return;
    }
    if let Some(last) = ops.last_mut()
        && let Operand::Imm(v) = *last
    {
        *last = Operand::Addr(Addr(v as u64));
    }
}
