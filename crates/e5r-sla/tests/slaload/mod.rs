//! The other direction: a compiled `.sla` back into the model `e5r-sleigh`
//! decodes from.
//!
//! This exists to make the writer's gate a decode rather than a comparison.
//! `e5r-sleigh` parses a `.slaspec` into a [`sl::Spec`] and its engine decodes
//! AArch64, x86-64 and RISC-V with zero disagreements against objdump. If the
//! same specification, compiled by us and read back through this, decodes the
//! same corpus to the same text, then everything a decoder needs survived the
//! round trip. That is a much stronger statement than "our reader likes what
//! our writer wrote".
//!
//! # What cannot survive, and why the gate reports it rather than hiding it
//!
//! The compiled format keeps a pattern as mask and value bits. Three things in
//! the front end's model have no representation in it:
//!
//! * a **residual** constraint, one that is not a bit test: `r1 = r2`, `f < 3`.
//! * an **approximate** reduction, where the mask is only a filter and the
//!   real pattern has to be re-evaluated. That is x86's ModR/M and every
//!   `...` that right justifies a sub-pattern.
//! * **per alternative operand offsets**. The file carries one offset per
//!   operand; the front end carries one per alternative.
//!
//! A fourth is not a pattern at all: a field's print base. `hex` and `dec`
//! compile to identical trees, so everything read back prints in hex.
//!
//! A language that needs any of them decodes from the file as well as the
//! file allows, which is not always as well as from the source. The gate
//! counts those languages rather than excluding them quietly.
//!
//! Everything else is recovered exactly: spaces, registers, tokens and their
//! fields, attachments, context fields, every constructor's display, operands,
//! patterns and disassembly actions.

#![allow(dead_code)]

use std::collections::HashMap;

use e5r_sla::model as sla;
use e5r_sleigh::model as sl;

/// A specification recovered from a compiled file, and what could not be.
pub struct Loaded {
    pub spec: sl::Spec,
    /// One line per thing that was approximated, deduplicated.
    pub notes: Vec<String>,
}

/// Rebuild a decodable specification from a compiled program.
#[must_use]
pub fn load(p: &sla::Program) -> Loaded {
    Load::new(p).run()
}

/// A token field as the file spells it. Two fields with the same key are the
/// same field, which is what lets an operand's inline copy and a family
/// symbol's copy share one entry.
#[derive(PartialEq, Eq, Hash, Clone, Copy)]
struct FieldKey {
    big_endian: bool,
    signed: bool,
    start_bit: u64,
    end_bit: u64,
    start_byte: u64,
    end_byte: u64,
    shift: u64,
}

impl FieldKey {
    fn of(t: &sla::TokenField) -> FieldKey {
        FieldKey {
            big_endian: t.big_endian,
            signed: t.signed,
            start_bit: t.start_bit,
            end_bit: t.end_bit,
            start_byte: t.start_byte,
            end_byte: t.end_byte,
            shift: t.shift,
        }
    }

    /// How wide the token this field is cut from must be.
    ///
    /// A big-endian token numbers its bytes from the far end, so the width is
    /// exact: `start_byte = size - 1 - end_bit / 8`. A little-endian token
    /// does not say, and only a lower bound is recoverable here; an operand
    /// that uses the field carries the true width in attribute 18, and
    /// [`Load::family_field`] uses it.
    fn token_size(&self) -> u32 {
        if self.big_endian {
            (self.start_byte + 1 + self.end_bit / 8) as u32
        } else {
            (self.end_byte + 1) as u32
        }
    }
}

struct Load<'a> {
    p: &'a sla::Program,
    spec: sl::Spec,
    notes: Vec<String>,
    varnode_of: HashMap<u32, sl::VarnodeId>,
    /// A family symbol's own field, per token width it is used at.
    ///
    /// The width has to be part of the key. A compressed RISC-V instruction
    /// and a full one cut the same bits out of tokens of different widths, and
    /// the width is what says how many bytes the operand consumes, so one
    /// field for both makes every compressed instruction four bytes long.
    field_of: HashMap<(u32, u32), sl::FieldId>,
    /// The body a family symbol carries, so its field can be made on demand at
    /// whatever width the operand using it says.
    family: HashMap<u32, (String, sla::TokenField, sl::Attach)>,
    context_of: HashMap<u32, sl::ContextFieldId>,
    table_of: HashMap<u32, sl::TableId>,
    /// Anonymous inline fields only. A family symbol always gets a field of
    /// its own: two symbols can cut the same bits and attach different
    /// register lists to them, which is how every architecture spells its
    /// floating point registers, and merging them swaps `s9` for `fs9`.
    anon_fields: HashMap<(FieldKey, u32), sl::FieldId>,
    anon_context: HashMap<(u64, u64), sl::ContextFieldId>,
}

impl<'a> Load<'a> {
    fn new(p: &'a sla::Program) -> Load<'a> {
        Load {
            p,
            spec: sl::Spec {
                endian: if p.big_endian {
                    sl::Endian::Big
                } else {
                    sl::Endian::Little
                },
                alignment: p.alignment.max(1) as u32,
                spaces: Vec::new(),
                default_space: None,
                varnodes: Vec::new(),
                tokens: Vec::new(),
                fields: Vec::new(),
                context_fields: Vec::new(),
                context_register: None,
                bitranges: Vec::new(),
                pcodeops: Vec::new(),
                macros: Vec::new(),
                tables: Vec::new(),
                constructors: Vec::new(),
                symbols: HashMap::new(),
                warnings: Vec::new(),
            },
            notes: Vec::new(),
            varnode_of: HashMap::new(),
            field_of: HashMap::new(),
            family: HashMap::new(),
            context_of: HashMap::new(),
            table_of: HashMap::new(),
            anon_fields: HashMap::new(),
            anon_context: HashMap::new(),
        }
    }

    fn note(&mut self, s: impl Into<String>) {
        let s = s.into();
        if !self.notes.contains(&s) {
            self.notes.push(s);
        }
    }

    fn run(mut self) -> Loaded {
        self.spaces();
        self.varnodes();
        self.families();
        self.tables();
        self.constructors();
        self.name_symbols();
        Loaded {
            spec: self.spec,
            notes: self.notes,
        }
    }

    /// Space indices are kept as they are, so `SpaceId(i)` is the file's own
    /// index. Slot 0 is the constant space, which the file never lists because
    /// it is the same in every language.
    fn spaces(&mut self) {
        let top = self.p.spaces.iter().map(|s| s.index).max().unwrap_or(0);
        self.spec.spaces = (0..=top)
            .map(|_| sl::Space {
                name: String::new(),
                kind: sl::SpaceKind::Ram,
                size: 0,
                wordsize: 1,
                default: false,
            })
            .collect();
        self.spec.spaces[0] = sl::Space {
            name: "const".into(),
            kind: sl::SpaceKind::Constant,
            size: 8,
            wordsize: 1,
            default: false,
        };
        for s in &self.p.spaces {
            let default = self.p.default_space.as_deref() == Some(s.name.as_str());
            self.spec.spaces[s.index as usize] = sl::Space {
                name: s.name.clone(),
                kind: match s.kind {
                    sla::SpaceKind::Unique => sl::SpaceKind::Unique,
                    // The file says whether a space is physical and how long a
                    // read from it takes, not whether it holds registers. A
                    // decoder does not care which it is.
                    _ => sl::SpaceKind::Ram,
                },
                size: s.size as u32,
                wordsize: s.word_size.max(1) as u32,
                default,
            };
            if default {
                self.spec.default_space = Some(sl::SpaceId(s.index));
            }
        }
    }

    fn varnodes(&mut self) {
        for s in &self.p.symbols {
            let sla::SymbolBody::Varnode {
                space,
                offset,
                size,
            } = &s.body
            else {
                continue;
            };
            let id = sl::VarnodeId(self.spec.varnodes.len() as u32);
            self.spec.varnodes.push(sl::Varnode {
                name: s.name.clone().unwrap_or_default(),
                space: sl::SpaceId(*space),
                offset: *offset,
                size: *size as u32,
            });
            self.varnode_of.insert(s.id, id);
        }
    }

    /// The token a field is cut from, interned by width and byte order.
    fn token(&mut self, k: FieldKey, size: u32) -> sl::TokenId {
        let endian = if k.big_endian {
            sl::Endian::Big
        } else {
            sl::Endian::Little
        };
        for (i, t) in self.spec.tokens.iter().enumerate() {
            if t.size == size && t.endian == endian {
                return sl::TokenId(i as u32);
            }
        }
        let id = sl::TokenId(self.spec.tokens.len() as u32);
        self.spec.tokens.push(sl::TokenDef {
            name: format!("token{}", self.spec.tokens.len()),
            size,
            endian,
        });
        id
    }

    /// A field of its own, named by the family symbol that owns it.
    fn new_field(
        &mut self,
        t: &sla::TokenField,
        name: &str,
        attach: sl::Attach,
        width: u32,
    ) -> sl::FieldId {
        let k = FieldKey::of(t);
        let token = self.token(k, width.max(k.token_size()));
        let id = sl::FieldId(self.spec.fields.len() as u32);
        self.spec.fields.push(sl::Field {
            name: if name.is_empty() {
                format!("${}", id.index())
            } else {
                name.to_owned()
            },
            token,
            low: t.start_bit as u32,
            high: t.end_bit as u32,
            signed: t.signed,
            // The compiled form does not record how a field prints: `hex` and
            // `dec` compile to identical trees. Hex is SLEIGH's own default
            // and the only thing a file leaves a reader able to do.
            base: sl::NumberBase::Hex,
            attach,
        });
        id
    }

    /// An operand that writes its bits out inline rather than naming a family
    /// symbol. These carry no attachment, so one entry per distinct bit range
    /// is enough and keeps the field table small.
    fn anon_field(&mut self, t: &sla::TokenField, width: u32) -> sl::FieldId {
        let k = FieldKey::of(t);
        let width = width.max(k.token_size());
        if let Some(id) = self.anon_fields.get(&(k, width)) {
            return *id;
        }
        let id = self.new_field(t, "", sl::Attach::None, width);
        self.anon_fields.insert((k, width), id);
        id
    }

    /// The field a family symbol stands for, at the width the operand naming
    /// it says its token is.
    fn family_field(&mut self, sym: u32, width: u32) -> Option<sl::FieldId> {
        let (name, t, attach) = self.family.get(&sym)?.clone();
        let width = width.max(FieldKey::of(&t).token_size());
        if let Some(id) = self.field_of.get(&(sym, width)) {
            return Some(*id);
        }
        let id = self.new_field(&t, &name, attach, width);
        self.field_of.insert((sym, width), id);
        Some(id)
    }

    fn new_context_field(
        &mut self,
        f: &sla::ContextField,
        name: &str,
        register: Option<sl::VarnodeId>,
        flow: bool,
        attach: sl::Attach,
    ) -> sl::ContextFieldId {
        let id = sl::ContextFieldId(self.spec.context_fields.len() as u32);
        self.spec.context_fields.push(sl::ContextField {
            name: name.to_owned(),
            register: register
                .or(self.spec.context_register)
                .unwrap_or(sl::VarnodeId(0)),
            low: f.start_bit as u32,
            high: f.end_bit as u32,
            signed: f.signed,
            base: sl::NumberBase::Hex,
            noflow: !flow,
            attach,
        });
        id
    }

    /// A context field written out inline, with no symbol naming it.
    fn anon_context_field(&mut self, f: &sla::ContextField) -> sl::ContextFieldId {
        let k = (f.start_bit, f.end_bit);
        if let Some(id) = self.anon_context.get(&k) {
            return *id;
        }
        let id = self.new_context_field(f, "", None, true, sl::Attach::None);
        self.anon_context.insert(k, id);
        id
    }

    /// Value, name, valuemap, `attach variables` and context symbols: the
    /// things an operand names rather than carrying inline.
    fn families(&mut self) {
        // The context register first, so a context field can name it.
        for s in &self.p.symbols {
            if let sla::SymbolBody::Context { varnode, .. } = &s.body {
                if let Some(v) = self.varnode_of.get(varnode) {
                    self.spec.context_register = Some(*v);
                    break;
                }
            }
        }
        for i in 0..self.p.symbols.len() {
            let s = &self.p.symbols[i];
            let id = s.id;
            let name = s.name.clone().unwrap_or_default();
            let attach = self.attach_of(&s.body);
            match &s.body {
                sla::SymbolBody::Context {
                    varnode,
                    flow,
                    field: Some(f),
                    ..
                } => {
                    let reg = self.varnode_of.get(varnode).copied();
                    let f = f.clone();
                    let flow = *flow;
                    let cf = self.new_context_field(&f, &name, reg, flow, sl::Attach::None);
                    self.context_of.insert(id, cf);
                }
                body @ (sla::SymbolBody::Value { .. }
                | sla::SymbolBody::ValueMap { .. }
                | sla::SymbolBody::Name { .. }
                | sla::SymbolBody::VarnodeList { .. }) => match family_field(body) {
                    Some(sla::FieldDef::Token(t)) => {
                        self.family.insert(id, (name.clone(), t.clone(), attach));
                    }
                    // A family symbol over the context register: `attach
                    // variables` applied to a context field replaces the
                    // context symbol outright, which the reference compiler
                    // confirms by refusing to use such a name as a context
                    // lvalue.
                    Some(sla::FieldDef::Context(c)) => {
                        let c = c.clone();
                        let cf = self.new_context_field(&c, &name, None, true, attach);
                        self.context_of.insert(id, cf);
                    }
                    None => {}
                },
                _ => {}
            }
        }
    }

    fn attach_of(&self, body: &sla::SymbolBody) -> sl::Attach {
        match body {
            sla::SymbolBody::VarnodeList { entries, .. } => sl::Attach::Variables(
                entries
                    .iter()
                    .map(|e| e.and_then(|v| self.varnode_of.get(&v).copied()))
                    .collect(),
            ),
            sla::SymbolBody::Name { names, .. } => sl::Attach::Names(names.clone()),
            sla::SymbolBody::ValueMap { values, .. } => {
                sl::Attach::Values(values.iter().map(|v| Some(*v as i64)).collect())
            }
            _ => sl::Attach::None,
        }
    }

    /// Tables, with the file's root subtable at [`sl::Spec::root`].
    fn tables(&mut self) {
        let mut order: Vec<u32> = Vec::new();
        if self.p.symbols.iter().any(|s| s.id == 0) {
            order.push(0);
        }
        for s in &self.p.symbols {
            if matches!(s.body, sla::SymbolBody::Subtable { .. }) && s.id != 0 {
                order.push(s.id);
            }
        }
        for id in order {
            let t = sl::TableId(self.spec.tables.len() as u32);
            let name = self
                .p
                .symbol(id)
                .and_then(|s| s.name.clone())
                .unwrap_or_default();
            self.spec.tables.push(sl::Table {
                name,
                constructors: Vec::new(),
                min_length: 0,
                max_length: 0,
            });
            self.table_of.insert(id, t);
        }
    }

    fn constructors(&mut self) {
        let ids: Vec<u32> = self.table_of.keys().copied().collect();
        let mut by_table: Vec<(sl::TableId, u32)> = ids
            .iter()
            .map(|id| (self.table_of[id], *id))
            .collect::<Vec<_>>();
        by_table.sort_by_key(|(t, _)| t.index());

        for (tid, sym) in by_table {
            let Some(symbol) = self.p.symbol(sym) else {
                continue;
            };
            let sla::SymbolBody::Subtable {
                constructors,
                decision,
            } = &symbol.body
            else {
                continue;
            };
            // One decision tree covers the whole table; a constructor's
            // alternatives are the pairs that name it.
            let mut alts: Vec<Vec<sla::Pattern>> = vec![Vec::new(); constructors.len()];
            if let Some(d) = decision {
                collect_pairs(d, &mut alts);
            }
            let (mut min, mut max) = (usize::MAX, 0usize);
            let mut list = Vec::new();
            for (k, c) in constructors.iter().enumerate() {
                let cid = sl::ConstructorId(self.spec.constructors.len() as u32);
                let built = self.constructor(tid, c, &alts[k]);
                min = min.min(built.resolved.min_length());
                max = max.max(
                    built
                        .resolved
                        .alternatives
                        .iter()
                        .map(|a| a.length)
                        .max()
                        .unwrap_or(0),
                );
                self.spec.constructors.push(built);
                list.push(cid);
            }
            let t = &mut self.spec.tables[tid.index()];
            t.constructors = list;
            t.min_length = if min == usize::MAX { 0 } else { min };
            t.max_length = max;
        }
    }

    fn constructor(
        &mut self,
        table: sl::TableId,
        c: &sla::Constructor,
        pats: &[sla::Pattern],
    ) -> sl::Constructor {
        let operands: Vec<sl::Operand> = c
            .operands
            .iter()
            .map(|id| self.operand(*id))
            .collect::<Vec<_>>();
        let offsets: Vec<sl::Offset> = operands.iter().map(|o| o.offset).collect();
        let length = c.length as usize;

        let mut alternatives: Vec<sl::PatternAlt> = pats
            .iter()
            .map(|p| sl::PatternAlt {
                instr: mask_value(&p.instruction),
                context: mask_value(&p.context),
                length,
                residual: Vec::new(),
                offsets: offsets.clone(),
            })
            .collect();
        if alternatives.is_empty() {
            alternatives.push(sl::PatternAlt {
                instr: sl::MaskValue::default(),
                context: sl::MaskValue::default(),
                length,
                residual: Vec::new(),
                offsets,
            });
        }

        let display = sl::Display {
            // The file writes the mnemonic as the first print pieces, so
            // rendering puts it back without a separate slot.
            mnemonic: None,
            pieces: c
                .print
                .iter()
                .map(|p| match p {
                    sla::PrintPiece::Literal(s) => sl::DisplayPiece::Literal(s.clone()),
                    sla::PrintPiece::Operand(i) => sl::DisplayPiece::Operand(*i as u16),
                })
                .collect(),
        };

        let disasm = self.disasm(c);
        let file = self
            .p
            .source_files
            .iter()
            .find(|f| f.index == c.source)
            .map(|f| f.name.clone())
            .unwrap_or_default();

        sl::Constructor {
            table,
            display,
            order: (0..operands.len() as u16).collect(),
            operands,
            locals: Vec::new(),
            labels: Vec::new(),
            // Never evaluated: nothing here is approximate and no alternative
            // carries a residual, because the file cannot say so.
            pattern: sl::PatternExpr::Epsilon,
            resolved: sl::ResolvedPattern {
                alternatives,
                approximation: None,
            },
            disasm,
            // The compiler does not write p-code yet, so every constructor
            // read back looks implemented with an empty body rather than
            // `unimpl`. Nothing in a decode depends on it.
            body: Some(Vec::new()),
            location: e5r_sleigh::Location::new(file, c.line as u32),
        }
    }

    fn operand(&mut self, id: u32) -> sl::Operand {
        let Some(s) = self.p.symbol(id) else {
            return sl::Operand {
                name: String::new(),
                source: sl::OperandSource::Unbound,
                offset: sl::Offset::absolute(0),
                invisible: false,
            };
        };
        let name = s.name.clone().unwrap_or_default();
        let sla::SymbolBody::Operand {
            offset,
            sub_symbol,
            base,
            min_length,
            expr,
            ..
        } = &s.body
        else {
            return sl::Operand {
                name,
                source: sl::OperandSource::Unbound,
                offset: sl::Offset::absolute(0),
                invisible: false,
            };
        };
        let place = sl::Offset {
            base: if *base < 0 { None } else { Some(*base as u16) },
            delta: *offset as usize,
        };
        let width = *min_length as u32;
        let source = match sub_symbol {
            Some(sub) => {
                if let Some(t) = self.table_of.get(sub) {
                    sl::OperandSource::Table(*t)
                } else if let Some(f) = self.family_field(*sub, width) {
                    sl::OperandSource::Field(f)
                } else if let Some(c) = self.context_of.get(sub) {
                    sl::OperandSource::Context(*c)
                } else if let Some(v) = self.varnode_of.get(sub) {
                    sl::OperandSource::Varnode(*v)
                } else {
                    sl::OperandSource::Unbound
                }
            }
            None => {
                // No family symbol: either the bits are written out inline, or
                // the operand is computed by a disassembly action.
                match expr.get(1) {
                    Some(sla::Expr::TokenField(t)) => {
                        let t = t.clone();
                        sl::OperandSource::Field(self.anon_field(&t, width))
                    }
                    Some(sla::Expr::Context(c)) => {
                        let c = c.clone();
                        sl::OperandSource::Context(self.anon_context_field(&c))
                    }
                    Some(_) => sl::OperandSource::Computed,
                    None => sl::OperandSource::Unbound,
                }
            }
        };
        sl::Operand {
            name,
            source,
            offset: place,
            invisible: false,
        }
    }

    /// The disassembly action section, rebuilt from the two places the file
    /// keeps it: the context records on the constructor and the expression in
    /// each computed operand's own body.
    ///
    /// The decoder runs context assignments during the descent and everything
    /// else afterwards, so what has to be preserved is the order within each
    /// group, not between them.
    fn disasm(&mut self, c: &sla::Constructor) -> Vec<sl::DisasmStmt> {
        let mut out = Vec::new();
        for op in &c.context_ops {
            if let sla::ContextOp::Set {
                word, mask, value, ..
            } = op
            {
                let Some(cf) = self.context_by_bits(*word, *mask) else {
                    self.note("a context assignment names bits no context field covers");
                    continue;
                };
                let Some(v) = value.first() else { continue };
                out.push(sl::DisasmStmt::Assign {
                    target: sl::DisasmTarget::Context(cf),
                    value: self.expr(v),
                });
            }
        }
        for (i, id) in c.operands.iter().enumerate() {
            let Some(s) = self.p.symbol(*id) else {
                continue;
            };
            let sla::SymbolBody::Operand { expr, .. } = &s.body else {
                continue;
            };
            for e in expr.iter().skip(1) {
                if matches!(e, sla::Expr::TokenField(_) | sla::Expr::Context(_)) {
                    continue;
                }
                let e = e.clone();
                let value = self.expr(&e);
                out.push(sl::DisasmStmt::Assign {
                    target: sl::DisasmTarget::Operand(i as u16),
                    value,
                });
            }
        }
        for op in &c.context_ops {
            if let sla::ContextOp::Commit {
                symbol, word, mask, ..
            } = op
            {
                let Some(cf) = self.context_by_bits(*word, *mask) else {
                    self.note("a globalset names bits no context field covers");
                    continue;
                };
                out.push(sl::DisasmStmt::GlobalSet {
                    address: self.globalset_address(*symbol, c),
                    context: cf,
                });
            }
        }
        out
    }

    /// Which context field a record's `(word, mask)` names.
    fn context_by_bits(&self, word: u64, mask: u64) -> Option<sl::ContextFieldId> {
        for (i, f) in self.spec.context_fields.iter().enumerate() {
            if u64::from(f.low / 32) != word {
                continue;
            }
            let high = f.high.min(f.low / 32 * 32 + 31);
            let shift = 31 - high % 32;
            let width = high - f.low + 1;
            let m = if width >= 64 {
                u64::MAX
            } else {
                ((1u64 << width) - 1) << shift
            };
            if m == mask {
                return Some(sl::ContextFieldId(i as u32));
            }
        }
        None
    }

    /// The address a `globalset` publishes at, which the file writes as a
    /// symbol id: one of the three built-in addresses, or an operand.
    fn globalset_address(&self, symbol: u32, c: &sla::Constructor) -> sl::DisasmExpr {
        if let Some(i) = c.operands.iter().position(|o| *o == symbol) {
            return sl::DisasmExpr::Symbol(sl::SymbolRef::Operand(i as u16));
        }
        sl::DisasmExpr::Symbol(sl::SymbolRef::Builtin(match symbol {
            2 => sl::Builtin::InstNext,
            3 => sl::Builtin::InstNext2,
            _ => sl::Builtin::InstStart,
        }))
    }

    fn expr(&mut self, e: &sla::Expr) -> sl::DisasmExpr {
        match e {
            sla::Expr::Constant(v) => sl::DisasmExpr::Num(*v as i64),
            sla::Expr::InstStart => {
                sl::DisasmExpr::Symbol(sl::SymbolRef::Builtin(sl::Builtin::InstStart))
            }
            sla::Expr::InstNext => {
                sl::DisasmExpr::Symbol(sl::SymbolRef::Builtin(sl::Builtin::InstNext))
            }
            sla::Expr::InstNext2 => {
                sl::DisasmExpr::Symbol(sl::SymbolRef::Builtin(sl::Builtin::InstNext2))
            }
            sla::Expr::OperandValue { index, .. } => {
                sl::DisasmExpr::Symbol(sl::SymbolRef::Operand(*index as u16))
            }
            sla::Expr::TokenField(t) => {
                let t = t.clone();
                let f = self.anon_field(&t, 0);
                sl::DisasmExpr::Symbol(sl::SymbolRef::Field(f))
            }
            sla::Expr::Context(cf) => {
                let cf = cf.clone();
                let id = self.anon_context_field(&cf);
                sl::DisasmExpr::Symbol(sl::SymbolRef::Context(id))
            }
            sla::Expr::Op { op, operands } => {
                let mut args: Vec<sl::DisasmExpr> = operands.iter().map(|o| self.expr(o)).collect();
                let unary = |k| match k {
                    sla::PatternOp::Minus => Some(sl::DisasmUnOp::Negate),
                    sla::PatternOp::Not => Some(sl::DisasmUnOp::Not),
                    _ => None,
                };
                if let Some(u) = unary(*op) {
                    if args.len() == 1 {
                        return sl::DisasmExpr::Unary(u, Box::new(args.remove(0)));
                    }
                }
                let b = match op {
                    sla::PatternOp::Plus => sl::DisasmBinOp::Add,
                    sla::PatternOp::Sub | sla::PatternOp::Minus => sl::DisasmBinOp::Sub,
                    sla::PatternOp::Mult => sl::DisasmBinOp::Mul,
                    sla::PatternOp::Div => sl::DisasmBinOp::Div,
                    sla::PatternOp::LeftShift => sl::DisasmBinOp::Shl,
                    sla::PatternOp::RightShift => sl::DisasmBinOp::Shr,
                    sla::PatternOp::And | sla::PatternOp::Not => sl::DisasmBinOp::And,
                    sla::PatternOp::Or => sl::DisasmBinOp::Or,
                    sla::PatternOp::Xor => sl::DisasmBinOp::Xor,
                };
                if args.len() < 2 {
                    return args.pop().unwrap_or(sl::DisasmExpr::Num(0));
                }
                let rhs = args.remove(1);
                let lhs = args.remove(0);
                sl::DisasmExpr::Binary(b, Box::new(lhs), Box::new(rhs))
            }
            sla::Expr::Unknown { .. } => sl::DisasmExpr::Num(0),
        }
    }

    /// The global scope, which a caller uses to find a context field by name.
    fn name_symbols(&mut self) {
        for (i, f) in self.spec.context_fields.iter().enumerate() {
            if !f.name.is_empty() {
                self.spec.symbols.insert(
                    f.name.clone(),
                    sl::Symbol::Context(sl::ContextFieldId(i as u32)),
                );
            }
        }
        for (i, f) in self.spec.fields.iter().enumerate() {
            if !f.name.starts_with('$') {
                self.spec
                    .symbols
                    .insert(f.name.clone(), sl::Symbol::Field(sl::FieldId(i as u32)));
            }
        }
        for (i, v) in self.spec.varnodes.iter().enumerate() {
            self.spec
                .symbols
                .insert(v.name.clone(), sl::Symbol::Varnode(sl::VarnodeId(i as u32)));
        }
        for (i, t) in self.spec.tables.iter().enumerate() {
            self.spec
                .symbols
                .insert(t.name.clone(), sl::Symbol::Table(sl::TableId(i as u32)));
        }
    }
}

/// The field a family symbol reads its bits from, whichever kind it is.
fn family_field(body: &sla::SymbolBody) -> Option<&sla::FieldDef> {
    match body {
        sla::SymbolBody::Value { field }
        | sla::SymbolBody::ValueMap { field, .. }
        | sla::SymbolBody::Name { field, .. }
        | sla::SymbolBody::VarnodeList { field, .. } => field.as_ref(),
        _ => None,
    }
}

/// Every `(constructor, pattern)` pair in a decision tree, gathered by
/// constructor. Our own writer emits one flat node; the reference emits a tree
/// split on bits, and both mean the same set of pairs.
fn collect_pairs(d: &sla::Decision, out: &mut Vec<Vec<sla::Pattern>>) {
    for (ix, p) in &d.pairs {
        if let Some(slot) = out.get_mut(*ix as usize) {
            slot.push(p.clone());
        }
    }
    for c in &d.children {
        collect_pairs(c, out);
    }
}

/// A run of pattern blocks as one mask and value over bytes from the
/// instruction's own first byte.
fn mask_value(blocks: &[sla::PatternBlock]) -> sl::MaskValue {
    let mut mask: Vec<u8> = Vec::new();
    let mut value: Vec<u8> = Vec::new();
    for b in blocks {
        for (i, w) in b.words.iter().enumerate() {
            for j in 0..4usize {
                let at = b.offset as usize + i * 4 + j;
                // A block says how many bytes it covers; a word is always four
                // and the tail beyond `bytes` is padding.
                if at >= b.offset as usize + b.bytes as usize {
                    continue;
                }
                if mask.len() <= at {
                    mask.resize(at + 1, 0);
                    value.resize(at + 1, 0);
                }
                let shift = 24 - 8 * j;
                mask[at] |= ((w.mask >> shift) & 0xff) as u8;
                value[at] |= ((w.value >> shift) & 0xff) as u8;
            }
        }
    }
    sl::MaskValue { mask, value }
}
