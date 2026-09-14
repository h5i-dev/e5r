//! The SLEIGH compiler: an `r12e-sleigh` specification to the model
//! `r12e-sla` writes, and from there to `.sla` bytes.
//!
//! # Why this is in the test harness
//!
//! It should be a module of `r12e-sleigh`, next to the front end whose model
//! it consumes. It is not, because `r12e-sleigh`'s decode engine reads a
//! compiled `.sla` and will therefore depend on `r12e-sla`, and cargo refuses
//! a cycle between two normal dependencies. A cycle through a dev-dependency
//! is allowed, so the compiler sits here until it can move, which is a file
//! move and no change to the code.
//!
//! # What it compiles and what it does not
//!
//! Everything a decoder needs: the address spaces, the register table, the
//! token and context fields, the attachments, the symbol table, every
//! constructor with its display, its operands, its bit patterns, its
//! disassembly actions and its subtable's decision tree. A file it writes
//! decodes RISC-V and x86-64 identically to the specification it came from,
//! and AArch64 identically but for eight encodings in twenty thousand; see
//! `docs/sla-format.md`.
//!
//! Not the p-code. A `construct_tpl` needs two things this project has not
//! established by experiment: the rule the reference compiler uses to hand out
//! offsets in the unique space, and the opcode numbers of the template-only
//! operations that surround a local label. Guessing either would produce a
//! file that looks right and lifts wrong, which is the one failure mode this
//! project refuses. So a constructor is written with no `construct_tpl` at
//! all, which is how the reference compiler writes `unimpl`, and
//! [`Report::without_semantics`] counts how many that is rather than letting
//! it pass unsaid.
//!
//! # Where it differs from the reference compiler on purpose
//!
//! * **The decision tree.** The reference splits on a run of bits it picks per
//!   subtable. This writes one flat node whose pairs are tried in order. That
//!   is a correct decision tree and a slower one, and it is what
//!   `Decision { num_bits: 0 }` means in the format.
//! * **`define pcodeop` ids.** The reference numbers a user operation where
//!   the source declares it, which can be between two constructors. The front
//!   end does not record where a `pcodeop` was declared, so they are all
//!   numbered together after the context fields. Every other symbol is
//!   numbered exactly as the reference numbers it.
//!
//! # Where it differs and should not
//!
//! A pattern constraint that is not a bit test has no place in the format. A
//! `field = field` equality is enumerated into one alternative per value, the
//! way the reference does, but an inequality or a disjunction is not, and the
//! pattern written then matches more than the constructor should.
//! [`Report::approximate_patterns`] counts those.

#![allow(dead_code)]

use r12e_sla::model as sla;
use r12e_sleigh::model as sl;

/// What the compiler could not do, counted rather than hidden.
#[derive(Debug, Clone, Default)]
pub struct Report {
    pub constructors: usize,
    /// Constructors with a semantic body in the source that were written with
    /// no p-code template.
    pub without_semantics: usize,
    /// Disassembly action statements written: context assignments, computed
    /// operands and `globalset`s.
    pub context_sets: usize,
    pub computed_operands: usize,
    pub globalsets: usize,
    /// Tables no operand names, which the reference drops and so do we.
    pub dropped_tables: usize,
    /// Constructors whose pattern reduced only approximately, so the bit
    /// tests written are a filter and not the pattern.
    pub approximate_patterns: usize,
    /// Anything else worth saying, one line each, deduplicated.
    pub notes: Vec<String>,
}

impl Report {
    fn note(&mut self, s: impl Into<String>) {
        let s = s.into();
        if !self.notes.contains(&s) {
            self.notes.push(s);
        }
    }
}

/// Compile a parsed specification.
#[must_use]
pub fn compile(spec: &sl::Spec) -> (sla::Program, Report) {
    Compiler::new(spec).run()
}

/// Compile and write a whole `.sla` file image.
///
/// # Errors
/// Only if the model holds something the tag encoding cannot carry.
pub fn compile_to_bytes(spec: &sl::Spec) -> Result<(Vec<u8>, Report), r12e_sla::SlaError> {
    let (p, r) = compile(spec);
    let bytes = r12e_sla::emit::write(&p, r12e_sla::KNOWN_VERSION, r12e_sla::Level::Fixed)?;
    Ok((bytes, r))
}

/// The three space indices the compiled form reserves before any declared
/// space: the constant space is 0 and never appears in the table, `OTHER` is
/// 1 and `unique` is 2.
const SPACE_CONST: u32 = 0;
const SPACE_OTHER: u32 = 1;
const SPACE_UNIQUE: u32 = 2;
const FIRST_DECLARED_SPACE: u32 = 3;

struct Compiler<'a> {
    spec: &'a sl::Spec,
    report: Report,
    /// Model space index to compiled space index.
    space_ix: Vec<u32>,
    /// Symbol ids, by kind.
    varnode_id: Vec<u32>,
    field_id: Vec<u32>,
    context_id: Vec<u32>,
    userop_id: Vec<u32>,
    table_id: Vec<u32>,
    /// Whether a table is written at all. The reference compiler warns
    /// "Unreferenced table" and drops one no operand names, and dropping it
    /// takes its constructors and its symbol id with it.
    keep_table: Vec<bool>,
    /// `(table, constructor within table, operand)` to symbol id.
    operand_id: Vec<Vec<u32>>,
    /// Constructor index in `spec.constructors` to `(table symbol id, index
    /// within that table)`.
    ct_place: Vec<(u32, u64)>,
    source_files: Vec<String>,
    /// The token width, when every token in the specification has the same
    /// one. That is the only case where a field's byte offset inside the
    /// instruction is known here without redoing the front end's pattern
    /// arithmetic, and it is what lets a `field = field` constraint be
    /// expanded into bits.
    uniform_token: Option<u32>,
}

impl<'a> Compiler<'a> {
    fn new(spec: &'a sl::Spec) -> Self {
        Self {
            spec,
            report: Report::default(),
            space_ix: Vec::new(),
            varnode_id: Vec::new(),
            field_id: Vec::new(),
            context_id: Vec::new(),
            userop_id: Vec::new(),
            table_id: Vec::new(),
            keep_table: Vec::new(),
            operand_id: Vec::new(),
            ct_place: Vec::new(),
            source_files: Vec::new(),
            uniform_token: None,
        }
    }

    fn run(mut self) -> (sla::Program, Report) {
        let first = self.spec.tokens.first().map(|t| t.size);
        self.uniform_token = first.filter(|w| self.spec.tokens.iter().all(|t| t.size == *w));
        self.map_spaces();
        self.reachable_tables();
        self.assign_ids();
        self.collect_sources();

        let big_endian = self.spec.endian == sl::Endian::Big;
        let mut p = sla::Program::empty();
        p.version = Some(u64::from(r12e_sla::KNOWN_VERSION));
        p.big_endian = big_endian;
        p.alignment = u64::from(self.spec.alignment.max(1));
        // Nothing is allocated in the unique space while no p-code is written,
        // so the next free offset is still the base.
        p.unique_base = 0;

        for (i, name) in self.source_files.iter().enumerate() {
            p.source_files.push(sla::SourceFile {
                name: name.clone(),
                index: i as u64,
            });
        }

        p.default_space = self
            .spec
            .default_space
            .map(|id| self.spec.space(id).name.clone());
        p.spaces = self.spaces(big_endian);

        let (scopes, symbols) = self.symbols();
        p.declared_scopes = Some(scopes.len() as u64);
        p.declared_symbols = Some(symbols.len() as u64);
        p.scopes = scopes;
        p.symbols = symbols;

        p.reindex();
        (p, self.report)
    }

    /// The compiled form numbers spaces differently from the front end: it
    /// puts `OTHER` at 1 and `unique` at 2, and the front end has no `OTHER`
    /// at all. So the mapping is built rather than assumed.
    fn map_spaces(&mut self) {
        let mut next = FIRST_DECLARED_SPACE;
        self.space_ix = self
            .spec
            .spaces
            .iter()
            .map(|s| match s.kind {
                sl::SpaceKind::Constant => SPACE_CONST,
                sl::SpaceKind::Unique => SPACE_UNIQUE,
                _ => {
                    let ix = next;
                    next += 1;
                    ix
                }
            })
            .collect();
    }

    fn spaces(&self, big_endian: bool) -> Vec<sla::Space> {
        // `OTHER` and `unique` are the same in every one of the 137 shipped
        // files: eight bytes and four bytes, no delay, and only `unique` is
        // physical. They do not follow the specification's own spaces.
        let mut out = vec![
            sla::Space {
                kind: sla::SpaceKind::Other,
                name: "OTHER".into(),
                index: SPACE_OTHER,
                big_endian,
                delay: 0,
                size: 8,
                word_size: 1,
                physical: false,
            },
            sla::Space {
                kind: sla::SpaceKind::Unique,
                name: "unique".into(),
                index: SPACE_UNIQUE,
                big_endian,
                delay: 0,
                size: 4,
                word_size: 1,
                physical: true,
            },
        ];
        for (i, s) in self.spec.spaces.iter().enumerate() {
            if matches!(s.kind, sl::SpaceKind::Constant | sl::SpaceKind::Unique) {
                continue;
            }
            out.push(sla::Space {
                kind: sla::SpaceKind::Normal,
                name: s.name.clone(),
                index: self.space_ix[i],
                big_endian,
                // A memory space takes an instruction's worth of delay to
                // read; a register space does not.
                delay: u64::from(!matches!(s.kind, sl::SpaceKind::Register)),
                size: u64::from(s.size),
                word_size: u64::from(s.wordsize.max(1)),
                physical: true,
            });
        }
        out
    }

    /// Which tables the file gets. The root always, and any table an operand
    /// names.
    ///
    /// **Proved** against the reference: `ADDR8` in `6502.slaspec` is defined
    /// and never used, the reference warns "Unreferenced table" and its
    /// `.sla` has neither the table nor its constructor, and every symbol id
    /// after it shifts down by two. The test is not transitive, because the
    /// reference's warning is per table rather than a traversal, and nothing
    /// in the corpus distinguishes the two.
    fn reachable_tables(&mut self) {
        let mut keep = vec![false; self.spec.tables.len()];
        if !keep.is_empty() {
            keep[0] = true;
        }
        for c in &self.spec.constructors {
            for o in &c.operands {
                if let sl::OperandSource::Table(t) = o.source {
                    if let Some(k) = keep.get_mut(t.index()) {
                        *k = true;
                    }
                }
            }
        }
        self.report.dropped_tables = keep.iter().filter(|k| !**k).count();
        self.keep_table = keep;
    }

    fn kept(&self, t: usize) -> bool {
        self.keep_table.get(t).copied().unwrap_or(true)
    }

    fn assign_ids(&mut self) {
        let mut next = 4u32; // 0 root table, 1 inst_start, 2 inst_next, 3 inst_next2
        self.varnode_id = (0..self.spec.varnodes.len())
            .map(|_| {
                next += 1;
                next - 1
            })
            .collect();
        self.field_id = (0..self.spec.fields.len())
            .map(|_| {
                next += 1;
                next - 1
            })
            .collect();
        self.context_id = (0..self.spec.context_fields.len())
            .map(|_| {
                next += 1;
                next - 1
            })
            .collect();
        self.userop_id = (0..self.spec.pcodeops.len())
            .map(|_| {
                next += 1;
                next - 1
            })
            .collect();

        // Subtables and operands are numbered the way the reference numbers
        // them: in the order the source defines them. A subtable's id is
        // taken when its first constructor is parsed, and that constructor's
        // operands follow immediately. Getting this right is most of what
        // makes our symbol table the same shape as Ghidra's.
        const UNSET: u32 = u32::MAX;
        self.table_id = vec![UNSET; self.spec.tables.len()];
        if !self.table_id.is_empty() {
            self.table_id[0] = 0;
        }
        self.operand_id = vec![Vec::new(); self.spec.constructors.len()];
        for (i, c) in self.spec.constructors.iter().enumerate() {
            let t = c.table.index();
            if !self.kept(t) {
                continue;
            }
            if self.table_id[t] == UNSET {
                self.table_id[t] = next;
                next += 1;
            }
            self.operand_id[i] = c
                .operands
                .iter()
                .map(|_| {
                    next += 1;
                    next - 1
                })
                .collect();
        }
        // A table with no constructors still needs an id.
        for t in 0..self.table_id.len() {
            if self.table_id[t] == UNSET && self.kept(t) {
                self.table_id[t] = next;
                next += 1;
            }
        }

        self.ct_place = vec![(0, 0); self.spec.constructors.len()];
        for (t, table) in self.spec.tables.iter().enumerate() {
            if !self.kept(t) {
                continue;
            }
            for (k, cid) in table.constructors.iter().enumerate() {
                self.ct_place[cid.index()] = (self.table_id[t], k as u64);
            }
        }
    }

    /// The files that define a constructor, in first-use order, which is the
    /// order the `sourcefiles` list has them.
    fn collect_sources(&mut self) {
        for c in &self.spec.constructors {
            if !self.kept(c.table.index()) {
                continue;
            }
            // The reference writes the file's own name, not the path it was
            // found at, so a compiled language does not carry the build
            // machine's directory layout.
            let f = base_name(&c.location.file);
            if !self.source_files.contains(&f) {
                self.source_files.push(f);
            }
        }
        if self.source_files.is_empty() {
            self.source_files.push("<input>".into());
        }
    }

    fn source_index(&self, c: &sl::Constructor) -> u64 {
        let name = base_name(&c.location.file);
        self.source_files
            .iter()
            .position(|f| *f == name)
            .unwrap_or(0) as u64
    }

    fn symbols(&mut self) -> (Vec<sla::Scope>, Vec<sla::Symbol>) {
        let mut scopes = vec![sla::Scope { id: 0, parent: 0 }];
        // The root table's body carries every constructor of `instruction`,
        // so it is built first even though it is written in id order. The
        // three built-in symbols follow it at fixed ids.
        let mut syms: Vec<sla::Symbol> = vec![
            self.table_symbol(0),
            sla::Symbol {
                id: 1,
                name: Some("inst_start".into()),
                scope: Some(0),
                body: sla::SymbolBody::Start,
            },
            sla::Symbol {
                id: 2,
                name: Some("inst_next".into()),
                scope: Some(0),
                body: sla::SymbolBody::End,
            },
            sla::Symbol {
                id: 3,
                name: Some("inst_next2".into()),
                scope: Some(0),
                body: sla::SymbolBody::Next2,
            },
        ];

        for (i, v) in self.spec.varnodes.iter().enumerate() {
            syms.push(sla::Symbol {
                id: self.varnode_id[i],
                name: Some(v.name.clone()),
                scope: Some(0),
                body: sla::SymbolBody::Varnode {
                    space: self.space_ix[v.space.index()],
                    offset: v.offset,
                    size: u64::from(v.size),
                },
            });
        }

        for (i, f) in self.spec.fields.iter().enumerate() {
            let field = Some(sla::FieldDef::Token(self.token_field(f)));
            let body = match &f.attach {
                sl::Attach::None => sla::SymbolBody::Value { field },
                sl::Attach::Variables(v) => sla::SymbolBody::VarnodeList {
                    field,
                    entries: v
                        .iter()
                        .map(|e| e.map(|id| self.varnode_id[id.index()]))
                        .collect(),
                },
                sl::Attach::Names(n) => sla::SymbolBody::Name {
                    field,
                    names: n.clone(),
                },
                sl::Attach::Values(v) => sla::SymbolBody::ValueMap {
                    field,
                    values: v.iter().map(|e| i128::from(e.unwrap_or(0))).collect(),
                },
            };
            syms.push(sla::Symbol {
                id: self.field_id[i],
                name: Some(f.name.clone()),
                scope: Some(0),
                body,
            });
        }

        for (i, cf) in self.spec.context_fields.iter().enumerate() {
            // An `attach` over a context field replaces the context symbol
            // rather than decorating it. **Proved**: after `attach variables
            // [ cc ] [ ... ]` the reference compiler refuses `cc` as a context
            // lvalue and in a `globalset` call, saying it is now a
            // varnodelist_symbol. So the body written is the family body, with
            // the context field inline where a token field would otherwise be.
            let field = Some(sla::FieldDef::Context(context_field(cf)));
            let body = match &cf.attach {
                sl::Attach::None => sla::SymbolBody::Context {
                    varnode: self.varnode_id[cf.register.index()],
                    low: u64::from(cf.low),
                    high: u64::from(cf.high),
                    flow: !cf.noflow,
                    field: Some(context_field(cf)),
                },
                sl::Attach::Variables(v) => sla::SymbolBody::VarnodeList {
                    field,
                    entries: v
                        .iter()
                        .map(|e| e.map(|id| self.varnode_id[id.index()]))
                        .collect(),
                },
                sl::Attach::Names(n) => sla::SymbolBody::Name {
                    field,
                    names: n.clone(),
                },
                sl::Attach::Values(v) => sla::SymbolBody::ValueMap {
                    field,
                    values: v.iter().map(|e| i128::from(e.unwrap_or(0))).collect(),
                },
            };
            syms.push(sla::Symbol {
                id: self.context_id[i],
                name: Some(cf.name.clone()),
                scope: Some(0),
                body,
            });
        }

        for (i, op) in self.spec.pcodeops.iter().enumerate() {
            syms.push(sla::Symbol {
                id: self.userop_id[i],
                name: Some(op.name.clone()),
                scope: Some(0),
                body: sla::SymbolBody::UserOp { index: i as u64 },
            });
        }

        // Then the subtables and the operands, interleaved in source order,
        // each subtable just before the operands of its first constructor.
        let spec = self.spec;
        let mut written = vec![false; spec.tables.len()];
        let mut pending: Vec<usize> = Vec::new();
        if !written.is_empty() {
            written[0] = true;
        }
        for (i, c) in spec.constructors.iter().enumerate() {
            let t = c.table.index();
            if !self.kept(t) {
                continue;
            }
            if !written[t] {
                written[t] = true;
                syms.push(self.table_symbol(t));
            }
            if c.operands.is_empty() {
                continue;
            }
            let scope = scopes.len() as u32;
            scopes.push(sla::Scope {
                id: scope,
                parent: 0,
            });
            for (k, o) in c.operands.iter().enumerate() {
                syms.push(self.operand_symbol(sl::ConstructorId(i as u32), c, k, o, scope));
            }
        }
        // A table with no constructors at all still needs its symbol written.
        for (t, done) in written.iter().enumerate().skip(1) {
            if !done && self.kept(t) {
                pending.push(t);
            }
        }
        for t in pending {
            syms.push(self.table_symbol(t));
        }

        (scopes, syms)
    }

    fn token_field(&self, f: &sl::Field) -> sla::TokenField {
        let token = &self.spec.tokens[f.token.index()];
        let big = token.endian == sl::Endian::Big;
        let (start_byte, end_byte) = if big {
            (
                u64::from(token.size - 1 - f.high / 8),
                u64::from(token.size - 1 - f.low / 8),
            )
        } else {
            (u64::from(f.low / 8), u64::from(f.high / 8))
        };
        sla::TokenField {
            big_endian: big,
            signed: f.signed,
            start_bit: u64::from(f.low),
            end_bit: u64::from(f.high),
            start_byte,
            end_byte,
            // The bytes the field touches are assembled most significant
            // first, so the field's own low bit sits `low % 8` up from the
            // bottom of that number whichever way the token runs.
            shift: u64::from(f.low % 8),
        }
    }

    fn operand_symbol(
        &self,
        cid: sl::ConstructorId,
        c: &sl::Constructor,
        index: usize,
        o: &sl::Operand,
        scope: u32,
    ) -> sla::Symbol {
        let (table, ct) = self.ct_place[cid.index()];
        let hand = hand_order(c);
        // The operand's own record always names where it came from: which
        // operand of which constructor of which table.
        let mut expr = vec![sla::Expr::OperandValue {
            index: hand[index],
            table: u64::from(table),
            ct,
        }];
        // A family symbol is referenced by id; a plain field is written out
        // inline, because it has no symbol of its own at this point.
        let sub = match o.source {
            sl::OperandSource::Table(t) => Some(self.table_id[t.index()]),
            sl::OperandSource::Field(f) => {
                if self.spec.field(f).attach.is_empty() {
                    expr.push(sla::Expr::TokenField(self.token_field(self.spec.field(f))));
                    None
                } else {
                    Some(self.field_id[f.index()])
                }
            }
            sl::OperandSource::Context(cf) => Some(self.context_id[cf.index()]),
            sl::OperandSource::Varnode(v) => Some(self.varnode_id[v.index()]),
            // A bit range over a register has no family symbol of its own in
            // the compiled form, so it is written like a computed operand.
            sl::OperandSource::BitRange(_)
            | sl::OperandSource::Computed
            | sl::OperandSource::Unbound => None,
        };
        // An operand a disassembly action computes carries the computation in
        // its own body, right after the `operand_value` that names it. Proved
        // against the reference: `[ val = -imm; ]` gives `12(...)` then
        // `50(12(...))` under the symbol named `val`.
        for st in &c.disasm {
            if let sl::DisasmStmt::Assign {
                target: sl::DisasmTarget::Operand(k),
                value,
            } = st
            {
                if usize::from(*k) == index {
                    expr.push(self.disasm_expr(value, cid, &hand));
                }
            }
        }
        sla::Symbol {
            id: self.operand_id[cid.index()][index],
            name: Some(o.name.clone()),
            scope: Some(scope),
            body: sla::SymbolBody::Operand {
                index: hand[index],
                offset: o.offset.delta as u64,
                sub_symbol: sub,
                base: o.offset.base.map_or(-1, |b| hand[b as usize] as i64),
                min_length: self.operand_length(o),
                flag: None,
                expr,
            },
        }
    }

    /// How many instruction bytes the operand's own bits occupy: the width of
    /// the token it is cut from, or the shortest match of the subtable it
    /// names. A fixed register, a context field and a value the disassembly
    /// action computes all take none, and the reference writes 0 for them.
    fn operand_length(&self, o: &sl::Operand) -> u64 {
        match o.source {
            sl::OperandSource::Field(f) => {
                u64::from(self.spec.tokens[self.spec.field(f).token.index()].size)
            }
            sl::OperandSource::Table(t) => self.spec.table(t).min_length as u64,
            _ => 0,
        }
    }

    fn table_symbol(&mut self, t: usize) -> sla::Symbol {
        // Copy the reference out so the constructor walk below borrows the
        // specification rather than `self`, which it also mutates.
        let spec = self.spec;
        let table = &spec.tables[t];
        let mut constructors = Vec::new();
        let mut pairs: Vec<(u32, sla::Pattern)> = Vec::new();
        for (k, cid) in table.constructors.iter().enumerate() {
            let c = spec.constructor(*cid);
            constructors.push(self.constructor(*cid, c));
            for alt in &c.resolved.alternatives {
                for p in self.patterns_for(c, alt) {
                    pairs.push((k as u32, p));
                }
            }
            if c.resolved.alternatives.is_empty() {
                pairs.push((
                    k as u32,
                    sla::Pattern {
                        has_instruction: true,
                        ..sla::Pattern::default()
                    },
                ));
            }
        }
        let decision = sla::Decision {
            number: pairs.len() as u64,
            on_context: false,
            start_bit: 0,
            // Zero bits examined: a leaf that tries each pattern in order.
            num_bits: 0,
            children: Vec::new(),
            pairs,
        };
        sla::Symbol {
            id: self.table_id[t],
            name: Some(table.name.clone()),
            scope: Some(0),
            body: sla::SymbolBody::Subtable {
                constructors,
                decision: Some(decision),
            },
        }
    }

    /// The decision-tree patterns for one alternative.
    ///
    /// A constraint between two fields, `Rn=Rm`, is not a bit test, so the
    /// front end leaves it as a residual. The compiled format has nowhere to
    /// put it, and the reference compiler's answer is to enumerate: one
    /// alternative per value the two fields share.
    ///
    /// **Proved**: `:same is op=0x30 & rd=rs` with `rd` and `rs` four bits
    /// wide gives a decision whose `number` is 17, sixteen alternatives for
    /// that constructor and one for its sibling.
    ///
    /// The enumeration needs the fields' byte offsets inside the instruction,
    /// which is only known here when every token is the same width and this
    /// alternative is one token long. Anything else is written as the bits
    /// alone and counted in [`Report::approximate_patterns`], because a
    /// pattern that matches too much is a wrong decode and saying so is the
    /// only honest option.
    fn patterns_for(&mut self, c: &sl::Constructor, alt: &sl::PatternAlt) -> Vec<sla::Pattern> {
        if alt.residual.is_empty() {
            return vec![pattern(&alt.instr, &alt.context)];
        }
        match self.expand(c, alt) {
            Some(v) => v,
            None => {
                self.report.approximate_patterns += 1;
                self.report.note(
                    "a pattern constraint that is not a bit test was written as the bits alone",
                );
                vec![pattern(&alt.instr, &alt.context)]
            }
        }
    }

    fn expand(&self, c: &sl::Constructor, alt: &sl::PatternAlt) -> Option<Vec<sla::Pattern>> {
        let width = self.uniform_token?;
        if c.resolved.approximation.is_some() || alt.length != width as usize {
            return None;
        }
        let mut variants = vec![alt.instr.clone()];
        for r in &alt.residual {
            let (a, b) = field_equality(r)?;
            let (fa, fb) = (self.spec.field(a), self.spec.field(b));
            let bits = fa.bits();
            if bits != fb.bits() || bits > 8 {
                return None;
            }
            let count = 1u64 << bits;
            // A cap, so a wide pair costs a refusal rather than a million
            // alternatives.
            if variants.len() as u64 * count > 512 {
                return None;
            }
            let (ta, tb) = (self.spec.token_of(a), self.spec.token_of(b));
            let mut next = Vec::new();
            for v in &variants {
                for x in 0..count {
                    let mut mv = v.clone();
                    set_field(&mut mv, fa, ta, x);
                    set_field(&mut mv, fb, tb, x);
                    next.push(mv);
                }
            }
            variants = next;
        }
        Some(
            variants
                .iter()
                .map(|mv| pattern(mv, &alt.context))
                .collect(),
        )
    }

    fn constructor(&mut self, cid: sl::ConstructorId, c: &sl::Constructor) -> sla::Constructor {
        self.report.constructors += 1;
        if c.body.is_some() {
            self.report.without_semantics += 1;
        }
        if let Some(why) = c.resolved.approximation {
            self.report.approximate_patterns += 1;
            self.report
                .note(format!("pattern reduced approximately: {why:?}"));
        }
        let hand = hand_order(c);
        let print = print_pieces(&c.display, &hand);
        let context_ops = self.context_ops(cid, c, &hand);
        for op in &context_ops {
            match op {
                sla::ContextOp::Set { .. } => self.report.context_sets += 1,
                sla::ContextOp::Commit { .. } => self.report.globalsets += 1,
            }
        }
        self.report.computed_operands += c
            .disasm
            .iter()
            .filter(|s| {
                matches!(
                    s,
                    sl::DisasmStmt::Assign {
                        target: sl::DisasmTarget::Operand(_),
                        ..
                    }
                )
            })
            .count();
        let ids = &self.operand_id[cid.index()];
        sla::Constructor {
            parent: self.ct_place[cid.index()].0,
            source: self.source_index(c),
            line: u64::from(c.location.line),
            length: c.resolved.min_length() as u64,
            flowthru: flowthru(&print),
            // The operand list is in resolution order, and every index in the
            // file, including the print pieces, is a position in it.
            operands: c.order.iter().map(|i| ids[*i as usize]).collect(),
            print,
            context_ops,
            templates: Vec::new(),
        }
    }

    /// The disassembly action section as the file carries it: a context
    /// assignment (element 32) or a `globalset` (79) each, in source order.
    /// An assignment to an operand is not here; it lives in that operand's own
    /// symbol body.
    fn context_ops(
        &self,
        cid: sl::ConstructorId,
        c: &sl::Constructor,
        hand: &[u64],
    ) -> Vec<sla::ContextOp> {
        let mut out = Vec::new();
        for st in &c.disasm {
            match st {
                sl::DisasmStmt::Assign {
                    target: sl::DisasmTarget::Context(cf),
                    value,
                } => {
                    let f = &self.spec.context_fields[cf.index()];
                    let (word, shift, mask) = context_word(f);
                    out.push(sla::ContextOp::Set {
                        word,
                        shift,
                        mask,
                        value: vec![self.disasm_expr(value, cid, hand)],
                    });
                }
                sl::DisasmStmt::Assign { .. } => {}
                sl::DisasmStmt::GlobalSet { address, context } => {
                    let f = &self.spec.context_fields[context.index()];
                    let (word, _, mask) = context_word(f);
                    out.push(sla::ContextOp::Commit {
                        symbol: self.globalset_symbol(address, cid),
                        word,
                        mask,
                        // `noflow` on the field is what clears it, proved by
                        // being the only edit that moves the bit.
                        flow: !f.noflow,
                    });
                }
            }
        }
        out
    }

    /// The address argument of a `globalset` is written as a symbol id, and
    /// the only things that can stand there are the three built-in addresses
    /// and an operand of the constructor.
    fn globalset_symbol(&self, address: &sl::DisasmExpr, cid: sl::ConstructorId) -> u32 {
        match address {
            sl::DisasmExpr::Symbol(sl::SymbolRef::Builtin(b)) => match b {
                sl::Builtin::InstNext => 2,
                sl::Builtin::InstNext2 => 3,
                _ => 1,
            },
            sl::DisasmExpr::Symbol(sl::SymbolRef::Operand(i)) => self.operand_id[cid.index()]
                .get(usize::from(*i))
                .copied()
                .unwrap_or(1),
            // `inst_start` is what the reference falls back to, and nothing in
            // the corpus writes anything else here.
            _ => 1,
        }
    }

    /// One disassembly-time expression as the element tree that carries it.
    /// Nothing is folded: `4 - imm` stays a subtract of a literal from an
    /// operand, in that order.
    fn disasm_expr(&self, e: &sl::DisasmExpr, cid: sl::ConstructorId, hand: &[u64]) -> sla::Expr {
        match e {
            // A negative literal is unary minus applied to a positive one,
            // which is what the reference writes and what our reader reads.
            sl::DisasmExpr::Num(v) if *v < 0 => sla::Expr::Op {
                op: sla::PatternOp::Minus,
                operands: vec![sla::Expr::Constant(i128::from(v.unsigned_abs()))],
            },
            sl::DisasmExpr::Num(v) => sla::Expr::Constant(i128::from(*v)),
            sl::DisasmExpr::Symbol(s) => self.disasm_symbol(*s, cid, hand),
            sl::DisasmExpr::Unary(op, a) => sla::Expr::Op {
                op: match op {
                    sl::DisasmUnOp::Negate => sla::PatternOp::Minus,
                    sl::DisasmUnOp::Not => sla::PatternOp::Not,
                },
                operands: vec![self.disasm_expr(a, cid, hand)],
            },
            sl::DisasmExpr::Binary(op, a, b) => sla::Expr::Op {
                op: match op {
                    sl::DisasmBinOp::Add => sla::PatternOp::Plus,
                    sl::DisasmBinOp::Sub => sla::PatternOp::Sub,
                    sl::DisasmBinOp::Mul => sla::PatternOp::Mult,
                    sl::DisasmBinOp::Div => sla::PatternOp::Div,
                    sl::DisasmBinOp::Shl => sla::PatternOp::LeftShift,
                    sl::DisasmBinOp::Shr => sla::PatternOp::RightShift,
                    sl::DisasmBinOp::And => sla::PatternOp::And,
                    sl::DisasmBinOp::Or => sla::PatternOp::Or,
                    sl::DisasmBinOp::Xor => sla::PatternOp::Xor,
                },
                operands: vec![
                    self.disasm_expr(a, cid, hand),
                    self.disasm_expr(b, cid, hand),
                ],
            },
        }
    }

    fn disasm_symbol(&self, s: sl::SymbolRef, cid: sl::ConstructorId, hand: &[u64]) -> sla::Expr {
        let (table, ct) = self.ct_place[cid.index()];
        match s {
            sl::SymbolRef::Operand(i) => sla::Expr::OperandValue {
                index: hand.get(usize::from(i)).copied().unwrap_or(u64::from(i)),
                table: u64::from(table),
                ct,
            },
            sl::SymbolRef::Context(cf) => {
                sla::Expr::Context(context_field(&self.spec.context_fields[cf.index()]))
            }
            sl::SymbolRef::Field(f) => sla::Expr::TokenField(self.token_field(self.spec.field(f))),
            sl::SymbolRef::Builtin(sl::Builtin::InstStart) => sla::Expr::InstStart,
            sl::SymbolRef::Builtin(sl::Builtin::InstNext) => sla::Expr::InstNext,
            sl::SymbolRef::Builtin(sl::Builtin::InstNext2) => sla::Expr::InstNext2,
            // A named register has no value at disassembly time. The reference
            // compiler accepts `[ val = r3 + imm; ]` without a warning and
            // writes a zero for the register, so this writes the same thing
            // rather than inventing a leaf the format does not have.
            _ => sla::Expr::Constant(0),
        }
    }
}

/// A context field as element 29 carries it: bit numbers from the register's
/// most significant bit, and the byte range they fall in.
fn context_field(cf: &sl::ContextField) -> sla::ContextField {
    sla::ContextField {
        signed: cf.signed,
        start_bit: u64::from(cf.low),
        end_bit: u64::from(cf.high),
        start_byte: u64::from(cf.low / 8),
        end_byte: u64::from(cf.high / 8),
        // Context bits are numbered from the most significant bit of the
        // register, so the shift is measured from the far end of the byte the
        // field ends in.
        shift: u64::from(7 - cf.high % 8),
    }
}

/// Where a context field sits in the 32-bit words a context record addresses:
/// which word, the right shift that brings the field to bit zero of it, and
/// the bits it owns.
///
/// **Proved** against the reference: `test=(0,0)` gives shift 31 and mask
/// `0x80000000`, `mode=(1,4)` gives 27 and `0x78000000`, `wide=(5,8)` gives 23
/// and `0x07800000`, and a field at (32,63) of an eight-byte register gives
/// word 1.
fn context_word(cf: &sl::ContextField) -> (u64, u64, u64) {
    let word = u64::from(cf.low / 32);
    // A field that straddles a word boundary has no representation here. The
    // published corpus has none, and clamping keeps the number written true to
    // the bits it describes rather than wrapping into the next word.
    let high = cf.high.max(cf.low).min(cf.low / 32 * 32 + 31);
    let shift = u64::from(31 - high % 32);
    let width = u64::from(high - cf.low + 1);
    let mask = if width >= 64 {
        u64::MAX
    } else {
        ((1u64 << width) - 1) << shift
    };
    (word, shift, mask)
}

/// For each operand, its position in the constructor's resolution order.
///
/// The front end numbers operands in display order; the compiled file numbers
/// them in the order a decoder has to resolve them, which is different
/// wherever a disassembly action computes one operand from another. Every
/// index in the file is a position in that second order.
fn hand_order(c: &sl::Constructor) -> Vec<u64> {
    let mut hand = vec![0u64; c.operands.len()];
    if c.order.len() != c.operands.len() {
        // A specification the front end could not order is written in display
        // order rather than refused; the round trip still holds.
        for (i, h) in hand.iter_mut().enumerate() {
            *h = i as u64;
        }
        return hand;
    }
    for (pos, i) in c.order.iter().enumerate() {
        if let Some(h) = hand.get_mut(*i as usize) {
            *h = pos as u64;
        }
    }
    hand
}

/// The display section as the file wants it: one piece per run of whitespace
/// and one per run of anything else, with operands in between.
fn print_pieces(d: &sl::Display, hand: &[u64]) -> Vec<sla::PrintPiece> {
    let mut out = Vec::new();
    if let Some(m) = &d.mnemonic {
        push_literal(&mut out, m);
    }
    for p in &d.pieces {
        match p {
            sl::DisplayPiece::Literal(s) => push_literal(&mut out, s),
            sl::DisplayPiece::Operand(i) => out.push(sla::PrintPiece::Operand(
                hand.get(*i as usize).copied().unwrap_or(u64::from(*i)),
            )),
        }
    }
    out
}

fn push_literal(out: &mut Vec<sla::PrintPiece>, s: &str) {
    let mut run = String::new();
    let mut space: Option<bool> = None;
    for ch in s.chars() {
        let is_space = ch.is_whitespace();
        if space != Some(is_space) && !run.is_empty() {
            out.push(sla::PrintPiece::Literal(std::mem::take(&mut run)));
        }
        space = Some(is_space);
        run.push(ch);
    }
    if !run.is_empty() {
        out.push(sla::PrintPiece::Literal(run));
    }
}

/// Where the mnemonic ends: the first whitespace piece, or the whole display
/// when there is none. Read off the corpus, where the two agree on every
/// constructor that has a whitespace piece at all.
fn flowthru(print: &[sla::PrintPiece]) -> i64 {
    for (i, p) in print.iter().enumerate() {
        if let sla::PrintPiece::Literal(s) = p {
            if !s.is_empty() && s.chars().all(char::is_whitespace) {
                return i as i64;
            }
        }
    }
    print.len() as i64
}

/// One alternative of a resolved pattern as the decision tree wants it.
fn pattern(instr: &sl::MaskValue, ctx: &sl::MaskValue) -> sla::Pattern {
    let instruction = blocks(instr);
    let context = blocks(ctx);
    let has_context = !context.is_empty();
    sla::Pattern {
        combined: has_context && !instruction.is_empty(),
        has_context,
        has_instruction: true,
        context,
        instruction,
    }
}

/// A mask and value over bytes, as the run of 32-bit big-endian words the
/// format uses. Leading and trailing bytes that constrain nothing are dropped,
/// because the block carries its own offset.
fn blocks(mv: &sl::MaskValue) -> Vec<sla::PatternBlock> {
    let first = match mv.mask.iter().position(|&b| b != 0) {
        Some(i) => i,
        None => return Vec::new(),
    };
    let last = mv.mask.iter().rposition(|&b| b != 0).unwrap_or(first);
    let mut words = Vec::new();
    let mut i = first;
    while i <= last {
        let mut mask = 0u64;
        let mut value = 0u64;
        for k in 0..4 {
            let at = i + k;
            let (m, v) = if at <= last {
                (mv.mask[at], mv.value.get(at).copied().unwrap_or(0))
            } else {
                (0, 0)
            };
            mask |= u64::from(m) << (24 - 8 * k);
            value |= u64::from(v) << (24 - 8 * k);
        }
        words.push(sla::PatternWord { mask, value });
        i += 4;
    }
    vec![sla::PatternBlock {
        offset: first as u64,
        bytes: (last - first + 1) as u64,
        words,
    }]
}

/// The last path component, which is what a compiled file records.
fn base_name(path: &str) -> String {
    path.rsplit(['/', '\\']).next().unwrap_or(path).to_owned()
}

/// A residual of the form `field = field`, which is the only shape that can be
/// enumerated into bits.
fn field_equality(e: &sl::PatternExpr) -> Option<(sl::FieldId, sl::FieldId)> {
    let sl::PatternExpr::Constraint { lhs, op, rhs } = e else {
        return None;
    };
    if *op != sl::ConstraintOp::Equal {
        return None;
    }
    match (lhs, rhs) {
        (sl::SymbolRef::Field(a), sl::DisasmExpr::Symbol(sl::SymbolRef::Field(b))) => {
            Some((*a, *b))
        }
        _ => None,
    }
}

/// Pin a token field to a value in a mask and value pair over instruction
/// bytes. The bit numbering is SLEIGH's own: bit zero of a token is the least
/// significant bit of its least significant byte, and a big-endian token
/// counts its bytes from the far end.
fn set_field(mv: &mut sl::MaskValue, f: &sl::Field, token: &sl::TokenDef, value: u64) {
    let size = token.size as usize;
    if mv.mask.len() < size {
        mv.mask.resize(size, 0);
        mv.value.resize(size, 0);
    }
    for (out, bit) in (f.low..=f.high).enumerate() {
        let byte = match token.endian {
            sl::Endian::Big => token.size - 1 - bit / 8,
            sl::Endian::Little => bit / 8,
        } as usize;
        let shift = bit % 8;
        mv.mask[byte] |= 1 << shift;
        mv.value[byte] &= !(1 << shift);
        if value >> out & 1 == 1 {
            mv.value[byte] |= 1 << shift;
        }
    }
}
