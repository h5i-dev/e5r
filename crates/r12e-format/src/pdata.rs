//! The PE exception directory and the unwind data behind it.
//!
//! On x86-64 and ARM64 the Windows ABI requires every function that touches the
//! stack to declare how to unwind it, so `.pdata` is a linker-built table of
//! function boundaries that survives stripping. There is nothing better in a
//! stripped PE: no prologue scan competes with a start and an end the file
//! states outright.
//!
//! Three layers, each weaker than the one above it:
//!
//! 1. `RUNTIME_FUNCTION`. Proven. The format defines the entry.
//! 2. `UNWIND_INFO` in `.xdata`, reached by an RVA the entry carries: the
//!    prologue's frame setup, the handler routine, and the chain to a parent
//!    record when this one is a funclet. Also proven; also stated outright.
//! 3. The language-specific data after the handler. Its shape depends on which
//!    handler it is, and the image does not say which. What follows is parsed
//!    as `__C_specific_handler`'s scope table only when every field validates,
//!    and dropped with a warning otherwise. A C++ image puts a `FuncInfo` RVA
//!    here instead, and that fails the very first bound.
//!
//! ARM64 gets boundaries and handlers but not decoded prologue opcodes; ARM32
//! gets starts only. Both say so rather than guessing.

use r12e_core::{Addr, Arch, Caps, Evidence, Provenance};

use crate::pe::Image;
use crate::{FunctionHint, Object};

// UNWIND_INFO flags.
const UNW_FLAG_EHANDLER: u8 = 0x1;
const UNW_FLAG_UHANDLER: u8 = 0x2;
const UNW_FLAG_CHAININFO: u8 = 0x4;

/// How deep a chain of `UNW_FLAG_CHAININFO` records is followed. Real chains
/// are one or two long; the limit is what stops a cycle in a hostile file.
const MAX_CHAIN: u32 = 8;

/// Entries accepted in one scope table. A function with more `__try` blocks
/// than this does not exist; a file that claims one is lying.
const MAX_SCOPE_ENTRIES: u64 = 4096;

/// One entry of the exception directory.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RuntimeFunction {
    /// First byte of the function.
    pub start: Addr,
    /// One past its last byte. x86-64 states this directly; ARM64 takes it from
    /// the unwind data; ARM32 is left unknown rather than guessed.
    pub end: Option<Addr>,
    /// RVA of the `UNWIND_INFO` record, when the entry points at one.
    pub unwind_rva: Option<u32>,
    /// ARM64's packed form, used instead of an `.xdata` record when the frame
    /// is simple enough to fit in the entry itself.
    pub packed: Option<Arm64Packed>,
}

/// ARM64 unwind data packed into the `.pdata` entry.
///
/// Field names follow the ARM64 exception handling documentation so an entry
/// can be diffed against it.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Arm64Packed {
    /// 1 for a whole function, 2 for a fragment.
    pub flag: u8,
    /// Function length in bytes.
    pub function_length: u32,
    /// Count of saved non-volatile floating-point registers, d8 upward.
    pub reg_f: u8,
    /// Count of saved non-volatile integer registers, x19 upward.
    pub reg_i: u8,
    /// True when the function homes its integer parameter registers.
    pub homed_parameters: bool,
    /// Chained-return, frame-chain and signing state, as the two-bit CR field.
    pub cr: u8,
    /// Bytes of stack the frame allocates.
    pub frame_size: u32,
}

/// One operation in an x86-64 prologue, as `UNWIND_CODE` records it.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum UnwindOp {
    /// `push` of a non-volatile integer register.
    PushNonVolatile {
        /// Register number, as [`x64_register`] names it.
        reg: u8,
    },
    /// A subtraction from `rsp`, in either the small or the large encoding.
    Alloc {
        /// Bytes allocated.
        bytes: u64,
    },
    /// The frame pointer is established here.
    SetFramePointer,
    /// A non-volatile integer register stored at a frame offset.
    SaveNonVolatile {
        /// Register number.
        reg: u8,
        /// Offset from the frame base.
        offset: u64,
    },
    /// The low 128 bits of a non-volatile XMM register stored at an offset.
    SaveXmm128 {
        /// XMM register number.
        reg: u8,
        /// Offset from the frame base.
        offset: u64,
    },
    /// A machine frame pushed by the processor, as an interrupt entry has.
    PushMachineFrame {
        /// True when the frame carries an error code.
        error_code: bool,
    },
    /// Version 2's epilogue marker, which describes an epilogue rather than the
    /// prologue and so says nothing about frame setup.
    Epilogue,
    /// An opcode this parser does not know. Recorded rather than dropped: the
    /// difference between "the prologue does something unusual" and "the
    /// prologue is what we listed" is the whole point of the evidence model.
    Unknown {
        /// The opcode nibble.
        op: u8,
        /// The info nibble.
        info: u8,
    },
}

/// One `UNWIND_CODE`, with the prologue offset it applies at.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct UnwindCode {
    /// Offset into the prologue of the instruction that follows this operation.
    pub prolog_offset: u8,
    /// What the instruction did.
    pub op: UnwindOp,
}

/// What a scope table entry names as its handler.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ScopeHandler {
    /// A filter or termination-handler address.
    Address(Addr),
    /// The compiler folded a constant filter: 0 is `EXCEPTION_CONTINUE_SEARCH`,
    /// 1 is `EXCEPTION_EXECUTE_HANDLER`. `__except(1)` produces the latter.
    Constant(u32),
}

/// One `__try` region of a `__C_specific_handler` scope table.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ScopeEntry {
    /// First address the region covers.
    pub begin: Addr,
    /// One past the last address it covers.
    pub end: Addr,
    /// The filter, for `__except`; the termination handler, for `__finally`.
    pub handler: ScopeHandler,
    /// Where control resumes when the filter accepts. Absent for `__finally`.
    pub target: Option<Addr>,
}

/// A decoded `UNWIND_INFO` record.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct UnwindInfo {
    /// The function this describes.
    pub function: Addr,
    /// Where the record itself is, as an RVA.
    pub rva: u32,
    /// Format version, 1 or 2.
    pub version: u8,
    /// The `UNW_FLAG_*` bits.
    pub flags: u8,
    /// Bytes of prologue.
    pub prolog_size: u8,
    /// Register holding the frame pointer, absent when the function addresses
    /// its frame through `rsp`.
    pub frame_register: Option<u8>,
    /// Distance from `rsp` at the point the frame pointer was established.
    pub frame_offset: u32,
    /// The prologue, in the order the unwinder undoes it, which is the reverse
    /// of the order the processor executed it. Codes from a chained parent
    /// follow this record's own.
    pub codes: Vec<UnwindCode>,
    /// Total bytes the prologue subtracts from `rsp`, chained records included.
    pub stack_alloc: u64,
    /// The language-specific handler routine, when the record names one.
    pub handler: Option<Addr>,
    /// Start of the `RUNTIME_FUNCTION` this record chains to. A funclet points
    /// at the function it was split out of, and the prologue lives there.
    pub chained: Option<Addr>,
    /// The scope table, when the language-specific data validated as one.
    pub scopes: Vec<ScopeEntry>,
}

impl UnwindInfo {
    /// True when the record names a handler that runs during the first pass.
    pub fn has_exception_handler(&self) -> bool {
        self.flags & UNW_FLAG_EHANDLER != 0
    }

    /// True when the record names a handler that runs while unwinding.
    pub fn has_termination_handler(&self) -> bool {
        self.flags & UNW_FLAG_UHANDLER != 0
    }
}

/// The x86-64 integer register a `UNWIND_CODE` register number names.
pub fn x64_register(n: u8) -> &'static str {
    const NAMES: [&str; 16] = [
        "rax", "rcx", "rdx", "rbx", "rsp", "rbp", "rsi", "rdi", "r8", "r9", "r10", "r11", "r12",
        "r13", "r14", "r15",
    ];
    NAMES[(n & 0xf) as usize]
}

/// Everything the exception directory and its unwind data produced.
#[derive(Debug, Clone, Default)]
pub struct Exceptions {
    /// One per `RUNTIME_FUNCTION`, in directory order.
    pub functions: Vec<RuntimeFunction>,
    /// The `UNWIND_INFO` records that were reachable and decodable, x86-64
    /// only. Shorter than `functions` whenever a record was absent or refused.
    pub unwind: Vec<UnwindInfo>,
}

/// Bytes per `RUNTIME_FUNCTION` for a machine, or `None` when the machine has
/// no exception directory in this shape.
fn entry_size(arch: &Arch) -> Option<u64> {
    match arch {
        Arch::X86_64 => Some(12),
        // Both ARM forms store a start and one word of unwind data, with no
        // end address: the length is inside the unwind data.
        Arch::AArch64 | Arch::Arm => Some(8),
        _ => None,
    }
}

/// Walk the exception directory, emitting a proven hint per entry.
pub fn read(
    img: &Image<'_>,
    dir_rva: u32,
    dir_size: u32,
    caps: &Caps,
    obj: &mut Object,
) -> Exceptions {
    let mut out = Exceptions::default();
    if dir_rva == 0 || dir_size == 0 {
        return out;
    }
    let Some(stride) = entry_size(img.arch()) else {
        obj.warnings.push(format!(
            "exception directory present but {} has no RUNTIME_FUNCTION layout; skipped",
            img.arch()
        ));
        return out;
    };
    let Some(at) = img.offset_of(dir_rva) else {
        obj.warnings
            .push("exception directory RVA is not inside any section".into());
        return out;
    };
    // Bound the count by the bytes that actually exist before touching any of
    // them: a size field is attacker-controlled and a capacity is not a promise.
    let available = img.len().saturating_sub(at);
    let count = (dir_size as u64 / stride)
        .min(available / stride)
        .min(caps.symbols);
    if count == 0 {
        obj.warnings.push(format!(
            "exception directory claims {dir_size} bytes but no whole entry fits in the file"
        ));
        return out;
    }
    if (dir_size as u64) / stride > count {
        obj.warnings.push(format!(
            "exception directory claims {} entries, {count} fit in the file",
            dir_size as u64 / stride
        ));
    }

    let mut unmapped = 0u64;
    let mut arm32 = 0u64;
    for i in 0..count {
        let Ok(mut e) = img
            .reader()
            .slice_at("runtime function", at + i * stride, stride)
        else {
            break;
        };
        let Ok(begin) = e.u32("BeginAddress") else {
            break;
        };
        if begin == 0 {
            // A terminator, or a hole the linker left.
            continue;
        }
        let start = img.addr_of(begin);
        let func = match img.arch() {
            Arch::X86_64 => {
                let (Ok(end), Ok(unwind)) = (e.u32("EndAddress"), e.u32("UnwindInfoAddress"))
                else {
                    break;
                };
                if end <= begin {
                    obj.warnings.push(format!(
                        "runtime function at {start} ends at or before it starts; ignored"
                    ));
                    continue;
                }
                RuntimeFunction {
                    start,
                    end: Some(img.addr_of(end)),
                    unwind_rva: (unwind != 0).then_some(unwind),
                    packed: None,
                }
            }
            Arch::AArch64 => {
                let Ok(data) = e.u32("UnwindData") else { break };
                arm64_entry(img, start, data, obj)
            }
            // The ARM32 packed form counts in halfwords and its `.xdata` header
            // differs from ARM64's. Neither is decoded here, so the end stays
            // unknown rather than being guessed from the ARM64 layout.
            _ => {
                let Ok(data) = e.u32("UnwindData") else { break };
                arm32 += 1;
                RuntimeFunction {
                    start,
                    end: None,
                    unwind_rva: (data & 3 == 0 && data != 0).then_some(data),
                    packed: None,
                }
            }
        };

        if !img.is_code(func.start) {
            unmapped += 1;
            continue;
        }
        obj.function_hints.push(FunctionHint {
            addr: func.start,
            size: func
                .end
                .and_then(|e| e.get().checked_sub(func.start.get()))
                .filter(|n| *n > 0),
            name: None,
            provenance: Provenance::new(Evidence::PeUnwind),
        });
        out.functions.push(func);
    }
    if unmapped != 0 {
        obj.warnings.push(format!(
            "{unmapped} runtime functions start outside every executable section; ignored"
        ));
    }
    if arm32 != 0 {
        obj.warnings.push(format!(
            "{arm32} ARM32 runtime functions gave starts only; their unwind encoding is not \
             decoded, so no end address is claimed"
        ));
    }

    if *img.arch() == Arch::X86_64 {
        for f in &out.functions {
            let Some(rva) = f.unwind_rva else { continue };
            if let Some(info) = read_unwind_info(img, f, rva, 0, caps, obj) {
                out.unwind.push(info);
            }
        }
    }
    out
}

/// One ARM64 `.pdata` entry: either a packed frame description or an RVA into
/// `.xdata`, decided by the low two bits.
fn arm64_entry(img: &Image<'_>, start: Addr, data: u32, obj: &mut Object) -> RuntimeFunction {
    if data & 3 == 0 {
        let rva = data;
        let (length, handler) = arm64_xdata(img, rva, obj);
        // The handler is code nothing else in the image references.
        if let Some(h) = handler {
            if img.is_code(h) {
                obj.function_hints.push(FunctionHint {
                    addr: h,
                    size: None,
                    name: None,
                    provenance: Provenance::new(Evidence::PeUnwind),
                });
            } else {
                obj.warnings.push(format!(
                    "ARM64 unwind handler for the function at {start} is {h}, which is not \
                     executable"
                ));
            }
        }
        return RuntimeFunction {
            start,
            end: length.and_then(|n| start.checked_add(n)),
            unwind_rva: Some(rva),
            packed: None,
        };
    }
    // Packed: the whole frame description is these 32 bits. Lengths count
    // instructions, so the byte length is four times the field.
    let packed = Arm64Packed {
        flag: (data & 3) as u8,
        function_length: ((data >> 2) & 0x7ff) * 4,
        reg_f: ((data >> 13) & 0x7) as u8,
        reg_i: ((data >> 16) & 0xf) as u8,
        homed_parameters: (data >> 20) & 1 != 0,
        cr: ((data >> 21) & 0x3) as u8,
        frame_size: ((data >> 23) & 0x1ff) * 16,
    };
    RuntimeFunction {
        start,
        end: start.checked_add(packed.function_length as u64),
        unwind_rva: None,
        packed: Some(packed),
    }
}

/// The ARM64 `.xdata` header, for the function length and the handler flag.
///
/// The unwind opcodes that follow are not decoded: they describe the prologue
/// in an encoding of their own and nothing above this crate asks for it yet.
fn arm64_xdata(img: &Image<'_>, rva: u32, obj: &mut Object) -> (Option<u64>, Option<Addr>) {
    let Some(at) = img.offset_of(rva) else {
        obj.warnings
            .push(format!("ARM64 unwind data at RVA {rva:#x} is not mapped"));
        return (None, None);
    };
    let Ok(mut r) = img.reader().slice_at("arm64 unwind header", at, 4) else {
        return (None, None);
    };
    let Ok(word) = r.u32("header") else {
        return (None, None);
    };
    // Lengths count instructions, and every A64 instruction is four bytes.
    let length = (word & 0x3_ffff) as u64 * 4;
    let version = (word >> 18) & 0x3;
    let has_exception_data = (word >> 20) & 1 != 0;
    // E: one packed epilogue, in which case the epilogue-count field is an
    // index into the opcodes rather than a count of scope words.
    let packed_epilogue = (word >> 21) & 1 != 0;
    let epilog_field = (word >> 22) & 0x1f;
    let code_words = (word >> 27) & 0x1f;
    if version != 0 {
        obj.warnings.push(format!(
            "ARM64 unwind data at RVA {rva:#x} is version {version}, which this parser does not \
             know; only its length was read"
        ));
        return (Some(length), None);
    }

    // A zero in both counts means an extension word carries the real ones.
    let (epilog_field, code_words, header_words) = if epilog_field == 0 && code_words == 0 {
        let Ok(mut ext) = img.reader().slice_at("arm64 unwind extension", at + 4, 4) else {
            return (Some(length), None);
        };
        let Ok(w) = ext.u32("extension") else {
            return (Some(length), None);
        };
        (w & 0xffff, (w >> 16) & 0xff, 2u64)
    } else {
        (epilog_field, code_words, 1u64)
    };

    if !has_exception_data {
        return (Some(length), None);
    }
    // Header words, then one word per epilogue scope unless the single
    // epilogue was packed into the header, then the opcode words. The handler
    // RVA follows all of it.
    let epilog_words = if packed_epilogue {
        0
    } else {
        epilog_field as u64
    };
    let handler_at = at
        + (header_words + epilog_words + code_words as u64)
            .saturating_mul(4)
            .min(u32::MAX as u64);
    let handler = img
        .reader()
        .slice_at("arm64 exception handler", handler_at, 4)
        .ok()
        .and_then(|mut h| h.u32("handler RVA").ok())
        .filter(|rva| *rva != 0)
        .map(|rva| img.addr_of(rva));
    (Some(length), handler)
}

/// Decode one `UNWIND_INFO`, following a chain to the record that holds the
/// prologue when this one is a funclet.
fn read_unwind_info(
    img: &Image<'_>,
    func: &RuntimeFunction,
    rva: u32,
    depth: u32,
    caps: &Caps,
    obj: &mut Object,
) -> Option<UnwindInfo> {
    let at = match img.offset_of(rva) {
        Some(at) => at,
        None => {
            obj.warnings.push(format!(
                "unwind info for the function at {} is at RVA {rva:#x}, which no section maps",
                func.start
            ));
            return None;
        }
    };
    let mut h = img.reader().slice_at("UNWIND_INFO", at, 4).ok()?;
    let version_flags = h.u8("VersionAndFlags").ok()?;
    let prolog_size = h.u8("SizeOfProlog").ok()?;
    let count_of_codes = h.u8("CountOfCodes").ok()?;
    let frame = h.u8("FrameRegisterAndOffset").ok()?;
    let version = version_flags & 0x7;
    let flags = version_flags >> 3;
    if version == 0 || version > 2 {
        obj.warnings.push(format!(
            "unwind info for the function at {} claims version {version}, which is not 1 or 2",
            func.start
        ));
        return None;
    }

    // Codes are two bytes each and the array is padded to a four-byte boundary,
    // so an odd count reserves one slot more than it uses.
    let slots = (count_of_codes as u64).next_multiple_of(2);
    let codes_bytes = slots * 2;
    let body = img
        .reader()
        .slice_at("unwind codes", at + 4, codes_bytes)
        .ok()?;

    let mut info = UnwindInfo {
        function: func.start,
        rva,
        version,
        flags,
        prolog_size,
        frame_register: (frame & 0xf != 0).then_some(frame & 0xf),
        frame_offset: (frame >> 4) as u32 * 16,
        codes: Vec::new(),
        stack_alloc: 0,
        handler: None,
        chained: None,
        scopes: Vec::new(),
    };
    decode_codes(&body, count_of_codes, version, &mut info, obj);

    let tail = at + 4 + codes_bytes;
    if flags & (UNW_FLAG_EHANDLER | UNW_FLAG_UHANDLER) != 0 {
        if let Ok(mut t) = img.reader().slice_at("exception handler RVA", tail, 4) {
            if let Ok(handler_rva) = t.u32("ExceptionHandler") {
                if handler_rva != 0 {
                    let addr = img.addr_of(handler_rva);
                    if img.is_code(addr) {
                        info.handler = Some(addr);
                        obj.function_hints.push(FunctionHint {
                            addr,
                            size: None,
                            name: None,
                            provenance: Provenance::new(Evidence::PeUnwind),
                        });
                    } else {
                        obj.warnings.push(format!(
                            "unwind handler for the function at {} points at {addr}, which is not \
                             executable",
                            func.start
                        ));
                    }
                }
                read_scope_table(img, func, tail + 4, caps, &mut info, obj);
            }
        }
    } else if flags & UNW_FLAG_CHAININFO != 0 && depth < MAX_CHAIN {
        if let Ok(mut c) = img.reader().slice_at("chained RUNTIME_FUNCTION", tail, 12) {
            if let (Ok(begin), Ok(_end), Ok(parent_rva)) = (
                c.u32("BeginAddress"),
                c.u32("EndAddress"),
                c.u32("UnwindInfoAddress"),
            ) {
                let parent_start = img.addr_of(begin);
                info.chained = Some(parent_start);
                if img.is_code(parent_start) {
                    obj.function_hints.push(FunctionHint {
                        addr: parent_start,
                        size: None,
                        name: None,
                        provenance: Provenance::new(Evidence::PeUnwind),
                    });
                }
                // The parent holds the prologue this funclet shares, so its
                // codes belong in the same frame description.
                if parent_rva != 0 && parent_rva != rva {
                    let parent_fn = RuntimeFunction {
                        start: parent_start,
                        end: None,
                        unwind_rva: Some(parent_rva),
                        packed: None,
                    };
                    if let Some(parent) =
                        read_unwind_info(img, &parent_fn, parent_rva, depth + 1, caps, obj)
                    {
                        info.codes.extend_from_slice(&parent.codes);
                        info.stack_alloc += parent.stack_alloc;
                        if info.frame_register.is_none() {
                            info.frame_register = parent.frame_register;
                            info.frame_offset = parent.frame_offset;
                        }
                    }
                }
            }
        }
    } else if flags & UNW_FLAG_CHAININFO != 0 {
        obj.warnings.push(format!(
            "unwind chain from the function at {} is more than {MAX_CHAIN} deep; stopped",
            func.start
        ));
    }

    Some(info)
}

/// Walk the `UNWIND_CODE` array. Every arm advances at least one slot, so the
/// walk terminates whatever the bytes say.
fn decode_codes(
    body: &r12e_core::Reader<'_>,
    count: u8,
    version: u8,
    info: &mut UnwindInfo,
    obj: &mut Object,
) {
    let slot = |i: u64| -> Option<u16> {
        body.slice_at("unwind code", i * 2, 2)
            .ok()?
            .u16("code")
            .ok()
    };
    let mut i = 0u64;
    while i < count as u64 {
        let Some(raw) = slot(i) else { break };
        let prolog_offset = (raw & 0xff) as u8;
        let op = ((raw >> 8) & 0xf) as u8;
        let extra = ((raw >> 12) & 0xf) as u8;
        let (nodes, decoded) = match op {
            0 => (1, UnwindOp::PushNonVolatile { reg: extra }),
            1 => match extra {
                0 => match slot(i + 1) {
                    Some(n) => (
                        2,
                        UnwindOp::Alloc {
                            bytes: n as u64 * 8,
                        },
                    ),
                    None => break,
                },
                1 => match (slot(i + 1), slot(i + 2)) {
                    (Some(lo), Some(hi)) => (
                        3,
                        UnwindOp::Alloc {
                            bytes: lo as u64 | ((hi as u64) << 16),
                        },
                    ),
                    _ => break,
                },
                info_bits => (
                    1,
                    UnwindOp::Unknown {
                        op,
                        info: info_bits,
                    },
                ),
            },
            2 => (
                1,
                UnwindOp::Alloc {
                    bytes: extra as u64 * 8 + 8,
                },
            ),
            3 => (1, UnwindOp::SetFramePointer),
            4 => match slot(i + 1) {
                Some(n) => (
                    2,
                    UnwindOp::SaveNonVolatile {
                        reg: extra,
                        offset: n as u64 * 8,
                    },
                ),
                None => break,
            },
            5 => match (slot(i + 1), slot(i + 2)) {
                (Some(lo), Some(hi)) => (
                    3,
                    UnwindOp::SaveNonVolatile {
                        reg: extra,
                        offset: lo as u64 | ((hi as u64) << 16),
                    },
                ),
                _ => break,
            },
            // Version 2 reuses 6 and 7 for epilogue description. Version 1 left
            // them undefined, and an undefined opcode is not a guess to make.
            6 if version >= 2 => (2, UnwindOp::Epilogue),
            7 if version >= 2 => (3, UnwindOp::Unknown { op, info: extra }),
            8 => match slot(i + 1) {
                Some(n) => (
                    2,
                    UnwindOp::SaveXmm128 {
                        reg: extra,
                        offset: n as u64 * 16,
                    },
                ),
                None => break,
            },
            9 => match (slot(i + 1), slot(i + 2)) {
                (Some(lo), Some(hi)) => (
                    3,
                    UnwindOp::SaveXmm128 {
                        reg: extra,
                        offset: lo as u64 | ((hi as u64) << 16),
                    },
                ),
                _ => break,
            },
            10 => (
                1,
                UnwindOp::PushMachineFrame {
                    error_code: extra == 1,
                },
            ),
            _ => {
                obj.warnings.push(format!(
                    "unwind code {op} in the function at {} is not a documented operation; the \
                     rest of the prologue was not read",
                    info.function
                ));
                info.codes.push(UnwindCode {
                    prolog_offset,
                    op: UnwindOp::Unknown { op, info: extra },
                });
                break;
            }
        };
        if let UnwindOp::Alloc { bytes } = decoded {
            info.stack_alloc += bytes;
        }
        info.codes.push(UnwindCode {
            prolog_offset,
            op: decoded,
        });
        i += nodes;
    }
}

/// Parse the language-specific data as a `__C_specific_handler` scope table,
/// and refuse it whole if any field fails.
///
/// The image does not say which handler the data belongs to, so acceptance is
/// the evidence. A C++ image stores a `FuncInfo` RVA in the same place; read as
/// a count it is far larger than the bytes that follow, which is the first
/// check below.
fn read_scope_table(
    img: &Image<'_>,
    func: &RuntimeFunction,
    at: u64,
    caps: &Caps,
    info: &mut UnwindInfo,
    obj: &mut Object,
) {
    let Some(end) = func.end else { return };
    let Ok(mut head) = img.reader().slice_at("scope table count", at, 4) else {
        return;
    };
    let Ok(count) = head.u32("Count") else { return };
    if count == 0 {
        return;
    }
    // The table cannot run past the section holding it, and it cannot be larger
    // than the file. Both bounds come before any allocation.
    let room = img
        .section_bytes_after(at)
        .unwrap_or_else(|| img.len().saturating_sub(at));
    let want = 4u64 + count as u64 * 16;
    if count as u64 > MAX_SCOPE_ENTRIES.min(caps.jump_table_entries) || want > room {
        obj.warnings.push(format!(
            "language-specific data for the function at {} is not a scope table: it claims \
             {count} entries, which does not fit the {room} bytes that follow",
            func.start
        ));
        return;
    }

    let body = func.start..end;
    let mut entries = Vec::with_capacity(count as usize);
    for i in 0..count as u64 {
        let Ok(mut e) = img
            .reader()
            .slice_at("scope table entry", at + 4 + i * 16, 16)
        else {
            return;
        };
        let (Ok(begin), Ok(stop), Ok(handler), Ok(target)) = (
            e.u32("BeginAddress"),
            e.u32("EndAddress"),
            e.u32("HandlerAddress"),
            e.u32("JumpTarget"),
        ) else {
            return;
        };
        let begin = img.addr_of(begin);
        let stop = img.addr_of(stop);
        // Every guarded region belongs to the function that declares it. This
        // is the check that keeps a C++ FuncInfo from being read as a table.
        if begin >= stop || !body.contains(&begin) || stop > end {
            obj.warnings.push(format!(
                "language-specific data for the function at {} is not a scope table: entry {i} \
                 guards {begin}..{stop}, which is not inside the function",
                func.start
            ));
            return;
        }
        entries.push(ScopeEntry {
            begin,
            end: stop,
            handler: if handler <= 1 {
                ScopeHandler::Constant(handler)
            } else {
                ScopeHandler::Address(img.addr_of(handler))
            },
            target: (target != 0).then(|| img.addr_of(target)),
        });
    }

    // Only now, with every entry validated, are the addresses worth acting on.
    for entry in &entries {
        if let ScopeHandler::Address(addr) = entry.handler {
            claim(img, func, addr, "scope table filter", obj);
        }
        if let Some(target) = entry.target {
            claim(img, func, target, "scope table handler", obj);
        }
    }
    info.scopes = entries;
}

/// Turn one scope-table address into a hint, a nothing, or a warning.
///
/// Inside the declaring function it is a block, not an entry, so it is recorded
/// in the scope table and nowhere else. Outside the function and executable, it
/// is a funclet that nothing else references. Outside every section it is not
/// evidence at all.
fn claim(img: &Image<'_>, func: &RuntimeFunction, addr: Addr, what: &str, obj: &mut Object) {
    if let Some(end) = func.end {
        if (func.start..end).contains(&addr) {
            return;
        }
    }
    if img.is_code(addr) {
        obj.function_hints.push(FunctionHint {
            addr,
            size: None,
            name: None,
            provenance: Provenance::new(Evidence::PeUnwind),
        });
    } else if img.is_mapped(addr) {
        obj.warnings.push(format!(
            "{what} for the function at {} is {addr}, which is mapped but not executable",
            func.start
        ));
    } else {
        obj.warnings.push(format!(
            "{what} for the function at {} is {addr}, which is outside every section",
            func.start
        ));
    }
}
