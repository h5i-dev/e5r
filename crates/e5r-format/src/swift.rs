//! Swift reflection metadata.
//!
//! Swift records what its runtime needs for reflection, casts and protocol
//! dispatch in sections the linker keeps: the nominal type descriptors, a
//! field descriptor per type naming every stored property with its type, and
//! one record per protocol conformance. None of it is stripped, because
//! `swift_conformsToProtocol` and `Mirror` read it at run time.
//!
//! Everything here is reached by relative pointer: a 32-bit signed
//! displacement from the address of the field that holds it, and in a few
//! places a low bit meaning the displacement reaches a pointer to the thing
//! rather than the thing. Measuring one from the start of its record instead
//! of from the field is the usual way a Swift reader produces output that
//! looks plausible and is wrong, so displacement arithmetic happens in exactly
//! two functions below and nowhere else.
//!
//! Nothing trusts a count: a field descriptor's record count is clamped to the
//! bytes behind it before one record is read, and the walk over a descriptor
//! section has to land exactly on the section's end or the section is reported
//! as not understood rather than half-parsed.

use e5r_core::{Addr, Evidence, Provenance};

use crate::metadata::{Image, MAX_NAME};
use crate::{FunctionHint, Object, Section};

/// Warnings to keep. A hostile section can produce one per record, and a
/// thousand copies of the same complaint is noise rather than a report.
const MAX_WARNINGS: usize = 32;

/// What the Swift sections said.
#[derive(Debug, Clone, Default)]
pub struct SwiftMetadata {
    /// Nominal type descriptors, in the order the type section lists them.
    pub types: Vec<SwiftType>,
    /// Every field descriptor, found by walking the field metadata section
    /// rather than only by following the types that point at one.
    pub field_descriptors: Vec<FieldDescriptor>,
    /// Protocol conformance records.
    pub conformances: Vec<Conformance>,
    /// Protocol descriptors this image defines.
    pub protocols: Vec<SwiftProtocol>,
    /// What could not be read, reported rather than guessed at.
    pub warnings: Vec<String>,
}

impl SwiftMetadata {
    /// True when no Swift section held anything.
    pub fn is_empty(&self) -> bool {
        self.types.is_empty()
            && self.field_descriptors.is_empty()
            && self.conformances.is_empty()
            && self.protocols.is_empty()
    }

    /// One hint per metadata accessor.
    ///
    /// The accessor is the only address in this metadata that is a function.
    /// A witness table and a descriptor are data, and a hint at either would
    /// be an invention.
    pub fn hints(&self) -> Vec<FunctionHint> {
        self.types
            .iter()
            .filter_map(|t| {
                Some(FunctionHint {
                    addr: t.accessor?,
                    size: None,
                    name: Some(format!("type metadata accessor for {}", t.qualified_name)),
                    provenance: Provenance::new(Evidence::SwiftMetadata),
                })
            })
            .collect()
    }
}

/// Which kind of context a descriptor describes.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ContextKind {
    /// A module.
    Module,
    /// An extension.
    Extension,
    /// An anonymous context: a function body or a local scope.
    Anonymous,
    /// A protocol.
    Protocol,
    /// An opaque type, which is what `some P` produces.
    OpaqueType,
    /// A class.
    Class,
    /// A struct.
    Struct,
    /// An enum.
    Enum,
    /// A kind this does not know, kept as the number the file spells.
    Other(u8),
}

impl ContextKind {
    fn from_flags(flags: u32) -> ContextKind {
        match (flags & 0x1f) as u8 {
            0 => ContextKind::Module,
            1 => ContextKind::Extension,
            2 => ContextKind::Anonymous,
            3 => ContextKind::Protocol,
            4 => ContextKind::OpaqueType,
            16 => ContextKind::Class,
            17 => ContextKind::Struct,
            18 => ContextKind::Enum,
            other => ContextKind::Other(other),
        }
    }

    /// The name the source spells this with.
    pub fn as_str(self) -> &'static str {
        match self {
            ContextKind::Module => "module",
            ContextKind::Extension => "extension",
            ContextKind::Anonymous => "anonymous",
            ContextKind::Protocol => "protocol",
            ContextKind::OpaqueType => "opaque type",
            ContextKind::Class => "class",
            ContextKind::Struct => "struct",
            ContextKind::Enum => "enum",
            ContextKind::Other(_) => "unknown",
        }
    }

    /// True when a descriptor of this kind carries a name, an accessor and a
    /// field descriptor, which is what makes it a nominal type.
    fn is_type(self) -> bool {
        matches!(
            self,
            ContextKind::Class | ContextKind::Struct | ContextKind::Enum
        )
    }
}

/// One nominal type the image declares.
#[derive(Debug, Clone)]
pub struct SwiftType {
    /// Where the descriptor is.
    pub addr: Addr,
    /// Class, struct or enum.
    pub kind: ContextKind,
    /// The type's own name, without its parents.
    pub name: String,
    /// The name with its parent contexts, module first, joined with dots. The
    /// same as `name` when no parent could be read.
    pub qualified_name: String,
    /// Its metadata accessor function, when the descriptor names one that
    /// lands in executable memory.
    pub accessor: Option<Addr>,
    /// Where its field descriptor is, when it has one.
    pub field_descriptor: Option<Addr>,
}

/// How a field descriptor's owner was declared.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum FieldDescriptorKind {
    /// A struct.
    Struct,
    /// A class.
    Class,
    /// An enum with one payload or none.
    Enum,
    /// An enum with several payload cases.
    MultiPayloadEnum,
    /// A Swift protocol.
    Protocol,
    /// A class-constrained protocol.
    ClassProtocol,
    /// An Objective-C protocol.
    ObjcProtocol,
    /// An Objective-C class.
    ObjcClass,
    /// A kind this does not know.
    Other(u16),
}

impl FieldDescriptorKind {
    fn from_raw(v: u16) -> FieldDescriptorKind {
        match v {
            0 => FieldDescriptorKind::Struct,
            1 => FieldDescriptorKind::Class,
            2 => FieldDescriptorKind::Enum,
            3 => FieldDescriptorKind::MultiPayloadEnum,
            4 => FieldDescriptorKind::Protocol,
            5 => FieldDescriptorKind::ClassProtocol,
            6 => FieldDescriptorKind::ObjcProtocol,
            7 => FieldDescriptorKind::ObjcClass,
            other => FieldDescriptorKind::Other(other),
        }
    }
}

/// One field descriptor: the stored properties or cases of one type.
#[derive(Debug, Clone)]
pub struct FieldDescriptor {
    /// Where the descriptor is, which is what a type descriptor points at.
    pub addr: Addr,
    /// The mangled name of the type it describes, when it carries one.
    pub mangled_type_name: Option<MangledName>,
    /// The mangled name of the superclass, for a class that has one.
    pub superclass: Option<MangledName>,
    /// How the type was declared.
    pub kind: FieldDescriptorKind,
    /// Its fields or cases, in declaration order.
    pub fields: Vec<Field>,
}

/// One stored property or enum case.
#[derive(Debug, Clone)]
pub struct Field {
    /// The name in the source.
    pub name: String,
    /// The mangled name of its type. Absent for an enum case with no payload,
    /// which genuinely has no type.
    pub mangled_type: Option<MangledName>,
    /// True for an enum case whose payload is stored indirectly.
    pub indirect_case: bool,
    /// True for a `var`, false for a `let`.
    pub mutable: bool,
    /// True for a field the compiler made rather than the source.
    pub artificial: bool,
}

/// A Swift mangled name as reflection spells it.
///
/// Reflection mangling is not plain text: a byte below 0x20 introduces a
/// symbolic reference, a relative pointer to the descriptor of the type that
/// belongs at that position. The text alone is therefore not the whole name,
/// and this says so rather than pretending otherwise.
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct MangledName {
    /// The printable characters, with the symbolic references taken out.
    pub text: String,
    /// True when the name carried at least one symbolic reference.
    pub symbolic: bool,
    /// What the symbolic references point at, in the order they appeared.
    pub references: Vec<Addr>,
}

/// How a conformance record names the type that conforms.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TypeReference {
    /// A relative pointer to the nominal type descriptor.
    DirectDescriptor,
    /// A relative pointer to a pointer to the descriptor.
    IndirectDescriptor,
    /// A relative pointer to an Objective-C class name.
    DirectObjcClassName,
    /// A relative pointer to a pointer to an Objective-C class object.
    IndirectObjcClass,
    /// A kind this does not know.
    Other(u8),
}

impl TypeReference {
    fn from_flags(flags: u32) -> TypeReference {
        match ((flags >> 3) & 0x7) as u8 {
            0 => TypeReference::DirectDescriptor,
            1 => TypeReference::IndirectDescriptor,
            2 => TypeReference::DirectObjcClassName,
            3 => TypeReference::IndirectObjcClass,
            other => TypeReference::Other(other),
        }
    }
}

/// One protocol conformance the image registers.
#[derive(Debug, Clone)]
pub struct Conformance {
    /// Where the record is.
    pub addr: Addr,
    /// The protocol descriptor it names, when the reference resolves.
    pub protocol_descriptor: Option<Addr>,
    /// The protocol's name, when the descriptor is in this image.
    pub protocol_name: Option<String>,
    /// How the conforming type is named.
    pub type_reference: TypeReference,
    /// The conforming type's descriptor, when the reference reaches one here.
    pub type_descriptor: Option<Addr>,
    /// The conforming type's name, when it could be read.
    pub type_name: Option<String>,
    /// The witness table or its instantiation pattern.
    pub witness_table: Option<Addr>,
    /// True when the conformance is declared outside both the protocol's
    /// module and the type's.
    pub retroactive: bool,
    /// How many conditional requirements the conformance carries. The
    /// requirements themselves are not parsed.
    pub conditional_requirements: u32,
}

/// One protocol the image defines.
#[derive(Debug, Clone)]
pub struct SwiftProtocol {
    /// Where the descriptor is.
    pub addr: Addr,
    /// Its name.
    pub name: String,
    /// Its name with its parent contexts.
    pub qualified_name: String,
    /// How many requirements it declares.
    pub requirements: u32,
}

/// Read every Swift section a loaded image carries.
pub fn read(obj: &Object) -> SwiftMetadata {
    let mut out = SwiftMetadata::default();
    let img = Image::new(obj);
    out.field_descriptors = field_descriptors(&img, &mut out.warnings);
    out.types = types(&img, &mut out.warnings);
    out.conformances = conformances(&img, &mut out.warnings);
    out.protocols = protocols(&img, &mut out.warnings);
    out
}

/// A 32-bit signed displacement from the address of the field holding it.
///
/// Zero is null rather than a self-reference, which is how Swift spells an
/// absent pointer in a fixed-size record.
fn relative(img: &Image<'_>, at: Addr) -> Option<Addr> {
    let d = img.u32(at)? as i32;
    (d != 0).then(|| at.wrapping_offset(d as i64))
}

/// The tagged form the type records use: the descriptor is four-byte aligned,
/// so the two bits below that carry the reference kind instead of address.
///
/// Zero in those bits is the descriptor itself and one is a pointer to it,
/// which is what a type defined in another image looks like once the linker
/// has made a slot for it.
fn relative_tagged(img: &Image<'_>, at: Addr) -> Option<(Addr, u8)> {
    let d = img.u32(at)? as i32;
    if d == 0 {
        return None;
    }
    Some((at.wrapping_offset((d & !3) as i64), (d & 3) as u8))
}

/// The indirectable form: the low bit of the displacement says the target is
/// a pointer to the thing rather than the thing itself.
///
/// The bit is part of the displacement and has to be cleared before it is
/// added, not after.
fn relative_indirect(img: &Image<'_>, at: Addr) -> Option<Addr> {
    let d = img.u32(at)? as i32;
    if d == 0 {
        return None;
    }
    let target = at.wrapping_offset((d & !1) as i64);
    if d & 1 != 0 {
        img.ptr(target).filter(|p| *p != Addr::ZERO)
    } else {
        Some(target)
    }
}

/// True when an address is inside a section this image declares.
///
/// A relative pointer that lands outside every section is a descriptor this
/// reader has misunderstood, or a file that is lying; either way it is a
/// warning and not a fact.
fn in_image(obj: &Object, at: Addr) -> bool {
    obj.section_at(at).is_some() || obj.memory.segment_at(at).is_some()
}

fn warn(warnings: &mut Vec<String>, message: String) {
    if warnings.len() < MAX_WARNINGS {
        warnings.push(message);
    }
}

/// Sections a Swift reflection kind lives in.
///
/// Mach-O prefixes the section name with its segment and ELF spells the same
/// section differently, so both names are checked. `__swift5_proto` and
/// `__swift5_protos` differ by one character and hold different things, which
/// is why this matches a whole name rather than a prefix.
fn sections<'a>(obj: &'a Object, mach: &'a str, elf: &'a str) -> impl Iterator<Item = &'a Section> {
    obj.sections.iter().filter(move |s| {
        !s.range.is_empty()
            && s.file_size != 0
            && (s.name.ends_with(mach) || s.name == elf || s.name.strip_prefix('.') == Some(elf))
    })
}

/// The bytes of a section, and the address they start at.
fn body<'a>(img: &Image<'a>, s: &Section) -> Option<(Addr, &'a [u8])> {
    let start = s.range.start();
    let bytes = img
        .obj()
        .memory
        .slice(start, s.file_size.min(s.range.len()))?;
    Some((start, bytes))
}

/// Every field descriptor, by walking the section they are packed into.
///
/// The section is a run of variable-length records with no count in front of
/// it, so the walk is the only way to enumerate them, and the walk landing
/// exactly on the end is the check that the record layout was read correctly.
fn field_descriptors(img: &Image<'_>, warnings: &mut Vec<String>) -> Vec<FieldDescriptor> {
    let mut out = Vec::new();
    for s in sections(img.obj(), "__swift5_fieldmd", "swift5_fieldmd") {
        let Some((start, bytes)) = body(img, s) else {
            continue;
        };
        let mut off = 0u64;
        let limit = bytes.len() as u64;
        while off + FIELD_DESCRIPTOR_SIZE <= limit {
            // A linker pads a section to its alignment, and a run of zeros is
            // padding rather than a descriptor with no name and no records.
            if bytes[off as usize..].iter().all(|b| *b == 0) {
                off = limit;
                break;
            }
            let Some(at) = start.checked_add(off) else {
                break;
            };
            let Some((d, size)) = field_descriptor(img, at, limit - off, warnings) else {
                warn(
                    warnings,
                    format!("swift: the field descriptor at {at} could not be read"),
                );
                break;
            };
            out.push(d);
            // A record is at least its header, so the walk always advances.
            off += size.max(FIELD_DESCRIPTOR_SIZE);
        }
        if off != limit {
            warn(
                warnings,
                format!(
                    "swift: {} is {limit} bytes and its records account for {off}, \
                     so the layout was not understood",
                    s.name
                ),
            );
        }
    }
    out
}

/// One field descriptor and how many bytes it took.
fn field_descriptor(
    img: &Image<'_>,
    at: Addr,
    room: u64,
    warnings: &mut Vec<String>,
) -> Option<(FieldDescriptor, u64)> {
    let mangled_type_name = relative(img, at).and_then(|p| mangled_name(img, p, warnings));
    let superclass = relative(img, at.checked_add(4)?).and_then(|p| mangled_name(img, p, warnings));
    let kind = FieldDescriptorKind::from_raw(img.u16(at.checked_add(8)?)?);
    let record_size = u64::from(img.u16(at.checked_add(10)?)?);
    let declared = u64::from(img.u32(at.checked_add(12)?)?);
    // Swift has only ever emitted twelve-byte records, and a record smaller
    // than its three fields cannot be walked at all.
    if record_size < FIELD_RECORD_SIZE {
        warn(
            warnings,
            format!("swift: the field descriptor at {at} declares {record_size}-byte records"),
        );
        return None;
    }
    // A count from the file cannot exceed the bytes behind it, and the bytes
    // behind it are what is left of the section.
    let fits = room.saturating_sub(FIELD_DESCRIPTOR_SIZE) / record_size;
    if declared > fits {
        warn(
            warnings,
            format!(
                "swift: the field descriptor at {at} declares {declared} fields \
                 and has room for {fits}"
            ),
        );
    }
    let count = declared.min(fits);
    let mut fields = Vec::with_capacity(usize::try_from(count).ok()?);
    for i in 0..count {
        let Some(record) = at.checked_add(FIELD_DESCRIPTOR_SIZE + i * record_size) else {
            break;
        };
        if let Some(f) = field(img, record, warnings) {
            fields.push(f);
        }
    }
    let size = FIELD_DESCRIPTOR_SIZE + count * record_size;
    Some((
        FieldDescriptor {
            addr: at,
            mangled_type_name,
            superclass,
            kind,
            fields,
        },
        size,
    ))
}

/// One field record: flags, then the type and the name.
fn field(img: &Image<'_>, at: Addr, warnings: &mut Vec<String>) -> Option<Field> {
    let flags = img.u32(at)?;
    let mangled_type =
        relative(img, at.checked_add(4)?).and_then(|p| mangled_name(img, p, warnings));
    let name_at = relative(img, at.checked_add(8)?)?;
    let Some(name) = img.cstr(name_at, MAX_NAME) else {
        warn(
            warnings,
            format!("swift: the field record at {at} names no readable field at {name_at}"),
        );
        return None;
    };
    Some(Field {
        name: name.to_string(),
        mangled_type,
        indirect_case: flags & FIELD_INDIRECT_CASE != 0,
        mutable: flags & FIELD_VAR != 0,
        artificial: flags & FIELD_ARTIFICIAL != 0,
    })
}

/// A mangled name, which ends at a NUL but may carry symbolic references that
/// contain one.
///
/// Stopping at the first zero byte is wrong for exactly that reason: a
/// symbolic reference is a control byte followed by a four-byte displacement,
/// and a displacement whose top byte is zero would cut the name short.
fn mangled_name(img: &Image<'_>, at: Addr, warnings: &mut Vec<String>) -> Option<MangledName> {
    let bytes = img.to_end(at)?;
    let mut out = MangledName::default();
    let mut i = 0usize;
    let pointer = usize::try_from(img.ptr_size()).ok()?;
    while i < bytes.len() && i < MAX_NAME as usize {
        let b = bytes[i];
        if b == 0 {
            return Some(out);
        }
        if (0x01..=0x17).contains(&b) {
            out.symbolic = true;
            let Some(payload) = bytes.get(i + 1..i + 5) else {
                break;
            };
            let d = i32::from_le_bytes([payload[0], payload[1], payload[2], payload[3]]);
            if let Some(field) = at.checked_add(i as u64 + 1) {
                out.references.push(field.wrapping_offset(d as i64));
            }
            i += 5;
            continue;
        }
        if (0x18..=0x1f).contains(&b) {
            // An absolute reference, which is a whole pointer rather than a
            // displacement. The bytes are stepped over, not read: a linked
            // image resolves them and a relocatable one does not.
            out.symbolic = true;
            i += 1 + pointer;
            continue;
        }
        out.text.push(b as char);
        i += 1;
    }
    warn(
        warnings,
        format!("swift: the mangled name at {at} has no terminator"),
    );
    (!out.text.is_empty() || out.symbolic).then_some(out)
}

/// Every nominal type descriptor the type section lists.
fn types(img: &Image<'_>, warnings: &mut Vec<String>) -> Vec<SwiftType> {
    let mut out = Vec::new();
    for s in sections(img.obj(), "__swift5_types", "swift5_type_metadata") {
        let Some((start, bytes)) = body(img, s) else {
            continue;
        };
        // An array of relative pointers, so its own length is the count.
        for i in 0..bytes.len() as u64 / 4 {
            let Some(slot) = start.checked_add(i * 4) else {
                break;
            };
            let Some((target, kind)) = relative_tagged(img, slot) else {
                continue;
            };
            if !in_image(img.obj(), target) {
                warn(
                    warnings,
                    format!(
                        "swift: the type record at {slot} points at {target}, \
                         outside the image"
                    ),
                );
                continue;
            }
            let at = match kind {
                0 => target,
                1 => match img.ptr(target).filter(|p| *p != Addr::ZERO) {
                    Some(p) => p,
                    None => {
                        warn(
                            warnings,
                            format!("swift: the type record at {slot} reaches an empty slot"),
                        );
                        continue;
                    }
                },
                other => {
                    warn(
                        warnings,
                        format!("swift: the type record at {slot} has reference kind {other}"),
                    );
                    continue;
                }
            };
            if !in_image(img.obj(), at) {
                warn(
                    warnings,
                    format!("swift: the type record at {slot} points at {at}, outside the image"),
                );
                continue;
            }
            if let Some(t) = nominal_type(img, at, warnings) {
                out.push(t);
            }
        }
    }
    out
}

/// One type context descriptor.
fn nominal_type(img: &Image<'_>, at: Addr, warnings: &mut Vec<String>) -> Option<SwiftType> {
    let flags = img.u32(at)?;
    let kind = ContextKind::from_flags(flags);
    if !kind.is_type() {
        warn(
            warnings,
            format!(
                "swift: the descriptor at {at} is a {} rather than a nominal type",
                kind.as_str()
            ),
        );
        return None;
    }
    let name = context_name(img, at)?;
    let accessor = relative(img, at.checked_add(12)?)
        .filter(|a| img.obj().section_at(*a).is_some_and(|s| s.exec));
    if accessor.is_none() && relative(img, at.checked_add(12)?).is_some() {
        warn(
            warnings,
            format!("swift: the metadata accessor of {name} is not in executable memory"),
        );
    }
    let field_descriptor = relative(img, at.checked_add(16)?).filter(|p| in_image(img.obj(), *p));
    Some(SwiftType {
        addr: at,
        kind,
        qualified_name: qualified(img, at, &name),
        name,
        accessor,
        field_descriptor,
    })
}

/// The name a context descriptor carries, which sits at the same offset for
/// every kind that has one.
fn context_name(img: &Image<'_>, at: Addr) -> Option<String> {
    let name_at = relative(img, at.checked_add(8)?)?;
    Some(img.cstr(name_at, MAX_NAME)?.to_string())
}

/// A name with its parent contexts, module first.
///
/// The chain is followed at most eight deep: a parent pointer is a number
/// from the file and can point back at its own child.
fn qualified(img: &Image<'_>, at: Addr, name: &str) -> String {
    let mut parts = vec![name.to_string()];
    let mut current = at;
    for _ in 0..8 {
        let Some(parent) = current
            .checked_add(4)
            .and_then(|p| relative_indirect(img, p))
            .filter(|p| *p != current && in_image(img.obj(), *p))
        else {
            break;
        };
        let Some(flags) = img.u32(parent) else { break };
        // Only the kinds whose descriptor carries a plain name at that offset
        // contribute one. An extension keeps a mangled type name there and an
        // anonymous context keeps nothing, so both end the chain rather than
        // spelling their bytes as an identifier.
        if !matches!(
            ContextKind::from_flags(flags),
            ContextKind::Module
                | ContextKind::Protocol
                | ContextKind::Class
                | ContextKind::Struct
                | ContextKind::Enum
        ) {
            break;
        }
        match context_name(img, parent) {
            Some(n) => parts.push(n),
            None => break,
        }
        current = parent;
    }
    parts.reverse();
    parts.join(".")
}

/// Every protocol conformance record.
fn conformances(img: &Image<'_>, warnings: &mut Vec<String>) -> Vec<Conformance> {
    let mut out = Vec::new();
    for s in sections(img.obj(), "__swift5_proto", "swift5_protocol_conformances") {
        let Some((start, bytes)) = body(img, s) else {
            continue;
        };
        for i in 0..bytes.len() as u64 / 4 {
            let Some(slot) = start.checked_add(i * 4) else {
                break;
            };
            let Some(at) = relative(img, slot) else {
                continue;
            };
            if !in_image(img.obj(), at) {
                warn(
                    warnings,
                    format!("swift: the conformance record at {slot} points outside the image"),
                );
                continue;
            }
            if let Some(c) = conformance(img, at) {
                out.push(c);
            }
        }
    }
    out
}

/// One `ProtocolConformanceDescriptor`.
fn conformance(img: &Image<'_>, at: Addr) -> Option<Conformance> {
    let flags = img.u32(at.checked_add(12)?)?;
    let type_reference = TypeReference::from_flags(flags);
    let protocol_descriptor = relative_indirect(img, at).filter(|p| in_image(img.obj(), *p));
    let protocol_name = protocol_descriptor.and_then(|p| context_name(img, p));

    let reference = at.checked_add(4)?;
    let (type_descriptor, type_name) = match type_reference {
        TypeReference::DirectDescriptor => {
            let d = relative(img, reference).filter(|p| in_image(img.obj(), *p));
            (d, d.and_then(|d| context_name(img, d)))
        }
        TypeReference::IndirectDescriptor => {
            let d = relative(img, reference)
                .and_then(|p| img.ptr(p))
                .filter(|p| *p != Addr::ZERO && in_image(img.obj(), *p));
            (d, d.and_then(|d| context_name(img, d)))
        }
        TypeReference::DirectObjcClassName => {
            let n = relative(img, reference).and_then(|p| img.cstr(p, MAX_NAME));
            (None, n.map(str::to_string))
        }
        // The indirect form reaches a class object, whose name lives behind
        // the Objective-C class layout rather than in this record.
        TypeReference::IndirectObjcClass | TypeReference::Other(_) => (None, None),
    };

    Some(Conformance {
        addr: at,
        protocol_descriptor,
        protocol_name,
        type_reference,
        type_descriptor,
        type_name,
        witness_table: relative(img, at.checked_add(8)?),
        retroactive: flags & CONFORMANCE_RETROACTIVE != 0,
        conditional_requirements: (flags >> 8) & 0xff,
    })
}

/// Every protocol descriptor the image defines.
fn protocols(img: &Image<'_>, warnings: &mut Vec<String>) -> Vec<SwiftProtocol> {
    let mut out = Vec::new();
    for s in sections(img.obj(), "__swift5_protos", "swift5_protocols") {
        let Some((start, bytes)) = body(img, s) else {
            continue;
        };
        for i in 0..bytes.len() as u64 / 4 {
            let Some(slot) = start.checked_add(i * 4) else {
                break;
            };
            let Some(at) = relative_indirect(img, slot).filter(|p| in_image(img.obj(), *p)) else {
                continue;
            };
            let Some(flags) = img.u32(at) else { continue };
            if ContextKind::from_flags(flags) != ContextKind::Protocol {
                warn(
                    warnings,
                    format!("swift: the protocol record at {slot} does not describe a protocol"),
                );
                continue;
            }
            let Some(name) = context_name(img, at) else {
                continue;
            };
            out.push(SwiftProtocol {
                addr: at,
                qualified_name: qualified(img, at, &name),
                name,
                requirements: at
                    .checked_add(16)
                    .and_then(|p| img.u32(p))
                    .unwrap_or_default(),
            });
        }
    }
    out
}

/// `MangledTypeName`, `Superclass`, `Kind`, `FieldRecordSize`, `NumFields`.
const FIELD_DESCRIPTOR_SIZE: u64 = 16;
/// `Flags`, `MangledTypeName`, `FieldName`.
const FIELD_RECORD_SIZE: u64 = 12;

const FIELD_INDIRECT_CASE: u32 = 0x1;
const FIELD_VAR: u32 = 0x2;
const FIELD_ARTIFICIAL: u32 = 0x4;

const CONFORMANCE_RETROACTIVE: u32 = 0x1 << 6;
