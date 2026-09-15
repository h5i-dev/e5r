//! C++ classes: the hierarchy, the constructors and destructors, and `this`.
//!
//! [`crate::vtables`] finds the tables. A table on its own is a list of
//! function pointers with an address for a name; it says nothing about what a
//! class inherits from, which of its functions build an object and which tear
//! one down, or what the first argument of any of them points at. This module
//! answers those three, and says for each answer what it rests on.
//!
//! The Itanium C++ ABI publishes the layout this reads. A virtual table's
//! second word points at a `std::type_info` derived object whose own first
//! word names one of `__class_type_info`, `__si_class_type_info` or
//! `__vmi_class_type_info`; the second points at the mangled type name; and
//! what follows gives the direct bases with their offsets and access flags.
//! Read that and a list of tables becomes a class hierarchy.
//!
//! Nothing here invents a name or a field. A class name out of the type
//! information is proven, and so is one out of a mangled symbol. A constructor
//! recognized by the vtable pointer it writes is inferred, and so is the type
//! of a `this` that only a vtable slot argued for. A binary built with
//! `-fno-rtti` has no type information to read, and [`Classes::rtti`] says so
//! rather than letting the vtable-only answer pass for the full one.

use std::collections::{BTreeMap, BTreeSet};

use e5r_analysis::Program;
use e5r_core::{Addr, Bits, Endian, Strength};
use e5r_ir::op::{Op, Space};
use e5r_ir::ssa::{Location, Operand, SsaFunction, SsaKind, Value};

use crate::vtables::{VTable, vtables};

/// What a recovered fact about a class rests on.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum Basis {
    /// The Itanium type information, identified by the ABI's own symbols. The
    /// compiler wrote the class name, the bases and their offsets down in a
    /// structure the ABI defines and the runtime reads.
    Rtti,
    /// A mangled symbol name: `_ZTV` for a table, `_ZTI` for type information,
    /// `C1` or `D0` for what a member function is.
    MangledName,
    /// Type information whose kind was decided by its shape, because the ABI's
    /// own `__class_type_info` symbols are not in this binary to compare
    /// against. The structure is the ABI's; which of the three it is, is a
    /// conclusion.
    RttiShape,
    /// A slot in a virtual table. The first argument of a function reached
    /// through a class's table is that class, by the ABI; that the function is
    /// a member of exactly this class is the step past what is written down.
    VtableSlot,
    /// The function writes a known vtable pointer into what its first argument
    /// points at, which is what a constructor and a destructor both do.
    VptrStore,
    /// The offsets and widths the code touched through the pointer.
    Accesses,
}

impl Basis {
    /// The phrase it prints as.
    pub fn as_str(self) -> &'static str {
        match self {
            Basis::Rtti => "RTTI",
            Basis::MangledName => "mangled name",
            Basis::RttiShape => "RTTI structure",
            Basis::VtableSlot => "vtable slot",
            Basis::VptrStore => "vtable pointer store",
            Basis::Accesses => "accesses through the pointer",
        }
    }

    /// How strongly a fact resting on this is known.
    pub fn strength(self) -> Strength {
        match self {
            // Written down by the compiler in a structure the ABI defines, and
            // named by a symbol. Reading it back is not a guess.
            Basis::Rtti | Basis::MangledName => Strength::Proven,
            // Everything else is a conclusion drawn from what the code does.
            Basis::RttiShape | Basis::VtableSlot | Basis::VptrStore | Basis::Accesses => {
                Strength::Inferred
            }
        }
    }
}

/// Which of the three Itanium type-information classes an object is.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum TypeInfoKind {
    /// `__class_type_info`: no bases.
    Class,
    /// `__si_class_type_info`: one public, non-virtual base at offset zero.
    SingleInheritance,
    /// `__vmi_class_type_info`: anything else, with an explicit base array.
    MultipleInheritance,
}

impl TypeInfoKind {
    /// The ABI's name for it.
    pub fn as_str(self) -> &'static str {
        match self {
            TypeInfoKind::Class => "__class_type_info",
            TypeInfoKind::SingleInheritance => "__si_class_type_info",
            TypeInfoKind::MultipleInheritance => "__vmi_class_type_info",
        }
    }
}

/// One direct base class, as the type information records it.
#[derive(Debug, Clone)]
pub struct BaseClass {
    /// The base's name, demangled.
    pub name: String,
    /// Where the base's type information lives.
    pub typeinfo: Addr,
    /// For an ordinary base, the byte offset of its subobject inside the
    /// derived object. For a virtual base this is not that: the ABI stores the
    /// offset into the virtual table at which the base's real offset is found,
    /// because a virtual base moves depending on the complete object.
    pub offset: i64,
    /// True when the base is inherited virtually, and `offset` is a table
    /// offset rather than an object offset.
    pub is_virtual: bool,
    /// True when the inheritance is public.
    pub is_public: bool,
    /// What this rests on.
    pub basis: Basis,
}

/// One place in an object that the code touched.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Field {
    /// Byte offset from the start of the object.
    pub offset: i64,
    /// The widest access seen there.
    pub size: u8,
    /// True when anything wrote it.
    pub written: bool,
    /// What this rests on.
    pub basis: Basis,
}

/// The first argument of a member function, and what it points at.
#[derive(Debug, Clone)]
pub struct This {
    /// The class it points at.
    pub class: String,
    /// How C++ spells the declaration.
    pub declaration: String,
    /// The offsets the function touched through it.
    pub fields: Vec<Field>,
    /// What the typing rests on.
    pub basis: Basis,
}

/// What a member function does for its class.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Role {
    /// Builds an object: writes the class's vtable pointer into it and is in
    /// no table itself.
    Constructor,
    /// Tears one down.
    Destructor,
    /// Tears one down and frees the storage. Under Itanium this is the second
    /// of the two destructor slots a table carries.
    DeletingDestructor,
    /// A virtual function that is neither.
    Virtual,
    /// A thunk: the compiler's adjustment of `this` on the way to the real
    /// function, which a secondary table's slots point at.
    Thunk,
    /// A member function that is in no table.
    Method,
}

impl Role {
    /// The phrase it prints as.
    pub fn as_str(self) -> &'static str {
        match self {
            Role::Constructor => "constructor",
            Role::Destructor => "destructor",
            Role::DeletingDestructor => "deleting destructor",
            Role::Virtual => "virtual function",
            Role::Thunk => "thunk",
            Role::Method => "method",
        }
    }
}

/// One function that belongs to a class.
#[derive(Debug, Clone)]
pub struct Member {
    /// Where it starts.
    pub addr: Addr,
    /// The class it belongs to.
    pub class: String,
    /// Its name, demangled, when a symbol gave one.
    pub name: Option<String>,
    /// What it does for the class.
    pub role: Role,
    /// Which table slot it occupies, when it occupies one.
    pub slot: Option<usize>,
    /// What the role rests on.
    pub basis: Basis,
    /// Its first argument, when the class is known well enough to type it.
    pub this: Option<This>,
}

/// A class, and everything found about it.
#[derive(Debug, Clone)]
pub struct Class {
    /// Its name, when anything named it. A stripped binary with no type
    /// information has tables whose class nothing names, and inventing a name
    /// for one would be a claim.
    pub name: Option<String>,
    /// The mangled name the type information carries, which is what `c++filt`
    /// is handed.
    pub mangled: Option<String>,
    /// Where its type information lives.
    pub typeinfo: Option<Addr>,
    /// Which of the three type-information classes it is.
    pub kind: Option<TypeInfoKind>,
    /// Its direct bases, in the order the type information lists them.
    pub bases: Vec<BaseClass>,
    /// Its virtual tables, primary first.
    pub vtables: Vec<Addr>,
    /// Its member functions.
    pub members: Vec<Member>,
    /// The offsets its member functions touch through `this`.
    pub fields: Vec<Field>,
    /// What the class itself rests on.
    pub basis: Basis,
}

impl Class {
    /// A name for output: the class's own, or where its first table is.
    pub fn display_name(&self) -> String {
        match (&self.name, self.vtables.first()) {
            (Some(name), _) => name.clone(),
            (None, Some(at)) => format!("class with a vtable at {at}"),
            (None, None) => "anonymous class".to_string(),
        }
    }

    /// Its constructors.
    pub fn constructors(&self) -> impl Iterator<Item = &Member> {
        self.members.iter().filter(|m| m.role == Role::Constructor)
    }

    /// Its destructors, of both kinds.
    pub fn destructors(&self) -> impl Iterator<Item = &Member> {
        self.members
            .iter()
            .filter(|m| matches!(m.role, Role::Destructor | Role::DeletingDestructor))
    }

    /// How big the object is, as far as anything said: past the last field
    /// touched, or past the last non-virtual base, whichever is further.
    pub fn size(&self) -> Option<u64> {
        let fields = self
            .fields
            .iter()
            .filter(|f| f.offset >= 0)
            .map(|f| f.offset as u64 + f.size as u64);
        let bases = self
            .bases
            .iter()
            .filter(|b| !b.is_virtual && b.offset >= 0)
            .map(|b| b.offset as u64);
        fields.chain(bases).max()
    }
}

/// Which C++ ABI the recovered classes are in.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Abi {
    /// The Itanium C++ ABI: GCC, Clang, and everything but MSVC.
    Itanium,
    /// The Microsoft C++ ABI.
    Msvc,
    /// Nothing said, because nothing was found.
    Unknown,
}

impl Abi {
    /// The phrase it prints as.
    pub fn as_str(self) -> &'static str {
        match self {
            Abi::Itanium => "Itanium",
            Abi::Msvc => "MSVC",
            Abi::Unknown => "unknown",
        }
    }
}

/// Whether the binary carries type information at all.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Rtti {
    /// Type information was found and read, so the hierarchy is the compiler's
    /// own record of it.
    Present,
    /// There are virtual tables but none of them points at type information:
    /// the binary was built with `-fno-rtti`. What comes back is the
    /// vtable-only answer, with no bases and no inheritance offsets, because
    /// there is nothing in the file that says what they are.
    Absent,
    /// No virtual tables, so nothing to say.
    NoClasses,
}

impl Rtti {
    /// The phrase it prints as.
    pub fn as_str(self) -> &'static str {
        match self {
            Rtti::Present => "present",
            Rtti::Absent => "absent (-fno-rtti): vtables only, no hierarchy",
            Rtti::NoClasses => "no classes",
        }
    }
}

/// Every class the program appears to contain, with the counts that say how
/// much of the answer came from where.
#[derive(Debug, Clone)]
pub struct Classes {
    /// The classes, by name where they have one and by address where they do
    /// not.
    pub classes: Vec<Class>,
    /// Whether type information was there to read.
    pub rtti: Rtti,
    /// Which ABI the type information is in.
    pub abi: Abi,
    /// How many virtual tables were found.
    pub tables: usize,
    /// How many of them a `_ZTV` symbol named.
    pub named_by_symbol: usize,
    /// How many of them only the type information named, which is what RTTI
    /// buys over the tables alone.
    pub named_by_rtti: usize,
}

/// What to spend time on.
#[derive(Debug, Clone)]
pub struct Options {
    /// Identify constructors and destructors by what they write rather than
    /// only by their names, so a stripped binary still gets them. This builds
    /// SSA for every function that mentions a virtual table.
    pub stores: bool,
    /// Recover what each member function touches through `this`. This builds
    /// SSA for every member function, which is the expensive part.
    pub fields: bool,
}

impl Default for Options {
    fn default() -> Options {
        Options {
            stores: true,
            fields: true,
        }
    }
}

/// Every class the program appears to contain.
pub fn classes(p: &Program) -> Classes {
    classes_with(p, &Options::default())
}

/// Every class the program appears to contain, doing only the work asked for.
pub fn classes_with(p: &Program, opts: &Options) -> Classes {
    let tables = vtables(p);
    let abi = abi_type_info_vtables(p);

    // Every type-information object anything points at, plus every one a
    // symbol names outright. A class with no virtual functions has no table,
    // but if it is a base of one that has, its type information is still here.
    let mut candidates: BTreeSet<Addr> = tables.iter().filter_map(|t| t.typeinfo).collect();
    for s in &p.object.symbols {
        if s.name.starts_with("_ZTI") && s.addr != Addr::ZERO {
            candidates.insert(s.addr);
        }
    }
    // Bases pull in type information nothing else pointed at, so keep reading
    // until the set stops growing.
    let mut infos: BTreeMap<Addr, TypeInfo> = BTreeMap::new();
    let mut queue: Vec<Addr> = candidates.iter().copied().collect();
    while let Some(at) = queue.pop() {
        if infos.contains_key(&at) {
            continue;
        }
        let Some(info) = read_type_info(p, &abi, at) else {
            continue;
        };
        for b in &info.bases {
            if !infos.contains_key(&b.typeinfo) {
                queue.push(b.typeinfo);
            }
        }
        infos.insert(at, info);
    }

    // The Microsoft layout, where the Itanium one found nothing. A PE has its
    // type information in a different shape and reached through relative
    // addresses, and a binary is one or the other, never both.
    let mut abi = if infos.is_empty() {
        Abi::Unknown
    } else {
        Abi::Itanium
    };
    let mut tables = tables;
    if infos.is_empty() {
        let found = crate::msvc::read(p);
        if !found.infos.is_empty() {
            abi = Abi::Msvc;
            infos = found.infos;
            let known: BTreeSet<u64> = tables.iter().map(|t| t.addr.get()).collect();
            tables.extend(
                found
                    .tables
                    .into_iter()
                    .filter(|t| !known.contains(&t.addr.get())),
            );
            tables.sort_by_key(|t| t.addr);
            tables.dedup_by_key(|t| t.addr);
        }
    }

    let rtti = if !infos.is_empty() {
        Rtti::Present
    } else if tables.is_empty() {
        Rtti::NoClasses
    } else {
        Rtti::Absent
    };

    // Type information finds tables the scan cannot. A sub-table with two
    // slots is under the length a run of pointers has to reach before it is a
    // table by itself, and a class that overrides nothing but its destructor
    // has exactly that; so does every secondary sub-table of a class with
    // virtual bases. A pair of words followed by a function, where the second
    // word is type information this program defines, is a table whatever its
    // length, because nothing else is shaped that way.
    let known: BTreeSet<u64> = tables.iter().map(|t| t.addr.get()).collect();
    for t in tables_from_type_info(p, &infos) {
        if !known.contains(&t.addr.get()) {
            tables.push(t);
        }
    }
    tables.sort_by_key(|t| t.addr);
    tables.dedup_by_key(|t| t.addr);

    let mut built = build_classes(&tables, &infos);
    attribute_members(p, opts, &tables, &mut built);

    let named_by_symbol = tables.iter().filter(|t| t.class.is_some()).count();
    let named_by_rtti = tables
        .iter()
        .filter(|t| t.class.is_none())
        .filter(|t| t.typeinfo.and_then(|a| infos.get(&a)).is_some())
        .count();

    Classes {
        classes: built,
        rtti,
        abi,
        tables: tables.len(),
        named_by_symbol,
        named_by_rtti,
    }
}

/// Every virtual table whose type-information word names a class this program
/// defines.
///
/// The scan in [`crate::vtables`] needs a run of function pointers long enough
/// to be a table rather than a coincidence. This needs no length at all,
/// because the type information is the evidence: two words followed by one
/// function, where the second word points at type information already read, is
/// a table.
fn tables_from_type_info(p: &Program, infos: &BTreeMap<Addr, TypeInfo>) -> Vec<VTable> {
    let w = word_size(p) as i64;
    let mut out = Vec::new();
    for section in &p.object.sections {
        // The sections a compiler puts tables in, which is where the scan
        // looks too.
        if !(section.name.starts_with(".data.rel.ro")
            || section.name == ".rodata"
            || section.name == ".data")
            || section.range.is_empty()
        {
            continue;
        }
        let mut at = section.range.start();
        while at.get() + 3 * w as u64 <= section.range.end().get() {
            let step = at;
            at = at.wrapping_offset(w);
            let Some(offset_to_top) = word(p, step) else {
                continue;
            };
            let Some(typeinfo) = word(p, step.wrapping_offset(w)) else {
                continue;
            };
            if !infos.contains_key(&Addr(typeinfo)) {
                continue;
            }
            let entry = step.wrapping_offset(2 * w);
            let mut methods = Vec::new();
            let mut slot = entry;
            while let Some(target) = word(p, slot) {
                if !is_code(p, Addr(target)) {
                    break;
                }
                methods.push(Addr(target));
                slot = slot.wrapping_offset(w);
            }
            if methods.is_empty() {
                continue;
            }
            at = slot;
            out.push(VTable {
                addr: step,
                entry,
                class: None,
                offset_to_top: offset_to_top as i64,
                typeinfo: Some(Addr(typeinfo)),
                methods,
                // The tables `vtables` found say where they came from. These
                // rest on the type information, which is not a kind the core
                // evidence list has a name for yet; a pointer in data is the
                // nearest true thing it can say.
                evidence: e5r_core::Evidence::DataPointer,
            });
        }
    }
    out
}

/// True when an address is inside something the container marked executable.
pub(crate) fn is_code(p: &Program, at: Addr) -> bool {
    at != Addr::ZERO
        && p.object
            .sections
            .iter()
            .any(|s| s.exec && s.range.contains(at))
}

/// One type-information object, read.
#[derive(Debug, Clone)]
pub(crate) struct TypeInfo {
    pub(crate) name: String,
    pub(crate) mangled: String,
    /// Which of the three Itanium type-information classes it is. The
    /// Microsoft layout has no such division, and leaves this empty.
    pub(crate) kind: Option<TypeInfoKind>,
    pub(crate) bases: Vec<BaseClass>,
    pub(crate) basis: Basis,
}

/// Where the ABI's three type-information class vtables are, when the symbols
/// for them are in this file.
///
/// A type-information object's first word points sixteen bytes into one of
/// them, which is what says which of the three it is. These are the names the
/// Itanium ABI gives them, and they are what `libstdc++` exports.
fn abi_type_info_vtables(p: &Program) -> BTreeMap<u64, TypeInfoKind> {
    let w = word_size(p);
    let mut out = BTreeMap::new();
    for s in &p.object.symbols {
        let kind = match s.name.as_str() {
            "_ZTVN10__cxxabiv117__class_type_infoE" => TypeInfoKind::Class,
            "_ZTVN10__cxxabiv120__si_class_type_infoE" => TypeInfoKind::SingleInheritance,
            "_ZTVN10__cxxabiv121__vmi_class_type_infoE" => TypeInfoKind::MultipleInheritance,
            _ => continue,
        };
        if s.addr != Addr::ZERO {
            out.insert(s.addr.get().wrapping_add(2 * w), kind);
        }
    }
    out
}

/// Read one type-information object.
fn read_type_info(p: &Program, abi: &BTreeMap<u64, TypeInfoKind>, at: Addr) -> Option<TypeInfo> {
    let w = word_size(p);
    let vptr = word(p, at)?;
    let name_at = Addr(word(p, at.wrapping_offset(w as i64))?);
    let mangled = mangled_name(p, name_at)?;
    let name = demangle_type_name(&mangled)?;

    // Which of the three it is. The ABI's own symbols settle it outright; with
    // them stripped, the structure has to.
    let (kind, basis) = match abi.get(&vptr) {
        Some(kind) => (*kind, Basis::Rtti),
        None => (kind_by_shape(p, at)?, Basis::RttiShape),
    };

    let mut bases = Vec::new();
    match kind {
        TypeInfoKind::Class => {}
        TypeInfoKind::SingleInheritance => {
            // One public base at offset zero, and the ABI stores nothing else
            // because there is nothing else to store.
            let base = Addr(word(p, at.wrapping_offset(2 * w as i64))?);
            bases.push(BaseClass {
                name: base_name(p, base)?,
                typeinfo: base,
                offset: 0,
                is_virtual: false,
                is_public: true,
                basis,
            });
        }
        TypeInfoKind::MultipleInheritance => {
            // `__flags` then `__base_count`, both 32 bits, then one
            // `__base_class_type_info` per direct base.
            let count = read_int(p, at.wrapping_offset(2 * w as i64 + 4), 4)? as u32;
            // An entry is a pointer and a word of packed offset and flags, so
            // a count that does not fit in the file is not a count.
            if count == 0 || count > 4096 {
                return None;
            }
            let array = at.wrapping_offset(2 * w as i64 + 8);
            for i in 0..count as i64 {
                let entry = array.wrapping_offset(i * 2 * w as i64);
                let base = Addr(word(p, entry)?);
                let flags = word(p, entry.wrapping_offset(w as i64))? as i64;
                bases.push(BaseClass {
                    name: base_name(p, base)?,
                    typeinfo: base,
                    // The low byte is the flags; the rest is a signed offset.
                    offset: flags >> 8,
                    is_virtual: flags & 1 != 0,
                    is_public: flags & 2 != 0,
                    basis,
                });
            }
        }
    }

    Some(TypeInfo {
        name,
        mangled,
        kind: Some(kind),
        bases,
        basis,
    })
}

/// Which type-information class an object is, decided by its shape.
///
/// Used only when the ABI's own vtable symbols are not in the file. The three
/// layouts are distinguishable: a single-inheritance object's third word
/// points at another type-information object, a many-bases object's third word
/// is a pair of packed 32-bit counts followed by that many base entries, and
/// anything else has no bases at all.
fn kind_by_shape(p: &Program, at: Addr) -> Option<TypeInfoKind> {
    let w = word_size(p);
    let third = at.wrapping_offset(2 * w as i64);
    if let Some(v) = word(p, third)
        && looks_like_type_info(p, Addr(v))
    {
        return Some(TypeInfoKind::SingleInheritance);
    }
    // A plausible base array: a small count, and every entry pointing at
    // something that is itself type information.
    if let Some(raw) = read_int(p, third.wrapping_offset(4), 4) {
        let count = raw as u32;
        if count > 0 && count <= 64 {
            let array = third.wrapping_offset(8);
            let ok = (0..count as i64).all(|i| {
                word(p, array.wrapping_offset(i * 2 * w as i64))
                    .is_some_and(|v| looks_like_type_info(p, Addr(v)))
            });
            if ok {
                return Some(TypeInfoKind::MultipleInheritance);
            }
        }
    }
    Some(TypeInfoKind::Class)
}

/// Whether an address holds something shaped like type information.
///
/// A base entry points at another type-information object, and in a binary
/// with no symbols there is nothing to check that against except the layout
/// itself: the second word has to point at a mangled name the demangler
/// accepts. Two words that happen to do that by accident is the false
/// positive this admits, and it has not been seen.
fn looks_like_type_info(p: &Program, at: Addr) -> bool {
    if at == Addr::ZERO {
        return false;
    }
    let Some(w) = word(p, at.wrapping_offset(word_size(p) as i64)) else {
        return false;
    };
    mangled_name(p, Addr(w))
        .as_deref()
        .and_then(demangle_type_name)
        .is_some()
}

/// The mangled type name a type-information object points at.
fn mangled_name(p: &Program, at: Addr) -> Option<String> {
    if at == Addr::ZERO {
        return None;
    }
    let window = p.object.memory.decode_window(at, 1024)?;
    let end = window.iter().position(|b| *b == 0)?;
    let text = window.get(..end)?;
    // A mangled name is ASCII and never empty. Anything else means the word
    // was not a name pointer and this is not type information.
    if text.is_empty() || !text.iter().all(|b| b.is_ascii_graphic()) {
        return None;
    }
    String::from_utf8(text.to_vec()).ok()
}

/// A class name from the mangled type name the ABI stores.
///
/// The stored name is the class's own mangled name with no prefix, so putting
/// the type-information prefix back on it gives the demangler something it
/// recognizes, nested names and templates included.
fn demangle_type_name(mangled: &str) -> Option<String> {
    let (_, text) = e5r_types::demangle(&format!("_ZTI{mangled}"))?;
    Some(text.strip_prefix("typeinfo for ")?.to_string())
}

/// The name of the class a base entry points at.
fn base_name(p: &Program, at: Addr) -> Option<String> {
    let w = word_size(p);
    let name_at = Addr(word(p, at.wrapping_offset(w as i64))?);
    demangle_type_name(&mangled_name(p, name_at)?)
}

pub(crate) fn word_size(p: &Program) -> u64 {
    match p.object.bits {
        Bits::Bits64 => 8,
        _ => 4,
    }
}

pub(crate) fn word(p: &Program, at: Addr) -> Option<u64> {
    read_int(p, at, word_size(p))
}

pub(crate) fn read_int(p: &Program, at: Addr, bytes: u64) -> Option<u64> {
    p.object
        .memory
        .read_ptr(at, bytes, p.object.endian == Endian::Little)
        .ok()
}

/// Turn the tables and the type information into classes.
fn build_classes(tables: &[VTable], infos: &BTreeMap<Addr, TypeInfo>) -> Vec<Class> {
    // A class is keyed by its name when anything named it, and by the address
    // of its first table when nothing did.
    let mut by_key: BTreeMap<String, usize> = BTreeMap::new();
    let mut out: Vec<Class> = Vec::new();

    let mut place = |key: String, seed: Class, out: &mut Vec<Class>| -> usize {
        match by_key.get(&key) {
            Some(i) => *i,
            None => {
                by_key.insert(key, out.len());
                out.push(seed);
                out.len() - 1
            }
        }
    };

    // Type information first: it is the strongest thing here, and it exists
    // for classes that have no table of their own.
    let mut info_index: BTreeMap<Addr, usize> = BTreeMap::new();
    for (at, info) in infos {
        let i = place(
            info.name.clone(),
            Class {
                name: Some(info.name.clone()),
                mangled: Some(info.mangled.clone()),
                typeinfo: Some(*at),
                kind: info.kind,
                bases: info.bases.clone(),
                vtables: Vec::new(),
                members: Vec::new(),
                fields: Vec::new(),
                basis: info.basis,
            },
            &mut out,
        );
        info_index.insert(*at, i);
    }

    for t in tables {
        // The type information names the class outright. Failing that, a
        // `_ZTV` symbol does. Failing both, the table is all there is.
        let i = match t.typeinfo.and_then(|a| info_index.get(&a)) {
            Some(i) => *i,
            None => {
                let key = t
                    .class
                    .clone()
                    .unwrap_or_else(|| format!("@{:#x}", t.addr.get()));
                let seed = Class {
                    name: t.class.clone(),
                    mangled: None,
                    typeinfo: t.typeinfo,
                    kind: None,
                    bases: Vec::new(),
                    vtables: Vec::new(),
                    members: Vec::new(),
                    fields: Vec::new(),
                    basis: if t.class.is_some() {
                        Basis::MangledName
                    } else {
                        Basis::VtableSlot
                    },
                };
                place(key, seed, &mut out)
            }
        };
        out[i].vtables.push(t.addr);
    }

    // The primary table first: it is the one at offset zero from the top of
    // the object, and the one whose slots take a `this` of this class.
    for c in &mut out {
        c.vtables.sort();
    }
    out.sort_by(|a, b| {
        a.name
            .cmp(&b.name)
            .then(a.vtables.first().cmp(&b.vtables.first()))
    });
    out
}

/// Find the member functions of each class and say what each one does.
fn attribute_members(p: &Program, opts: &Options, tables: &[VTable], classes: &mut [Class]) {
    let mut index: BTreeMap<String, usize> = BTreeMap::new();
    for (i, c) in classes.iter().enumerate() {
        if let Some(name) = &c.name {
            index.insert(name.clone(), i);
        }
    }
    // Which class each table belongs to, and which table is its primary.
    let mut table_of: BTreeMap<u64, usize> = BTreeMap::new();
    for (i, c) in classes.iter().enumerate() {
        for t in &c.vtables {
            table_of.insert(t.get(), i);
        }
    }
    // Every address a vtable pointer can hold, the class it belongs to, and
    // how far into that class's objects the subobject it serves begins. The
    // second number is what tells a base's pointer from a member's.
    let mut vptr_class: BTreeMap<u64, (usize, i64)> = BTreeMap::new();
    // Every function any table reaches. A constructor is never one of these,
    // because a table holds virtual functions and a constructor is not one.
    let mut dispatched: BTreeSet<u64> = BTreeSet::new();
    for t in tables {
        if let Some(i) = table_of.get(&t.addr.get()) {
            vptr_class.insert(t.entry.get(), (*i, -t.offset_to_top));
        }
        dispatched.extend(t.methods.iter().map(|m| m.get()));
    }

    // What each function is, best evidence first. A later weaker claim never
    // overwrites an earlier stronger one.
    let mut found: BTreeMap<u64, Member> = BTreeMap::new();

    // 1. The symbols. A mangled member-function name says the class and says
    // whether the function is a constructor or a destructor, and which of the
    // several the ABI emits per class it is.
    for s in &p.object.symbols {
        if !s.is_defined_function() || s.addr == Addr::ZERO {
            continue;
        }
        let Some(m) = member_from_symbol(&s.name, s.addr) else {
            continue;
        };
        if !index.contains_key(&m.class) {
            continue;
        }
        found.insert(s.addr.get(), m);
    }

    // 2. The tables. A slot of a primary table is a virtual function of that
    // class, and the first two slots of a class with a virtual destructor are
    // the complete and the deleting destructor, in that order.
    for t in tables {
        let Some(i) = table_of.get(&t.addr.get()) else {
            continue;
        };
        let Some(name) = classes[*i].name.clone() else {
            continue;
        };
        // Only the primary table types a plain `this`: a secondary table's
        // slots are entered with a pointer to the subobject, not to the
        // complete object, and calling that a `this` of the class would be
        // wrong by exactly the offset to the top.
        let primary = t.offset_to_top == 0;
        for (slot, target) in t.methods.iter().enumerate() {
            if *target == Addr::ZERO {
                continue;
            }
            if let Some(m) = found.get_mut(&target.get()) {
                // Already known from a name, which outranks a slot. Record
                // where it sits, which the name does not say.
                if m.slot.is_none() && primary {
                    m.slot = Some(slot);
                }
                continue;
            }
            if !primary {
                continue;
            }
            found.insert(
                target.get(),
                Member {
                    addr: *target,
                    class: name.clone(),
                    name: p.name_of(*target).map(|n| e5r_types::pretty(&n)),
                    role: Role::Virtual,
                    slot: Some(slot),
                    basis: Basis::VtableSlot,
                    this: None,
                },
            );
        }
    }

    // 3. What the code does. A function that writes a class's vtable pointer
    // into what its first argument points at is building or tearing down an
    // object of that class.
    //
    // Which store counts is the whole question, and the answer is the one the
    // ABI states: offset zero of the object, holding a table whose own
    // subobject begins at offset zero, which is the complete object's own
    // pointer. A store anywhere else belongs to a subobject, and a subobject
    // is either a base this function is not a member of or a member variable
    // of another class entirely: `~basic_ofstream` sets its `basic_filebuf`
    // member's primary pointer eight bytes in, and eighteen functions in
    // `libstdc++` came back a constructor of the wrong class because a store
    // like that was read as a claim about the function.
    let descends = descendants(classes);
    if opts.stores {
        for (at, writes) in vptr_writers(p, tables) {
            // In the order the code performs them, which is what separates
            // building from tearing down when more than one is written.
            let mut built: Vec<usize> = writes
                .iter()
                .filter(|(offset, _)| *offset == 0)
                .filter_map(|(_, table)| {
                    let (i, begins) = vptr_class.get(&table.get()).copied()?;
                    (begins == 0).then_some(i)
                })
                .collect();
            built.dedup();
            // The complete object's class: the one of those that is not a base
            // of any other. A constructor writes its bases' pointers before
            // its own and a destructor writes them after, so taking the most
            // derived rather than the first or the last is right either way.
            let Some(i) = built
                .iter()
                .find(|i| !built.iter().any(|j| descends(*j, **i)))
                .copied()
            else {
                continue;
            };
            let Some(name) = classes[i].name.clone() else {
                continue;
            };
            let slot = found.get(&at.get()).and_then(|m| m.slot);
            // Which of the two it is. A function that writes the pointer of
            // this class and of classes it inherits from has its base
            // constructors or base destructors inlined into it, and the order
            // settles it outright: an object is built from the base up and torn
            // down from the derived end, so the complete object's own pointer
            // goes in last when building and first when tearing down. The
            // others have to be its bases for that to be the reading; two
            // unrelated classes written into the same object are a lattice this
            // does not understand, and it says nothing rather than guessing.
            //
            // Otherwise the tables decide: a constructor is never reached
            // through one, and a destructor of a class with a virtual
            // destructor is, at the first of the two slots the class spends on
            // destruction. What that cannot tell apart is a base-object
            // destructor of a class whose bases are not inlined: it writes the
            // pointer exactly as a constructor does and is in no table, so it
            // comes back a constructor.
            let inlined_bases = built.len() > 1 && built.iter().all(|j| *j == i || descends(i, *j));
            let tearing_down = if inlined_bases {
                built.first() == Some(&i)
            } else {
                dispatched.contains(&at.get())
            };
            let role = if !tearing_down {
                Role::Constructor
            } else {
                match slot {
                    Some(1) => Role::DeletingDestructor,
                    _ => Role::Destructor,
                }
            };
            match found.get_mut(&at.get()) {
                // A name already said what this is; the store corroborates it
                // and does not get to contradict it.
                Some(m) if m.basis.strength() >= Strength::Proven => {}
                Some(m) => {
                    m.role = role;
                    m.basis = Basis::VptrStore;
                }
                None => {
                    found.insert(
                        at.get(),
                        Member {
                            addr: at,
                            class: name,
                            name: p.name_of(at).map(|n| e5r_types::pretty(&n)),
                            role,
                            slot,
                            basis: Basis::VptrStore,
                            this: None,
                        },
                    );
                }
            }
        }
    }

    // 4. The second destructor slot. Under Itanium a class with a virtual
    // destructor spends two adjacent slots on it: the complete-object one
    // first and the deleting one second. The deleting one frees the storage
    // and usually writes no vtable pointer of its own, so nothing above
    // reaches it; but once the slot before it is known to be a destructor,
    // the ABI says what the slot after it is.
    for t in tables.iter().filter(|t| t.offset_to_top == 0) {
        let (Some(first), Some(second)) = (t.methods.first(), t.methods.get(1)) else {
            continue;
        };
        let complete = found
            .get(&first.get())
            .is_some_and(|m| m.role == Role::Destructor);
        if !complete || *second == Addr::ZERO || second == first {
            continue;
        }
        match found.get_mut(&second.get()) {
            Some(m) if m.basis.strength() >= Strength::Proven => {}
            Some(m) => {
                m.role = Role::DeletingDestructor;
                m.basis = Basis::VtableSlot;
            }
            None => {}
        }
    }

    // 5. `this`. The first argument of every one of these is the object, by
    // the ABI on both System V and MSVC, so once the class is known the
    // argument is typed and the offsets the code touches through it are the
    // class's fields.
    let mut members: Vec<Member> = found.into_values().collect();
    for m in &mut members {
        let fields = if opts.fields {
            this_fields(p, m.addr)
        } else {
            Vec::new()
        };
        m.this = Some(This {
            class: m.class.clone(),
            declaration: format!("{} *this", m.class),
            fields,
            // The class came from a name, or from the table the function is
            // in. The typing is never stronger than that.
            basis: match m.basis {
                Basis::MangledName => Basis::MangledName,
                other => other,
            },
        });
    }

    for m in members {
        let Some(i) = index.get(&m.class) else {
            continue;
        };
        classes[*i].members.push(m);
    }
    for c in classes.iter_mut() {
        c.members.sort_by_key(|m| m.addr);
        c.fields = merge_fields(&c.members);
    }
}

/// Which classes each one inherits from, transitively, by index.
///
/// The answer says "a descends from b", which is what decides the complete
/// object's class where a function writes several vtable pointers into the
/// same object: the one that is nobody else's base is the one being built or
/// destroyed. A hierarchy read out of a hostile file can name a cycle, so the
/// walk carries the set it has already seen.
fn descendants(classes: &[Class]) -> impl Fn(usize, usize) -> bool + use<> {
    let index: BTreeMap<&str, usize> = classes
        .iter()
        .enumerate()
        .filter_map(|(i, c)| c.name.as_deref().map(|n| (n, i)))
        .collect();
    let mut ancestors: BTreeMap<usize, BTreeSet<usize>> = BTreeMap::new();
    for i in 0..classes.len() {
        let mut seen = BTreeSet::new();
        let mut queue = vec![i];
        while let Some(at) = queue.pop() {
            for b in &classes[at].bases {
                let Some(j) = index.get(b.name.as_str()).copied() else {
                    continue;
                };
                if seen.insert(j) {
                    queue.push(j);
                }
            }
        }
        ancestors.insert(i, seen);
    }
    move |a, b| ancestors.get(&a).is_some_and(|set| set.contains(&b))
}

/// Union the fields every member saw, widest access per offset.
fn merge_fields(members: &[Member]) -> Vec<Field> {
    let mut widest: BTreeMap<i64, Field> = BTreeMap::new();
    for f in members
        .iter()
        .filter_map(|m| m.this.as_ref())
        .flat_map(|t| t.fields.iter())
    {
        let e = widest.entry(f.offset).or_insert(*f);
        e.size = e.size.max(f.size);
        e.written |= f.written;
    }
    widest.into_values().collect()
}

/// Read a member function's name and role out of a mangled symbol.
///
/// The demangled form says which class it belongs to and whether it is a
/// constructor or a destructor: `A::B::B()` builds, `A::B::~B()` tears down.
/// Which of the several the ABI emits per class it is comes from the mangled
/// form, because all three demangle to the same text.
fn member_from_symbol(symbol: &str, addr: Addr) -> Option<Member> {
    let (e5r_types::Scheme::Itanium, text) = e5r_types::demangle(symbol)? else {
        return None;
    };
    // A thunk adjusts `this` and jumps; it is not the member function, and
    // typing its argument as the complete object would be wrong by the
    // adjustment.
    if text.starts_with("non-virtual thunk to ") || text.starts_with("virtual thunk to ") {
        return Some(Member {
            addr,
            class: qualified(text.rsplit(" to ").next()?)?.0,
            name: Some(text.clone()),
            role: Role::Thunk,
            slot: None,
            basis: Basis::MangledName,
            this: None,
        });
    }
    let (class, last) = qualified(&text)?;
    // The class's own name, without what encloses it and without its template
    // arguments: `std::__cxx11::basic_string<char, ...>` is written
    // `basic_string` where it declares its own constructor. Splitting on `::`
    // has to skip the ones inside the argument list, or the name of a class
    // whose arguments are themselves qualified comes out as an argument.
    let short = simple_name(&class);
    let role = if last == format!("~{short}") {
        // `D0` is the deleting destructor, `D1` the complete one and `D2` the
        // base one. Only the first frees the storage.
        if symbol.contains("D0E") {
            Role::DeletingDestructor
        } else {
            Role::Destructor
        }
    } else if last == short {
        Role::Constructor
    } else {
        Role::Method
    };
    Some(Member {
        addr,
        class,
        name: Some(text),
        role,
        slot: None,
        basis: Basis::MangledName,
        this: None,
    })
}

/// Split a demangled name into the class it is in and its last component.
fn qualified(text: &str) -> Option<(String, String)> {
    // Cut the parameter list and anything after it, then split on the last
    // `::` that is not inside a template argument list.
    let name = before_parameters(text);
    let mut depth = 0i32;
    let bytes: Vec<char> = name.chars().collect();
    let mut cut = None;
    for i in 0..bytes.len() {
        match bytes[i] {
            '<' | '(' => depth += 1,
            '>' | ')' => depth -= 1,
            ':' if depth == 0 && i + 1 < bytes.len() && bytes[i + 1] == ':' => cut = Some(i),
            _ => {}
        }
    }
    let cut = cut?;
    let class: String = bytes[..cut].iter().collect();
    let last: String = bytes[cut + 2..].iter().collect();
    (!class.is_empty() && !last.is_empty()).then_some((class, last))
}

/// A class's own name: the last component of a qualified name, with any
/// template argument list taken off.
fn simple_name(class: &str) -> String {
    let chars: Vec<char> = class.chars().collect();
    let mut depth = 0i32;
    let mut start = 0usize;
    let mut template = chars.len();
    for i in 0..chars.len() {
        match chars[i] {
            '<' | '(' => {
                if depth == 0 && template == chars.len() {
                    template = i;
                }
                depth += 1;
            }
            '>' | ')' => depth -= 1,
            ':' if depth == 0 && i + 1 < chars.len() && chars[i + 1] == ':' => {
                start = i + 2;
                // A template list before this `::` belonged to an enclosing
                // class, not to this one.
                template = chars.len();
            }
            _ => {}
        }
    }
    chars[start..template.max(start)].iter().collect()
}

/// The name part of a demangled function, without its parameters.
fn before_parameters(text: &str) -> &str {
    let mut depth = 0i32;
    for (i, c) in text.char_indices() {
        match c {
            '<' => depth += 1,
            '>' => depth -= 1,
            '(' if depth == 0 => return text[..i].trim_end(),
            _ => {}
        }
    }
    text
}

/// Every function that writes a known vtable pointer through its first
/// argument, and which pointers it writes where.
///
/// Each write is the offset into the object and the table whose address went
/// there, in the order the instructions appear. The order is what tells a
/// constructor with its bases inlined from a destructor with the same, so it
/// is not sorted away.
///
/// The prefilter is what makes this affordable: only functions that mention a
/// virtual table at all are lifted, which over a real library is a small
/// fraction of them.
fn vptr_writers(p: &Program, tables: &[VTable]) -> BTreeMap<Addr, Vec<(i64, Addr)>> {
    let entries: BTreeSet<u64> = tables.iter().map(|t| t.entry.get()).collect();
    // The byte range each table covers, so a reference to any part of one
    // counts as mentioning it.
    let mut ranges: Vec<(u64, u64)> = tables
        .iter()
        .map(|t| (t.addr.get(), t.entry.get() + t.methods.len() as u64 * 8))
        .collect();
    ranges.sort_unstable();

    // Function hulls, sorted, so mapping a reference to its function does not
    // walk every function in the program.
    let mut hulls: Vec<(u64, u64, Addr)> = p
        .functions_by_address()
        .map(|f| (f.range.start().get(), f.range.end().get(), f.entry))
        .collect();
    hulls.sort_unstable();

    let mut candidates: BTreeSet<Addr> = BTreeSet::new();
    for x in p.xrefs.all() {
        let to = x.to.get();
        // The last table that starts at or before the reference is the only
        // one that can contain it, because tables do not overlap. A shared
        // library does not name its own tables directly: it reaches them
        // through a global offset table slot, so a reference to a word that
        // holds a table's address counts as a mention of the table.
        let inside = |v: u64| {
            let i = ranges.partition_point(|(start, _)| *start <= v);
            i > 0 && v < ranges[i - 1].1
        };
        if !inside(to) && !word(p, x.to).is_some_and(inside) {
            continue;
        }
        let from = x.from.get();
        // The last hull that starts at or before the reference.
        let i = hulls.partition_point(|(start, _, _)| *start <= from);
        for (start, end, entry) in hulls[..i].iter().rev().take(8) {
            if from >= *start && from < *end {
                candidates.insert(*entry);
                break;
            }
        }
    }

    let mut out: BTreeMap<Addr, Vec<(i64, Addr)>> = BTreeMap::new();
    for at in candidates {
        let Some(f) = p.function(at) else { continue };
        let Some(ssa) = ssa_of(p, f) else { continue };
        let abi = e5r_ir::abi::of(&p.object.arch);
        let Some(this) = abi.integer_arguments.first().copied() else {
            continue;
        };
        let defs = ssa.definitions();
        let mut writes = Vec::new();
        for b in ssa.blocks.values() {
            for op in &b.ops {
                if op.kind != SsaKind::Op(Op::Store) {
                    continue;
                }
                let (Some(address), Some(value)) = (op.inputs.first(), op.inputs.get(1)) else {
                    continue;
                };
                let Some(v) = constant(p, &ssa, &defs, value, 0) else {
                    continue;
                };
                if !entries.contains(&v) {
                    continue;
                }
                // Through the first argument, which is what a member function
                // is handed a pointer to the object in.
                let Some((base, offset)) = based_on(p, &ssa, &defs, address, 0) else {
                    continue;
                };
                if base.space == Space::Register && base.offset == this {
                    writes.push((op.addr, offset, Addr(v)));
                }
            }
        }
        if !writes.is_empty() {
            // By the address of the instruction that wrote it, so the order is
            // the one the code is written in rather than the one the blocks
            // happened to be walked in. A pointer written twice counts once,
            // at the first place it went in.
            writes.sort();
            let mut seen = BTreeSet::new();
            out.insert(
                at,
                writes
                    .into_iter()
                    .filter(|(_, offset, v)| seen.insert((*offset, *v)))
                    .map(|(_, offset, v)| (offset, v))
                    .collect(),
            );
        }
    }
    out
}

/// What a member function touched through its first argument.
fn this_fields(p: &Program, at: Addr) -> Vec<Field> {
    let Some(f) = p.function(at) else {
        return Vec::new();
    };
    crate::shapes::shapes_of(p, f)
        .into_iter()
        .filter(|s| s.argument == Some(0))
        .flat_map(|s| {
            let written = s.written;
            s.fields.into_iter().map(move |(offset, size)| Field {
                offset,
                size,
                written,
                basis: Basis::Accesses,
            })
        })
        .collect()
}

/// Lift a function to optimized SSA, the way every other pass here does.
fn ssa_of(p: &Program, f: &e5r_analysis::Function) -> Option<SsaFunction> {
    let blocks: BTreeMap<Addr, (Addr, Vec<Addr>)> = f
        .cfg
        .blocks
        .iter()
        .map(|(a, b)| (*a, (b.range.end(), b.successors.clone())))
        .collect();
    if blocks.is_empty() {
        return None;
    }
    let mut ir = e5r_ir::func::build(&p.object.memory, &p.object.arch, f.entry, &blocks);
    e5r_ir::stack::promote(&mut ir);
    let mut ssa = e5r_ir::ssa::build(&ir);
    e5r_ir::opt::optimize(&mut ssa);
    Some(ssa)
}

/// The literal an operand holds, following copies and folding an addition of
/// two literals, which is how an address is built on AArch64.
///
/// A load from a fixed address counts, because a shared library reaches its own
/// virtual tables through the global offset table rather than as an immediate:
/// `adrp` then `ldr` of a slot the loader filled in. Reading that slot back is
/// reading what the loader will put there, which is why the relocations have to
/// have been applied first.
fn constant(
    p: &Program,
    f: &SsaFunction,
    defs: &BTreeMap<Value, (Addr, usize)>,
    operand: &Operand,
    depth: u32,
) -> Option<u64> {
    if depth > 16 {
        return None;
    }
    if let Some(v) = operand.as_const() {
        return Some(v);
    }
    let op = defining(f, defs, operand)?;
    if op.kind == SsaKind::Op(Op::Load) && op.size as u64 == word_size(p) {
        let at = constant(p, f, defs, op.inputs.first()?, depth + 1)?;
        return word(p, Addr(at));
    }
    match op.kind {
        SsaKind::Op(Op::Copy) => constant(p, f, defs, op.inputs.first()?, depth + 1),
        SsaKind::Op(Op::IntAdd) => {
            let a = constant(p, f, defs, op.inputs.first()?, depth + 1)?;
            let b = constant(p, f, defs, op.inputs.get(1)?, depth + 1)?;
            Some(a.wrapping_add(b))
        }
        SsaKind::Op(Op::IntOr) => {
            let a = constant(p, f, defs, op.inputs.first()?, depth + 1)?;
            let b = constant(p, f, defs, op.inputs.get(1)?, depth + 1)?;
            Some(a | b)
        }
        _ => None,
    }
}

/// Unwind an address to the incoming value it is measured from, plus a
/// constant offset.
fn based_on(
    p: &Program,
    f: &SsaFunction,
    defs: &BTreeMap<Value, (Addr, usize)>,
    operand: &Operand,
    depth: u32,
) -> Option<(Location, i64)> {
    if depth > 16 {
        return None;
    }
    if let Operand::Undefined(l) = operand {
        return Some((*l, 0));
    }
    let op = defining(f, defs, operand)?;
    match op.kind {
        SsaKind::Op(Op::Copy) => based_on(p, f, defs, op.inputs.first()?, depth + 1),
        SsaKind::Op(Op::IntAdd) | SsaKind::Op(Op::IntSub) => {
            let sign = if op.kind == SsaKind::Op(Op::IntSub) {
                -1
            } else {
                1
            };
            for (a, b) in [(0, 1), (1, 0)] {
                if let Some(k) = constant(p, f, defs, op.inputs.get(b)?, depth + 1)
                    && let Some((base, offset)) = based_on(p, f, defs, op.inputs.get(a)?, depth + 1)
                {
                    return Some((base, offset.wrapping_add(sign * k as i64)));
                }
            }
            None
        }
        _ => None,
    }
}

fn defining<'a>(
    f: &'a SsaFunction,
    defs: &BTreeMap<Value, (Addr, usize)>,
    operand: &Operand,
) -> Option<&'a e5r_ir::ssa::SsaOp> {
    let v = operand.as_value()?;
    let (block, index) = defs.get(&v)?;
    f.blocks.get(block)?.ops.get(*index)
}
