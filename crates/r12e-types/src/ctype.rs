//! A C type model.
//!
//! Enough of C's type system to hold what debug information carries and what
//! structure recovery infers, and to print a declaration correctly. Printing is
//! the part people get wrong: C's declarator syntax wraps around the name, so a
//! pointer to a function returning a pointer to an array is not a prefix and a
//! suffix glued together.
//!
//! Types live in a store and are referred to by id, because they are recursive:
//! a linked list node points to itself, and a tree of boxes cannot.

use std::collections::BTreeMap;
use std::fmt::Write as _;

/// A type's identity within a [`Types`] store.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct TypeId(pub u32);

/// How a value is stored and what its bits mean.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Type {
    /// No value.
    Void,
    /// An integer of this many bytes, signed or not.
    Int {
        /// Width in bytes.
        size: u8,
        /// True for a signed type.
        signed: bool,
    },
    /// A floating point number of this many bytes.
    Float {
        /// Width in bytes.
        size: u8,
    },
    /// A boolean, which C spells `_Bool` and gives one byte.
    Bool,
    /// A pointer to something.
    Pointer(TypeId),
    /// An array, with a count when the declaration gave one.
    Array(TypeId, Option<u64>),
    /// A structure or union.
    Composite(Composite),
    /// An enumeration.
    Enum(Enumeration),
    /// A function type.
    Function(Signature),
    /// A name for another type.
    Typedef(String, TypeId),
    /// A type the debug information named but did not define.
    Opaque(String),
}

/// A structure or a union.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Composite {
    /// The tag, when it has one.
    pub name: Option<String>,
    /// True for a union, where every field starts at zero.
    pub union: bool,
    /// Declared size in bytes, when known.
    pub size: Option<u64>,
    /// The fields, in offset order.
    pub fields: Vec<Field>,
}

/// One field of a structure.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Field {
    /// Its name.
    pub name: String,
    /// Its type.
    pub ty: TypeId,
    /// Byte offset from the start of the structure.
    pub offset: u64,
    /// Width in bits, for a bitfield.
    pub bits: Option<u8>,
}

/// An enumeration and its named values.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Enumeration {
    /// The tag, when it has one.
    pub name: Option<String>,
    /// Size in bytes.
    pub size: u8,
    /// The named values.
    pub values: Vec<(String, i64)>,
}

/// A function's type.
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct Signature {
    /// What it returns.
    pub returns: Option<TypeId>,
    /// Its parameters, named where a name is known.
    pub parameters: Vec<(Option<String>, TypeId)>,
    /// True when it takes a variable number of arguments.
    pub varargs: bool,
}

/// A store of types, addressed by id.
#[derive(Debug, Clone, Default)]
pub struct Types {
    types: Vec<Type>,
    /// Types that have a name, so a second reference finds the first.
    by_name: BTreeMap<String, TypeId>,
}

impl Types {
    /// An empty store, with the basic types already in it.
    pub fn new() -> Types {
        let mut t = Types::default();
        t.add(Type::Void);
        t
    }

    /// The void type, which is always first.
    pub const VOID: TypeId = TypeId(0);

    /// Add a type and return its id.
    pub fn add(&mut self, ty: Type) -> TypeId {
        if let Some(name) = named(&ty) {
            if let Some(existing) = self.by_name.get(&name) {
                return *existing;
            }
            let id = TypeId(self.types.len() as u32);
            self.by_name.insert(name, id);
            self.types.push(ty);
            return id;
        }
        // An unnamed type that is structurally identical to one already here is
        // the same type; the store stays small and comparisons stay cheap.
        if let Some(n) = self.types.iter().position(|t| *t == ty) {
            return TypeId(n as u32);
        }
        let id = TypeId(self.types.len() as u32);
        self.types.push(ty);
        id
    }

    /// Reserve an id to be filled in later, for a type that refers to itself.
    pub fn reserve(&mut self, name: &str) -> TypeId {
        let id = TypeId(self.types.len() as u32);
        self.types.push(Type::Opaque(name.to_string()));
        id
    }

    /// Replace a reserved id's type.
    pub fn define(&mut self, id: TypeId, ty: Type) {
        if let Some(slot) = self.types.get_mut(id.0 as usize) {
            *slot = ty;
        }
    }

    /// Look one up.
    pub fn get(&self, id: TypeId) -> Option<&Type> {
        self.types.get(id.0 as usize)
    }

    /// How many there are.
    pub fn len(&self) -> usize {
        self.types.len()
    }

    /// True when the store holds nothing but void.
    pub fn is_empty(&self) -> bool {
        self.types.len() <= 1
    }

    /// A common integer type of this width.
    pub fn integer(&mut self, size: u8, signed: bool) -> TypeId {
        self.add(Type::Int { size, signed })
    }

    /// A pointer to a type.
    pub fn pointer(&mut self, to: TypeId) -> TypeId {
        self.add(Type::Pointer(to))
    }

    /// The size a value of this type occupies, when it is known.
    pub fn size_of(&self, id: TypeId) -> Option<u64> {
        match self.get(id)? {
            Type::Void => None,
            Type::Bool => Some(1),
            Type::Int { size, .. } | Type::Float { size } => Some(*size as u64),
            // Every pointer is eight bytes on the architectures this supports.
            Type::Pointer(_) => Some(8),
            Type::Array(inner, Some(n)) => Some(self.size_of(*inner)? * n),
            Type::Array(_, None) => None,
            Type::Composite(c) => c.size,
            Type::Enum(e) => Some(e.size as u64),
            Type::Function(_) => None,
            Type::Typedef(_, inner) => self.size_of(*inner),
            Type::Opaque(_) => None,
        }
    }

    /// Follow typedefs to the type underneath.
    pub fn resolve(&self, mut id: TypeId) -> TypeId {
        for _ in 0..64 {
            match self.get(id) {
                Some(Type::Typedef(_, inner)) => id = *inner,
                _ => break,
            }
        }
        id
    }

    /// The field at an offset, for turning a pointer access into a field
    /// access. Returns the field and the offset within it.
    pub fn field_at(&self, id: TypeId, offset: u64) -> Option<(&Field, u64)> {
        let Type::Composite(c) = self.get(self.resolve(id))? else {
            return None;
        };
        // The last field that starts at or before the offset and covers it.
        c.fields
            .iter()
            .filter(|f| f.offset <= offset)
            .rfind(|f| match self.size_of(f.ty) {
                Some(size) => offset < f.offset + size.max(1),
                None => true,
            })
            .map(|f| (f, offset - f.offset))
    }

    /// The C definition of a named type, so output that uses it compiles.
    ///
    /// Returns nothing for a type that needs no definition: the basic types,
    /// and anything anonymous.
    pub fn definition(&self, id: TypeId) -> Option<String> {
        match self.get(id)? {
            Type::Typedef(name, inner) => Some(format!("typedef {};", self.declare(*inner, name))),
            Type::Composite(c) => {
                let name = c.name.as_ref()?;
                let keyword = if c.union { "union" } else { "struct" };
                let mut out = format!("{keyword} {name} {{");
                for f in &c.fields {
                    out.push(' ');
                    out.push_str(&self.declare(f.ty, &f.name));
                    match f.bits {
                        Some(bits) => {
                            let _ = write!(out, " : {bits};");
                        }
                        None => out.push(';'),
                    }
                }
                out.push_str(" };");
                Some(out)
            }
            Type::Enum(e) => {
                let name = e.name.as_ref()?;
                let mut out = format!("enum {name} {{");
                for (n, (value_name, value)) in e.values.iter().enumerate() {
                    if n > 0 {
                        out.push(',');
                    }
                    let _ = write!(out, " {value_name} = {value}");
                }
                out.push_str(" };");
                Some(out)
            }
            _ => None,
        }
    }

    /// Every type this one refers to, including itself, deepest first, so a
    /// list of definitions comes out in an order C will accept.
    pub fn dependencies(&self, id: TypeId) -> Vec<TypeId> {
        let mut out = Vec::new();
        let mut seen = std::collections::BTreeSet::new();
        self.walk(id, &mut seen, &mut out, 0);
        out
    }

    fn walk(
        &self,
        id: TypeId,
        seen: &mut std::collections::BTreeSet<TypeId>,
        out: &mut Vec<TypeId>,
        depth: u32,
    ) {
        if depth > 32 || !seen.insert(id) {
            return;
        }
        match self.get(id) {
            Some(Type::Pointer(inner)) | Some(Type::Array(inner, _)) => {
                self.walk(*inner, seen, out, depth + 1)
            }
            Some(Type::Typedef(_, inner)) => self.walk(*inner, seen, out, depth + 1),
            Some(Type::Composite(c)) => {
                for f in c.fields.clone() {
                    self.walk(f.ty, seen, out, depth + 1);
                }
            }
            Some(Type::Function(sig)) => {
                let sig = sig.clone();
                if let Some(r) = sig.returns {
                    self.walk(r, seen, out, depth + 1);
                }
                for (_, ty) in &sig.parameters {
                    self.walk(*ty, seen, out, depth + 1);
                }
            }
            _ => {}
        }
        out.push(id);
    }

    /// Render a declaration of `name` with this type, the way C spells it.
    pub fn declare(&self, id: TypeId, name: &str) -> String {
        let mut declarator = name.to_string();
        let base = self.build(id, &mut declarator);
        if declarator.is_empty() {
            base
        } else {
            format!("{base} {declarator}")
        }
    }

    /// The name of a type on its own, as a cast or a field type would spell it.
    pub fn name_of(&self, id: TypeId) -> String {
        self.declare(id, "")
    }

    /// Build the base type, wrapping the declarator as C requires.
    fn build(&self, id: TypeId, declarator: &mut String) -> String {
        match self.get(id) {
            None => "void".to_string(),
            Some(Type::Void) => "void".to_string(),
            Some(Type::Bool) => "_Bool".to_string(),
            Some(Type::Int { size, signed }) => int_name(*size, *signed).to_string(),
            Some(Type::Float { size }) => match size {
                4 => "float".to_string(),
                16 => "long double".to_string(),
                _ => "double".to_string(),
            },
            Some(Type::Pointer(inner)) => {
                declarator.insert(0, '*');
                // A pointer to an array or a function binds looser than the
                // brackets, so it needs parentheses.
                if self.needs_parentheses(*inner) {
                    declarator.insert(0, '(');
                    declarator.push(')');
                }
                self.build(*inner, declarator)
            }
            Some(Type::Array(inner, count)) => {
                match count {
                    Some(n) => {
                        let _ = write!(declarator, "[{n}]");
                    }
                    None => declarator.push_str("[]"),
                }
                self.build(*inner, declarator)
            }
            Some(Type::Function(sig)) => {
                declarator.push('(');
                for (n, (param_name, ty)) in sig.parameters.iter().enumerate() {
                    if n > 0 {
                        declarator.push_str(", ");
                    }
                    declarator.push_str(&self.declare(*ty, param_name.as_deref().unwrap_or("")));
                }
                if sig.varargs {
                    if !sig.parameters.is_empty() {
                        declarator.push_str(", ");
                    }
                    declarator.push_str("...");
                }
                if sig.parameters.is_empty() && !sig.varargs {
                    declarator.push_str("void");
                }
                declarator.push(')');
                match sig.returns {
                    Some(r) => self.build(r, declarator),
                    None => "void".to_string(),
                }
            }
            Some(Type::Composite(c)) => {
                let keyword = if c.union { "union" } else { "struct" };
                match &c.name {
                    Some(n) => format!("{keyword} {n}"),
                    None => format!("{keyword} {{...}}"),
                }
            }
            Some(Type::Enum(e)) => match &e.name {
                Some(n) => format!("enum {n}"),
                None => "enum {...}".to_string(),
            },
            Some(Type::Typedef(n, _)) => n.clone(),
            Some(Type::Opaque(n)) => n.clone(),
        }
    }

    fn needs_parentheses(&self, id: TypeId) -> bool {
        matches!(
            self.get(id),
            Some(Type::Array(..)) | Some(Type::Function(_))
        )
    }
}

fn named(ty: &Type) -> Option<String> {
    match ty {
        Type::Typedef(n, _) => Some(format!("typedef {n}")),
        Type::Composite(c) => c
            .name
            .as_ref()
            .map(|n| format!("{} {n}", if c.union { "union" } else { "struct" })),
        Type::Enum(e) => e.name.as_ref().map(|n| format!("enum {n}")),
        _ => None,
    }
}

fn int_name(size: u8, signed: bool) -> &'static str {
    match (size, signed) {
        (1, true) => "int8_t",
        (1, false) => "uint8_t",
        (2, true) => "int16_t",
        (2, false) => "uint16_t",
        (4, true) => "int32_t",
        (4, false) => "uint32_t",
        (16, true) => "__int128",
        (16, false) => "unsigned __int128",
        (_, true) => "int64_t",
        (_, false) => "uint64_t",
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn a_pointer_to_an_array_needs_its_parentheses() {
        let mut t = Types::new();
        let int = t.integer(4, true);
        let array = t.add(Type::Array(int, Some(10)));
        let pointer = t.pointer(array);
        assert_eq!(t.declare(pointer, "p"), "int32_t (*p)[10]");
        // Where an array of pointers does not.
        let pointer_to_int = t.pointer(int);
        let pointers = t.add(Type::Array(pointer_to_int, Some(10)));
        assert_eq!(t.declare(pointers, "p"), "int32_t *p[10]");
    }

    #[test]
    fn a_function_pointer_reads_the_way_c_spells_it() {
        let mut t = Types::new();
        let int = t.integer(4, true);
        let c = t.integer(1, true);
        let char_ptr = t.pointer(c);
        let sig = Signature {
            returns: Some(int),
            parameters: vec![(None, char_ptr)],
            varargs: false,
        };
        let f = t.add(Type::Function(sig));
        let p = t.pointer(f);
        assert_eq!(t.declare(p, "handler"), "int32_t (*handler)(int8_t *)");
    }

    #[test]
    fn a_named_structure_is_stored_once() {
        let mut t = Types::new();
        let c = Composite {
            name: Some("Point".into()),
            union: false,
            size: Some(8),
            fields: Vec::new(),
        };
        let a = t.add(Type::Composite(c.clone()));
        let b = t.add(Type::Composite(c));
        assert_eq!(a, b);
        assert_eq!(t.name_of(a), "struct Point");
    }

    #[test]
    fn a_field_is_found_by_the_offset_it_covers() {
        let mut t = Types::new();
        let int = t.integer(4, true);
        let long = t.integer(8, true);
        let point = t.add(Type::Composite(Composite {
            name: Some("Point".into()),
            union: false,
            size: Some(16),
            fields: vec![
                Field {
                    name: "x".into(),
                    ty: int,
                    offset: 0,
                    bits: None,
                },
                Field {
                    name: "y".into(),
                    ty: int,
                    offset: 4,
                    bits: None,
                },
                Field {
                    name: "tag".into(),
                    ty: long,
                    offset: 8,
                    bits: None,
                },
            ],
        }));
        assert_eq!(t.field_at(point, 0).unwrap().0.name, "x");
        assert_eq!(t.field_at(point, 6).unwrap().0.name, "y");
        assert_eq!(t.field_at(point, 6).unwrap().1, 2);
        assert_eq!(t.field_at(point, 8).unwrap().0.name, "tag");
        assert!(t.field_at(point, 64).is_none());
    }

    #[test]
    fn sizes_follow_through_typedefs_and_arrays() {
        let mut t = Types::new();
        let int = t.integer(4, true);
        let name = t.add(Type::Typedef("word".into(), int));
        let array = t.add(Type::Array(name, Some(8)));
        assert_eq!(t.size_of(array), Some(32));
        assert_eq!(t.declare(array, "v"), "word v[8]");
    }
}
