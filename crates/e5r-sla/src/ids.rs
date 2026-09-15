//! Names for the element and attribute ids.
//!
//! The ids are numbers in the file; the names here are ours, worked out by
//! compiling `.slaspec` inputs and watching which number moved. Only ids whose
//! meaning was established that way are named. An id with no name is not a
//! guess waiting to happen: it is counted as an uninterpreted region, so the
//! gap between what this reader understands and what a `.sla` contains is a
//! number rather than an impression. `docs/sla-format.md` records the evidence
//! for each name and separates what was proved from what was inferred.

/// The name for an element id, or `None` if the meaning is not established.
#[must_use]
pub fn element_name(id: u32) -> Option<&'static str> {
    Some(match id {
        1 => "const_real",
        2 => "varnode_tpl",
        3 => "const_spaceid",
        4 => "const_handle",
        5 => "op_tpl",
        6 => "pattern_word",
        7 => "pattern_block",
        8 => "print_literal",
        9 => "decision_pair",
        10 => "context_pattern",
        11 => "null",
        12 => "operand_value",
        13 => "operand_sym",
        14 => "operand_sym_head",
        15 => "constructor_operand",
        16 => "decision",
        17 => "print_operand",
        18 => "instruction_pattern",
        19 => "combine_pattern",
        20 => "constructor",
        21 => "construct_tpl",
        22 => "scope",
        23 => "varnode_sym",
        24 => "varnode_sym_head",
        25 => "userop_sym",
        26 => "userop_sym_head",
        27 => "token_field",
        28 => "varnode_list_entry",
        29 => "context_field",
        30 => "handle_tpl",
        31 => "const_relative",
        32 => "context_change",
        33 => "sleigh",
        34 => "spaces",
        35 => "sourcefiles",
        36 => "sourcefile",
        37 => "space",
        38 => "symbol_table",
        39 => "value_sym",
        40 => "value_sym_head",
        41 => "context_sym",
        42 => "context_sym_head",
        43 => "end_sym",
        44 => "end_sym_head",
        45 => "space_other",
        46 => "space_unique",
        47 => "pexp_and",
        48 => "pexp_div",
        49 => "pexp_lshift",
        50 => "pexp_minus",
        51 => "pexp_mult",
        52 => "pexp_not",
        53 => "pexp_or",
        54 => "pexp_plus",
        55 => "pexp_rshift",
        56 => "pexp_sub",
        57 => "pexp_xor",
        58 => "pexp_constant",
        59 => "pexp_inst_next",
        60 => "pexp_inst_next2",
        61 => "pexp_inst_start",
        64 => "name_sym",
        65 => "name_sym_head",
        66 => "name_entry",
        67 => "next2_sym",
        68 => "next2_sym_head",
        69 => "start_sym",
        70 => "start_sym_head",
        71 => "subtable_sym",
        72 => "subtable_sym_head",
        73 => "valuemap_sym",
        74 => "valuemap_sym_head",
        75 => "valuemap_entry",
        76 => "varnode_list_sym",
        77 => "varnode_list_sym_head",
        79 => "globalset",
        80 => "const_inst_start",
        81 => "const_inst_next",
        82 => "const_inst_next2",
        83 => "const_curspace",
        84 => "const_curspace_size",
        _ => return None,
    })
}

/// The name for an attribute id, or `None` if the meaning is not established.
/// Several ids are reused with a different meaning depending on the element
/// that carries them, so these names are the common case and the model reads
/// each element's attributes in its own terms.
#[must_use]
pub fn attribute_name(id: u32) -> Option<&'static str> {
    Some(match id {
        2 => "val",
        3 => "id",
        4 => "space",
        5 => "select",
        6 => "off",
        7 => "code",
        8 => "mask",
        9 => "index",
        10 => "nbytes",
        11 => "piece",
        12 => "name",
        13 => "scope",
        14 => "startbit",
        15 => "size",
        16 => "table",
        17 => "ct",
        20 => "number",
        21 => "context",
        22 => "parent",
        23 => "subsym",
        24 => "line",
        25 => "source",
        26 => "length",
        29 => "shift",
        30 => "endbit",
        31 => "signbit",
        32 => "endbyte",
        33 => "startbyte",
        34 => "version",
        35 => "bigendian",
        36 => "align",
        37 => "uniqbase",
        41 => "defaultspace",
        42 => "delay",
        43 => "wordsize",
        44 => "physical",
        45 => "scopesize",
        46 => "symbolsize",
        47 => "varnode",
        48 => "low",
        49 => "high",
        50 => "flow",
        52 => "word",
        53 => "numct",
        54 => "section",
        55 => "labels",
        _ => return None,
    })
}

/// Element ids used by the tree walk, so the model does not spell numbers
/// inline where a mistake would be silent.
pub mod el {
    pub const CONST_REAL: u32 = 1;
    pub const VARNODE_TPL: u32 = 2;
    pub const CONST_SPACEID: u32 = 3;
    pub const CONST_HANDLE: u32 = 4;
    pub const OP_TPL: u32 = 5;
    pub const PATTERN_WORD: u32 = 6;
    pub const PATTERN_BLOCK: u32 = 7;
    pub const PRINT_LITERAL: u32 = 8;
    pub const DECISION_PAIR: u32 = 9;
    pub const CONTEXT_PATTERN: u32 = 10;
    pub const NULL: u32 = 11;
    pub const OPERAND_SYM: u32 = 13;
    pub const CONSTRUCTOR_OPERAND: u32 = 15;
    pub const DECISION: u32 = 16;
    pub const PRINT_OPERAND: u32 = 17;
    pub const INSTRUCTION_PATTERN: u32 = 18;
    pub const COMBINE_PATTERN: u32 = 19;
    pub const CONSTRUCTOR: u32 = 20;
    pub const CONSTRUCT_TPL: u32 = 21;
    pub const SCOPE: u32 = 22;
    pub const VARNODE_SYM: u32 = 23;
    pub const USEROP_SYM: u32 = 25;
    pub const TOKEN_FIELD: u32 = 27;
    pub const VARNODE_LIST_ENTRY: u32 = 28;
    pub const CONTEXT_FIELD: u32 = 29;
    pub const HANDLE_TPL: u32 = 30;
    pub const CONST_RELATIVE: u32 = 31;
    pub const CONTEXT_CHANGE: u32 = 32;
    pub const SLEIGH: u32 = 33;
    pub const SPACES: u32 = 34;
    pub const SOURCEFILES: u32 = 35;
    pub const SOURCEFILE: u32 = 36;
    pub const SPACE: u32 = 37;
    pub const SYMBOL_TABLE: u32 = 38;
    pub const VALUE_SYM: u32 = 39;
    pub const CONTEXT_SYM: u32 = 41;
    pub const END_SYM: u32 = 43;
    pub const SPACE_OTHER: u32 = 45;
    pub const SPACE_UNIQUE: u32 = 46;
    pub const NAME_SYM: u32 = 64;
    pub const NAME_ENTRY: u32 = 66;
    pub const NEXT2_SYM: u32 = 67;
    pub const START_SYM: u32 = 69;
    pub const SUBTABLE_SYM: u32 = 71;
    pub const VALUEMAP_SYM: u32 = 73;
    pub const VALUEMAP_ENTRY: u32 = 75;
    pub const VARNODE_LIST_SYM: u32 = 76;
    pub const VARNODE_LIST_SYM_HEAD: u32 = 77;
    pub const GLOBALSET: u32 = 79;
    pub const CONST_INST_START: u32 = 80;
    pub const CONST_INST_NEXT: u32 = 81;
    pub const CONST_INST_NEXT2: u32 = 82;
    pub const CONST_CURSPACE: u32 = 83;
    pub const CONST_CURSPACE_SIZE: u32 = 84;

    /// Pattern expression operators, settled one experiment each; see
    /// `docs/sla-format.md`. The run is alphabetical by the operator's name
    /// in the SLEIGH source, which is why it is contiguous.
    pub const PEXP_AND: u32 = 47;
    pub const PEXP_DIV: u32 = 48;
    pub const PEXP_LSHIFT: u32 = 49;
    pub const PEXP_MINUS: u32 = 50;
    pub const PEXP_MULT: u32 = 51;
    pub const PEXP_NOT: u32 = 52;
    pub const PEXP_OR: u32 = 53;
    pub const PEXP_PLUS: u32 = 54;
    pub const PEXP_RSHIFT: u32 = 55;
    pub const PEXP_SUB: u32 = 56;
    pub const PEXP_XOR: u32 = 57;
    pub const PEXP_CONSTANT: u32 = 58;
    pub const PEXP_INST_NEXT: u32 = 59;
    pub const PEXP_INST_NEXT2: u32 = 60;
    pub const PEXP_INST_START: u32 = 61;
    pub const OPERAND_VALUE: u32 = 12;
}

/// Attribute ids used by the tree walk.
pub mod at {
    pub const VAL: u32 = 2;
    pub const ID: u32 = 3;
    pub const SPACE: u32 = 4;
    pub const SELECT: u32 = 5;
    pub const OFF: u32 = 6;
    pub const CODE: u32 = 7;
    pub const MASK: u32 = 8;
    pub const INDEX: u32 = 9;
    pub const NBYTES: u32 = 10;
    pub const PIECE: u32 = 11;
    pub const NAME: u32 = 12;
    pub const SCOPE: u32 = 13;
    pub const STARTBIT: u32 = 14;
    pub const SIZE: u32 = 15;
    pub const TABLE: u32 = 16;
    pub const CT: u32 = 17;
    pub const NUMBER: u32 = 20;
    pub const CONTEXT: u32 = 21;
    pub const PARENT: u32 = 22;
    pub const SUBSYM: u32 = 23;
    pub const LINE: u32 = 24;
    pub const SOURCE: u32 = 25;
    pub const LENGTH: u32 = 26;
    pub const SHIFT: u32 = 29;
    pub const ENDBIT: u32 = 30;
    pub const SIGNBIT: u32 = 31;
    pub const ENDBYTE: u32 = 32;
    pub const STARTBYTE: u32 = 33;
    pub const VERSION: u32 = 34;
    pub const BIGENDIAN: u32 = 35;
    pub const ALIGN: u32 = 36;
    pub const UNIQBASE: u32 = 37;
    pub const DEFAULTSPACE: u32 = 41;
    pub const DELAY: u32 = 42;
    pub const WORDSIZE: u32 = 43;
    pub const PHYSICAL: u32 = 44;
    pub const SCOPESIZE: u32 = 45;
    pub const SYMBOLSIZE: u32 = 46;
    pub const VARNODE: u32 = 47;
    pub const LOW: u32 = 48;
    pub const HIGH: u32 = 49;
    pub const FLOW: u32 = 50;
    pub const NUMCT: u32 = 53;
    pub const SECTION: u32 = 54;
    pub const LABELS: u32 = 55;
    pub const WORD: u32 = 52;
    /// On a constructor: where the mnemonic ends among the print pieces.
    pub const FLOWTHRU: u32 = 27;
    /// On an operand symbol body, the two values whose meaning is not
    /// established. They are carried through so the file can be written back.
    pub const OPERAND_18: u32 = 18;
    pub const OPERAND_19: u32 = 19;
    /// On a const_handle template leaf.
    pub const HANDLE_28: u32 = 28;
}
