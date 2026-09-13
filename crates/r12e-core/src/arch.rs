//! Architectures, byte order, and pointer width.

use std::fmt;
use std::str::FromStr;

use serde::{Deserialize, Serialize};

/// Byte order of a container and of the machine it targets.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[serde(rename_all = "lowercase")]
pub enum Endian {
    /// Least significant byte first.
    Little,
    /// Most significant byte first.
    Big,
}

/// Pointer width.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
#[serde(rename_all = "lowercase")]
pub enum Bits {
    /// 16-bit pointers.
    Bits16,
    /// 32-bit pointers.
    Bits32,
    /// 64-bit pointers.
    Bits64,
}

impl Bits {
    /// Pointer size in bytes.
    pub const fn bytes(self) -> u64 {
        match self {
            Bits::Bits16 => 2,
            Bits::Bits32 => 4,
            Bits::Bits64 => 8,
        }
    }

    /// A mask covering a pointer of this width.
    pub const fn mask(self) -> u64 {
        match self {
            Bits::Bits16 => 0xffff,
            Bits::Bits32 => 0xffff_ffff,
            Bits::Bits64 => u64::MAX,
        }
    }
}

impl fmt::Display for Bits {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.bytes() * 8)
    }
}

/// An instruction set. Natively decoded ones get a variant; everything a
/// SLEIGH spec reaches arrives as [`Arch::Sleigh`], so breadth needs no edit here.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[serde(rename_all = "lowercase")]
pub enum Arch {
    /// 32-bit x86.
    X86,
    /// 64-bit x86, the `amd64` / `x86-64` naming both appear in the wild.
    X86_64,
    /// 32-bit ARM, A32 and T32.
    Arm,
    /// 64-bit ARM, A64.
    AArch64,
    /// Decoded by a SLEIGH language rather than by a hand-written decoder.
    Sleigh(String),
    /// Recognized container, unknown machine. Analysis stops at the container.
    Unknown(u32),
}

impl Arch {
    /// The width this architecture's pointers have by default.
    pub fn bits(&self) -> Bits {
        match self {
            Arch::X86 | Arch::Arm => Bits::Bits32,
            Arch::X86_64 | Arch::AArch64 => Bits::Bits64,
            Arch::Sleigh(_) | Arch::Unknown(_) => Bits::Bits64,
        }
    }

    /// True when r12e has a native decoder for this architecture.
    pub fn has_native_decoder(&self) -> bool {
        matches!(self, Arch::X86 | Arch::X86_64 | Arch::AArch64)
    }

    /// Instruction alignment. One byte is what makes x86 sweep ambiguous.
    pub fn insn_alignment(&self) -> u64 {
        match self {
            Arch::X86 | Arch::X86_64 => 1,
            Arch::Arm => 2,
            Arch::AArch64 => 4,
            Arch::Sleigh(_) | Arch::Unknown(_) => 1,
        }
    }

    /// The longest instruction, used to bound a decode window.
    pub fn max_insn_len(&self) -> u64 {
        match self {
            Arch::X86 | Arch::X86_64 => 15,
            Arch::Arm => 4,
            Arch::AArch64 => 4,
            Arch::Sleigh(_) | Arch::Unknown(_) => 16,
        }
    }

    /// The short name used on the command line and in JSON.
    pub fn name(&self) -> &str {
        match self {
            Arch::X86 => "x86",
            Arch::X86_64 => "x86-64",
            Arch::Arm => "arm",
            Arch::AArch64 => "aarch64",
            Arch::Sleigh(id) => id,
            Arch::Unknown(_) => "unknown",
        }
    }
}

impl fmt::Display for Arch {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Arch::Unknown(m) => write!(f, "unknown({m:#x})"),
            other => f.write_str(other.name()),
        }
    }
}

impl FromStr for Arch {
    type Err = String;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        // Accept what readelf and objdump print, so a pasted command works.
        Ok(match s.to_ascii_lowercase().replace('_', "-").as_str() {
            "x86" | "i386" | "i686" | "x86-32" => Arch::X86,
            "x86-64" | "amd64" | "x64" => Arch::X86_64,
            "arm" | "armv7" | "thumb" => Arch::Arm,
            "aarch64" | "arm64" | "armv8" => Arch::AArch64,
            other => return Err(format!("unknown architecture {other:?}")),
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn the_spellings_other_tools_print_all_parse() {
        for s in ["x86-64", "amd64", "x64", "X86_64"] {
            assert_eq!(s.parse::<Arch>().unwrap(), Arch::X86_64, "{s}");
        }
        for s in ["aarch64", "arm64", "ARMv8"] {
            assert_eq!(s.parse::<Arch>().unwrap(), Arch::AArch64, "{s}");
        }
        assert!("vax".parse::<Arch>().is_err());
    }

    #[test]
    fn alignment_reflects_the_isa() {
        // The reason linear sweep is hard on x86 and easy on AArch64.
        assert_eq!(Arch::X86_64.insn_alignment(), 1);
        assert_eq!(Arch::AArch64.insn_alignment(), 4);
    }

    #[test]
    fn sleigh_languages_do_not_need_an_enum_variant() {
        let a = Arch::Sleigh("MIPS:BE:32:default".to_string());
        assert_eq!(a.name(), "MIPS:BE:32:default");
        assert!(!a.has_native_decoder());
    }
}
