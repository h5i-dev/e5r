//! Where a fact came from (`ROADMAP.md` bet 4).
//!
//! A boundary from an `.eh_frame` FDE and one from a prologue pattern are not
//! the same claim. Every recovered fact carries one of these so the CLI can
//! answer "why do you think that?" without re-running analysis.

use std::cmp::Ordering;
use std::fmt;

use serde::{Deserialize, Serialize};

/// How strongly a fact is known. Ordered weakest to strongest.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
#[serde(rename_all = "lowercase")]
pub enum Strength {
    /// A pattern guess: prologue match, alignment, a plausible-looking string.
    Heuristic,
    /// Derived from something proven. A direct call's target is inferred: the
    /// decode is proven, "therefore a function" is a step past it.
    Inferred,
    /// Stated by the file in a structure the format defines.
    Proven,
    /// Written in the annotation log. Outranks anything the engine derives.
    Asserted,
}

impl Strength {
    /// True when the engine may overwrite a fact of this strength with one of
    /// its own. It may never overwrite an assertion.
    pub fn is_overridable(self) -> bool {
        self != Strength::Asserted
    }

    /// The lowercase word used in output and in JSON.
    pub fn as_str(self) -> &'static str {
        match self {
            Strength::Heuristic => "heuristic",
            Strength::Inferred => "inferred",
            Strength::Proven => "proven",
            Strength::Asserted => "asserted",
        }
    }
}

impl fmt::Display for Strength {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.as_str())
    }
}

/// The specific evidence behind a fact: the "why" the CLI prints.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum Evidence {
    /// An entry in a symbol table.
    SymbolTable,
    /// Debug information: what the compiler recorded about its own output.
    DebugInfo,
    /// A symbol with no declared type, sitting in executable memory.
    CodeSymbol,
    /// An entry in a dynamic symbol table.
    DynamicSymbol,
    /// The container's declared entry point.
    EntryPoint,
    /// An initializer or finalizer array.
    InitArray,
    /// A `.eh_frame` frame description entry.
    EhFrame,
    /// A PE `RUNTIME_FUNCTION` unwind record.
    PeUnwind,
    /// A Mach-O `LC_FUNCTION_STARTS` entry.
    MachFunctionStarts,
    /// Go's `pclntab`.
    GoPclntab,
    /// An export table entry.
    Export,
    /// An import thunk, PLT or IAT.
    ImportThunk,
    /// The target of a direct call found by decoding.
    CallTarget,
    /// The target of a direct branch found by decoding.
    BranchTarget,
    /// A recovered jump table entry.
    JumpTable,
    /// A function prologue byte pattern.
    ProloguePattern,
    /// Code found by sweeping a gap between known functions.
    LinearSweep,
    /// A pointer found in a data section that lands in executable memory.
    DataPointer,
    /// Written in the annotation log by a person or an agent.
    Annotation,
}

impl Evidence {
    /// Strength this evidence carries. One place to decide, so two analyses
    /// cannot disagree about how good a symbol table is.
    pub fn strength(self) -> Strength {
        match self {
            Evidence::SymbolTable
            | Evidence::DebugInfo
            | Evidence::DynamicSymbol
            | Evidence::EntryPoint
            | Evidence::InitArray
            | Evidence::EhFrame
            | Evidence::PeUnwind
            | Evidence::MachFunctionStarts
            | Evidence::GoPclntab
            | Evidence::Export => Strength::Proven,

            Evidence::CodeSymbol
            | Evidence::ImportThunk
            | Evidence::CallTarget
            | Evidence::BranchTarget
            | Evidence::JumpTable => Strength::Inferred,

            Evidence::ProloguePattern | Evidence::LinearSweep | Evidence::DataPointer => {
                Strength::Heuristic
            }

            Evidence::Annotation => Strength::Asserted,
        }
    }

    /// A short human-readable name.
    pub fn as_str(self) -> &'static str {
        match self {
            Evidence::SymbolTable => "symbol table",
            Evidence::DebugInfo => "debug info",
            Evidence::CodeSymbol => "code symbol",
            Evidence::DynamicSymbol => "dynamic symbol",
            Evidence::EntryPoint => "entry point",
            Evidence::InitArray => "init array",
            Evidence::EhFrame => ".eh_frame FDE",
            Evidence::PeUnwind => "PE unwind record",
            Evidence::MachFunctionStarts => "LC_FUNCTION_STARTS",
            Evidence::GoPclntab => "Go pclntab",
            Evidence::Export => "export table",
            Evidence::ImportThunk => "import thunk",
            Evidence::CallTarget => "direct call target",
            Evidence::BranchTarget => "direct branch target",
            Evidence::JumpTable => "jump table entry",
            Evidence::ProloguePattern => "prologue pattern",
            Evidence::LinearSweep => "linear sweep",
            Evidence::DataPointer => "pointer in data",
            Evidence::Annotation => "annotation",
        }
    }
}

impl fmt::Display for Evidence {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.as_str())
    }
}

/// Best evidence for a fact, plus everything else that agreed.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct Provenance {
    /// The strongest evidence seen, which sets the strength.
    pub best: Evidence,
    /// Everything else that pointed at the same fact, strongest first, with no
    /// duplicates.
    pub corroborating: Vec<Evidence>,
}

impl Provenance {
    /// A provenance with one piece of evidence.
    pub fn new(e: Evidence) -> Provenance {
        Provenance {
            best: e,
            corroborating: Vec::new(),
        }
    }

    /// The strength of the best evidence.
    pub fn strength(&self) -> Strength {
        self.best.strength()
    }

    /// How many independent sources agree.
    pub fn support(&self) -> usize {
        1 + self.corroborating.len()
    }

    /// Record another source agreeing. Order-independent: the determinism gate
    /// needs the same answer whatever order the work queue found things in.
    pub fn add(&mut self, e: Evidence) {
        if e == self.best || self.corroborating.contains(&e) {
            return;
        }
        if e.strength() > self.best.strength() {
            let old = std::mem::replace(&mut self.best, e);
            self.corroborating.push(old);
        } else {
            self.corroborating.push(e);
        }
        self.corroborating.sort_by(|a, b| {
            b.strength()
                .cmp(&a.strength())
                .then_with(|| (*a as u8).cmp(&(*b as u8)))
        });
    }

    /// Merge another provenance into this one.
    pub fn merge(&mut self, other: &Provenance) {
        self.add(other.best);
        for e in &other.corroborating {
            self.add(*e);
        }
    }

    /// Rank two provenances: stronger evidence first, then more corroboration.
    pub fn rank(&self, other: &Provenance) -> Ordering {
        other
            .strength()
            .cmp(&self.strength())
            .then_with(|| other.support().cmp(&self.support()))
    }
}

impl fmt::Display for Provenance {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} ({})", self.strength(), self.best)?;
        for e in &self.corroborating {
            write!(f, ", {e}")?;
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn assertions_outrank_everything_the_engine_knows() {
        assert!(Strength::Asserted > Strength::Proven);
        assert!(Strength::Proven > Strength::Inferred);
        assert!(Strength::Inferred > Strength::Heuristic);
        assert!(!Strength::Asserted.is_overridable());
        assert!(Strength::Proven.is_overridable());
    }

    #[test]
    fn adding_stronger_evidence_promotes_it() {
        let mut p = Provenance::new(Evidence::ProloguePattern);
        assert_eq!(p.strength(), Strength::Heuristic);
        p.add(Evidence::SymbolTable);
        assert_eq!(p.best, Evidence::SymbolTable);
        assert_eq!(p.strength(), Strength::Proven);
        assert_eq!(p.corroborating, vec![Evidence::ProloguePattern]);
    }

    #[test]
    fn provenance_does_not_depend_on_arrival_order() {
        // The determinism gate: analysis discovers evidence in whatever order
        // the work queue hands it over, and the answer must not notice.
        let order_a = [
            Evidence::ProloguePattern,
            Evidence::EhFrame,
            Evidence::CallTarget,
        ];
        let order_b = [
            Evidence::CallTarget,
            Evidence::ProloguePattern,
            Evidence::EhFrame,
        ];
        let build = |evs: &[Evidence]| {
            let mut p = Provenance::new(evs[0]);
            for e in &evs[1..] {
                p.add(*e);
            }
            p
        };
        assert_eq!(build(&order_a), build(&order_b));
    }

    #[test]
    fn repeats_do_not_inflate_support() {
        let mut p = Provenance::new(Evidence::SymbolTable);
        p.add(Evidence::SymbolTable);
        p.add(Evidence::EhFrame);
        p.add(Evidence::EhFrame);
        assert_eq!(p.support(), 2);
    }

    #[test]
    fn display_says_why() {
        let mut p = Provenance::new(Evidence::EhFrame);
        p.add(Evidence::ProloguePattern);
        assert_eq!(p.to_string(), "proven (.eh_frame FDE), prologue pattern");
    }
}
