//! Which functions never come back.
//!
//! A call to `abort` is the end of a basic block. Treating it as an ordinary
//! call makes the walk continue into whatever the compiler put next, which is
//! usually a literal pool or the next function, and the result is a function
//! that appears to contain code it does not.
//!
//! Two sources. Some names are known never to return, and that list is short
//! and stable. The rest is a fixpoint over the call graph: a function whose
//! every path ends in a call to something that does not return does not return
//! either.

use std::collections::{BTreeMap, BTreeSet};

use e5r_core::Addr;

use crate::cfg::{Cfg, Terminator};

/// Names that never return, across the platforms this loads.
///
/// Matched after demangling is not attempted, so both the C name and the
/// mangled C++ one appear where both exist.
const KNOWN: &[&str] = &[
    "abort",
    "exit",
    "_exit",
    "_Exit",
    "quick_exit",
    "__assert_fail",
    "__assert_fail_base",
    "__stack_chk_fail",
    "__fortify_fail",
    "__chk_fail",
    "__libc_fatal",
    "longjmp",
    "siglongjmp",
    "__longjmp_chk",
    "pthread_exit",
    "_Unwind_Resume",
    "__cxa_throw",
    "__cxa_rethrow",
    "__cxa_bad_cast",
    "__cxa_bad_typeid",
    "__cxa_pure_virtual",
    "_ZSt9terminatev",
    "_ZSt10unexpectedv",
    "_ZSt20__throw_length_errorPKc",
    "_ZSt20__throw_out_of_rangePKc",
    "_ZSt17__throw_bad_allocv",
    "_ZSt19__throw_logic_errorPKc",
    "_ZSt24__throw_out_of_range_fmtPKcz",
    "rust_begin_unwind",
    "rust_panic",
    "_ZN4core9panicking5panic17h",
    "ExitProcess",
    "TerminateProcess",
    "RaiseException",
    "_invalid_parameter_noinfo_noreturn",
];

/// True when the name is one that never returns.
///
/// Rust's panic entry points carry a hash suffix, so those are matched by
/// prefix; everything else matches exactly.
pub fn name_never_returns(name: &str) -> bool {
    // A PLT thunk stands in for the function it reaches.
    let name = name.strip_suffix("@plt").unwrap_or(name);
    KNOWN.iter().any(|k| {
        if k.ends_with("17h") {
            name.starts_with(k)
        } else {
            name == *k
        }
    }) || name.starts_with("_ZN4core9panicking")
        || name.starts_with("_ZN3std9panicking")
}

/// Work out which of the recovered functions never return.
///
/// `named` gives each function's name where one is known, and `graph` gives
/// the calls each one makes. A function is added when its name says so, or
/// when every one of its terminating blocks ends in a call to something
/// already in the set.
pub fn compute(
    named: &BTreeMap<Addr, Option<String>>,
    graph: &BTreeMap<Addr, &Cfg>,
) -> BTreeSet<Addr> {
    let mut set: BTreeSet<Addr> = named
        .iter()
        .filter(|(_, n)| n.as_deref().is_some_and(name_never_returns))
        .map(|(a, _)| *a)
        .collect();

    // A fixpoint, bounded: each round can only add, and there are finitely
    // many functions, but a bound keeps a pathological graph from looping.
    for _ in 0..8 {
        let mut added = false;
        for (addr, cfg) in graph {
            if set.contains(addr) {
                continue;
            }
            if never_returns(cfg, &set) {
                set.insert(*addr);
                added = true;
            }
        }
        if !added {
            break;
        }
    }
    set
}

/// True when no path through `cfg` reaches a return.
///
/// Every block that ends the function has to end in a trap or in a call to
/// something already known not to return. A single `ret`, a tail call to a
/// function that does return, or anything unresolved means the claim cannot be
/// made: the conservative answer is that it returns.
fn never_returns(cfg: &Cfg, set: &BTreeSet<Addr>) -> bool {
    if cfg.blocks.is_empty() || cfg.has_indirect || !cfg.is_complete() {
        return false;
    }
    let mut terminal = 0;
    for b in cfg.blocks.values() {
        if !b.successors.is_empty() {
            continue;
        }
        terminal += 1;
        match b.terminator {
            Terminator::Trap | Terminator::NoReturnCall => {}
            // A tail call to something in the set is also an exit.
            Terminator::TailCall if cfg.calls.iter().any(|c| set.contains(c)) => {}
            _ => return false,
        }
    }
    terminal > 0
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn the_known_names_are_recognized() {
        assert!(name_never_returns("abort"));
        assert!(name_never_returns("exit"));
        assert!(name_never_returns("__stack_chk_fail"));
        // A PLT thunk stands in for what it reaches.
        assert!(name_never_returns("abort@plt"));
        assert!(name_never_returns("_ZSt9terminatev"));
        assert!(name_never_returns(
            "_ZN4core9panicking5panic17habcdef0123456789E"
        ));
    }

    #[test]
    fn ordinary_names_are_not_claimed() {
        assert!(!name_never_returns("main"));
        assert!(!name_never_returns("printf"));
        assert!(!name_never_returns("exit_handler"));
        assert!(!name_never_returns("aborted"));
    }
}
