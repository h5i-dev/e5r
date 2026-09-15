//! The streamed cross reference walk against the one that decoded a whole
//! function first.
//!
//! Cross references are read off instructions in address order, and the tracker
//! that resolves an `adrp`/`add` pair carries state from one instruction to the
//! next. Feeding it one instruction at a time instead of a decoded list saves
//! 224 bytes per instruction on every thread at once, and is only worth doing
//! if it cannot change an answer. This checks that on every function of every
//! fixture, which is the only way to know.

mod common;

use common::{corpus, load};
use e5r_analysis::{Options, Session, cfg, xref};

#[test]
fn streaming_agrees_with_decoding_the_whole_function() {
    let Some(dir) = corpus() else {
        return;
    };
    let mut checked = 0usize;
    for name in ["hello.a64.O2", "hello.a64.O0", "hello.go", "panicky"] {
        if !dir.join(name).exists() {
            continue;
        }
        let Some((_, obj)) = load(name) else { continue };
        let session = Session::new(obj, Options::default());
        let functions = session.functions();
        let mem = &session.object().memory;
        let arch = &session.object().arch;
        for f in functions.values() {
            let insns = cfg::instructions(mem, arch, &f.cfg);
            let mut whole = Vec::new();
            xref::collect(&insns, mem, &mut whole);

            let mut streamed = Vec::new();
            let mut c = xref::Collector::new(mem, &mut streamed);
            let ordered = cfg::for_each_instruction(mem, arch, &f.cfg, |i| c.push(i));
            c.finish();

            assert!(
                ordered,
                "{name}: blocks of {:x} are out of address order",
                f.entry.get()
            );
            assert_eq!(
                whole,
                streamed,
                "{name}: streaming changed the references of {:x}",
                f.entry.get()
            );
            checked += 1;
        }
    }
    assert!(checked > 100, "only {checked} functions were compared");
}
