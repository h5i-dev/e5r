//! Ghidra's decompiler datatests, ported.
//!
//! `Ghidra/Features/Decompiler/src/decompile/datatests/` holds eighty-nine
//! saved programs, each with a list of regular expressions its output must
//! match. They are two decades of decompiler bugs written down: a loop that
//! came out as a goto, a division the algebra did not fold back, a comparison
//! that printed the wrong way round. None of them can be run here, because the
//! programs are stored in Ghidra's own XML and the assertions are against
//! Ghidra's own text.
//!
//! So the port is by behaviour, not by text. Each case here is C written to
//! make a compiler emit the shape the original pinned, built into
//! `fixtures/datatests/`, and asserted on by the property the original was
//! about: that the loop is a loop, that the switch is a switch, that the second
//! store did not merge with the first. Never by whole-text comparison, which
//! would only say that our output is not Ghidra's, which it never will be.
//!
//! Cases marked `#[ignore]` are the ones where our decompiler has the bug the
//! datatest was written to catch. They are kept, and named after what is wrong,
//! because a datatest that is deleted when it fails measures nothing.

use std::collections::BTreeMap;
use std::path::{Path, PathBuf};
use std::sync::{Arc, Mutex, OnceLock};

use r12e_analysis::{Options, Program, analyze};
use r12e_format::LoadOptions;

/// Every function of one fixture, decompiled together, indexed by name.
type Functions = BTreeMap<String, String>;

fn build_dir() -> Option<PathBuf> {
    let d = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../fixtures/build");
    d.is_dir().then(|| d.canonicalize().unwrap())
}

fn open(name: &str) -> Option<Program> {
    let data = std::fs::read(build_dir()?.join(name)).ok()?;
    let obj = r12e_format::load(&data, &LoadOptions::default()).ok()?;
    Some(analyze(obj, &Options::default()))
}

/// One fixture, analyzed and decompiled once however many cases ask for it.
///
/// Fifty cases over sixteen builds is eight hundred decompilations of sixteen
/// programs if nothing remembers, and the tests run on threads, so the memo has
/// to be shared rather than thread-local.
fn functions(binary: &str) -> Option<Arc<Functions>> {
    static CACHE: OnceLock<Mutex<BTreeMap<String, Option<Arc<Functions>>>>> = OnceLock::new();
    let cache = CACHE.get_or_init(|| Mutex::new(BTreeMap::new()));
    if let Some(hit) = cache.lock().unwrap().get(binary) {
        return hit.clone();
    }
    let built = open(binary).map(|p| {
        // The same path the command line takes, so a case that passes here is a
        // case a user sees pass.
        let targets: Vec<&r12e_analysis::Function> = p
            .functions_by_address()
            .filter(|f| f.is_complete())
            .collect();
        let unit = r12e_api::decompile_program(&p, &targets);
        Arc::new(
            unit.functions
                .into_iter()
                .map(|f| (f.name.clone(), f.text))
                .collect::<Functions>(),
        )
    });
    cache
        .lock()
        .unwrap()
        .insert(binary.to_string(), built.clone());
    built
}

/// One function's output in one build, with what is being checked attached to
/// every failure so a report names the case, the build and the property.
struct Case {
    build: String,
    name: String,
    text: String,
}

impl Case {
    fn fail(&self, what: &str) -> ! {
        panic!(
            "{}: {} in `{}` [{}]:\n{}",
            self.name, what, self.build, self.build, self.text
        );
    }

    /// The output says this.
    fn has(&self, needle: &str) -> &Self {
        if !self.text.contains(needle) {
            self.fail(&format!("expected `{needle}`"));
        }
        self
    }

    /// The output says at least one of these, for a property two architectures
    /// spell differently.
    fn has_any(&self, needles: &[&str]) -> &Self {
        if !needles.iter().any(|n| self.text.contains(n)) {
            self.fail(&format!("expected one of {needles:?}"));
        }
        self
    }

    /// The output does not say this.
    fn lacks(&self, needle: &str) -> &Self {
        if self.text.contains(needle) {
            self.fail(&format!("did not expect `{needle}`"));
        }
        self
    }

    /// The output says this exactly this many times.
    fn times(&self, needle: &str, n: usize) -> &Self {
        let got = self.text.matches(needle).count();
        if got != n {
            self.fail(&format!("expected `{needle}` {n} times, found {got}"));
        }
        self
    }

    /// The output says this at least this many times.
    fn at_least(&self, needle: &str, n: usize) -> &Self {
        let got = self.text.matches(needle).count();
        if got < n {
            self.fail(&format!(
                "expected `{needle}` at least {n} times, found {got}"
            ));
        }
        self
    }
}

/// Check one property on every named build that was actually produced.
///
/// A missing fixture skips rather than fails: the corpus is gitignored, and a
/// checkout that has not run `scripts/build-fixtures.sh` still runs the suite.
fn case(builds: &[String], function: &str, check: impl Fn(&Case)) {
    for build in builds {
        let Some(fns) = functions(build) else {
            continue;
        };
        let Some(text) = fns.get(function) else {
            panic!("{function}: not recovered from {build}");
        };
        check(&Case {
            build: build.clone(),
            name: function.to_string(),
            text: text.clone(),
        });
    }
}

/// Every build of one fixture: two architectures, two optimization levels.
fn all(source: &str) -> Vec<String> {
    let mut out = Vec::new();
    for arch in ["a64", "x64"] {
        for opt in ["O1", "O2"] {
            out.push(format!("dt-{source}.{arch}.{opt}"));
        }
    }
    out
}

/// One architecture's builds, for a property only that architecture shows.
fn arch(source: &str, arch: &str) -> Vec<String> {
    ["O1", "O2"]
        .iter()
        .map(|opt| format!("dt-{source}.{arch}.{opt}"))
        .collect()
}

/// One optimization level's builds, for a case the other level compiles away.
fn opt(source: &str, opt: &str) -> Vec<String> {
    ["a64", "x64"]
        .iter()
        .map(|a| format!("dt-{source}.{a}.{opt}"))
        .collect()
}

// --- control flow -----------------------------------------------------------

/// forloop1.xml: a counted loop is a loop.
///
/// Ghidra asks for `for (i = 0; i < max; i = i + 1)`. We have no `for` in the
/// region vocabulary, so the property is the one underneath it: the back edge
/// came out as a loop with the call inside, and nothing needed a label.
#[test]
fn forloop1() {
    case(&all("control"), "forloop1", |c| {
        c.has("while (").has("sink(").times("goto ", 0);
    });
}

/// forloop_withskip.xml: a loop whose body can bump the loop variable again.
/// The extra increment must not break the loop apart.
#[test]
fn forloop_withskip() {
    case(&all("control"), "forloop_withskip", |c| {
        c.has("while (").has("source()").times("goto ", 0);
    });
}

/// noforloop_globcall.xml: the loop variable is a global a call can change, so
/// it has to be re-read each time round rather than held in a register.
#[test]
fn noforloop_globcall() {
    case(&all("control"), "noforloop_globcall", |c| {
        c.has("while (").has("sink(1)").times("goto ", 0);
    });
}

/// noforloop_iterused.xml: the loop variable outlives the loop, and the value
/// it carries out has to be the one the last iteration left.
#[test]
fn noforloop_iterused() {
    case(&all("control"), "noforloop_iterused", |c| {
        c.has("while (").has("sink(").has("100");
    });
}

/// copytrim.xml: a loop that counts down to zero, where the iterator is a
/// subtraction rather than an addition.
#[test]
fn countdown_loop() {
    case(&all("control"), "countdown", |c| {
        c.has("while (").has("- 1").times("goto ", 0);
    });
}

/// ifnoexit.xml: a loop body whose early exits are returns. The three tested
/// values have to survive as tests, not collapse into the accumulation.
///
/// O1 only: at O2 clang turns the whole body into a branchless accumulate, so
/// there is nothing left to test.
#[test]
fn ifnoexit() {
    case(&opt("control", "O1"), "ifnoexit", |c| {
        c.has("while (").has("100").has("200").has("300");
    });
}

/// elseif.xml: a six-way ladder stays one chain of tests and needs no label.
///
/// Ghidra additionally asks for the `else if` spelling; ours nests the `if`
/// inside the `else` block instead, which says the same thing with more braces.
#[test]
fn elseif() {
    case(&all("control"), "elseif", |c| {
        c.at_least("if (", 5).times("goto ", 0);
        for n in 1..=6 {
            c.has(&format!("sink{n}("));
        }
    });
}

/// orcompare.xml: two comparisons joined by a short-circuit or.
///
/// Ghidra fuses the pair into `if (a == 10 || b == 20)`. We do not fuse, so the
/// property is what fusing is derived from: both comparisons are there, and the
/// arm they share is reached from each of them.
#[test]
fn orcompare() {
    case(&all("control"), "orcompare", |c| {
        c.has("10").has("20").times("sink1(", 2).times("sink2(", 1);
    });
}

/// orcompare.xml, the three-way case: a chain of three ors.
#[test]
fn orcompare_three_terms() {
    case(&all("control"), "orcompare3", |c| {
        c.at_least("if (", 3).times("sink3(", 3).times("sink4(", 1);
    });
}

/// ccmp.xml: two comparisons joined by a short-circuit and, which AArch64
/// compiles into one `ccmp` against the flags the first left behind.
///
/// Ghidra's assertion is that the pair reads as `ptr[1] == 0x3c && val < 10`
/// with no `SBORROW` left over. Ours keeps them as nested tests, and the
/// property is that both comparisons survive with their operands intact: the
/// load of the second element compared against 60, and the bound on the
/// argument.
#[test]
fn ccmp() {
    case(&all("control"), "andcompare", |c| {
        c.has("+ 4")
            .has("== 60")
            .times("sink5(", 1)
            .times("sink6(", 2)
            .lacks("__borrow");
    });
}

/// multiret.xml: values of one, two and eight bytes flowing into one return.
/// This used to put Ghidra into an infinite loop, so the property is that it
/// terminates with the arithmetic folded: 'a' plus 1001 plus the argument.
#[test]
fn multiret() {
    case(&all("control"), "multiret", |c| {
        c.has("1098");
    });
}

/// condconst.xml: a value known to be constant on the path that reaches its
/// use. The arm that assigns 10 has to say 10 and not name a variable.
#[test]
fn condconst() {
    case(&all("control"), "condconst", |c| {
        c.has("= 10").has("source()");
    });
}

/// condmulti.xml: a conditional constant reaching a join along two paths.
#[test]
fn condmulti() {
    case(&all("control"), "condmulti", |c| {
        c.has("sink1(").has("sink2(").has("sink3(").has("10");
    });
}

// --- arithmetic -------------------------------------------------------------

/// divopt.xml, the easy end: division by a power of two, which is a shift and
/// needs no reciprocal to undo.
#[test]
fn divopt_power_of_two() {
    case(&all("arith"), "divu8", |c| {
        c.has(">> 3");
    });
}

/// convert.xml: constants of several widths reaching the calls that take them.
///
/// Ghidra's assertion is about how each one prints; ours is the step before it,
/// that the right constant arrives at the right call after the compiler has
/// spread the loads out.
#[test]
fn convert_constants_reach_their_calls() {
    case(&all("arith"), "convert", |c| {
        c.has("sink1(256)")
            .has("sink3(1000)")
            .has("sink5(0xfa56ea00)")
            .has("sink6(97)");
    });
}

/// sbyte.xml: a signed byte compared against constants. Ghidra's point is that
/// the decompiler must not reach for `char` just because the load is one byte
/// wide; ours is the same, plus that both equality tests keep their value, with
/// -9 as the byte 0xf7 the machine actually compares.
#[test]
fn sbyte() {
    case(&all("arith"), "sbyte", |c| {
        c.has("247").has("== 10").lacks("char ");
        for n in 1..=4 {
            c.has(&format!("sink{n}("));
        }
    });
}

/// promotecompare.xml: a byte widened before it is compared. The comparison is
/// the point and the widening is noise, so the constant has to survive as one
/// number rather than as a masked subtraction.
///
/// AArch64 only: on x86-64 the `setb` that carries the answer out is dropped,
/// which `setcc_result_is_dropped` records.
#[test]
fn promotecompare() {
    case(&arch("arith", "a64"), "promotecompare", |c| {
        c.has("57").lacks("char ");
    });
}

/// lzcount.xml: a zero test that a compiler renders without a branch. Ghidra
/// wants `return param_1 == 3` out of PowerPC's `cntlzw`; the portable half of
/// that is that a flag turned into a value stays a comparison.
#[test]
fn lzcount() {
    case(&arch("arith", "a64"), "iszero", |c| {
        c.has("== 0");
    });
}

/// statuscmp.xml and boolless.xml in spirit: seven comparisons whose results
/// are values rather than branches. The signed ones and the unsigned one have
/// to stay distinguishable, which is what a flag-word shift would lose.
#[test]
fn statuscmp() {
    case(&arch("arith", "a64"), "cmpvalue", |c| {
        c.has("(int64_t)").has("arg0 != arg1").has("arg1 > arg0");
    });
}

/// statuscmp.xml, the branch half: the signed orderings that come out right.
/// `>` and `>=` are negated into a constant-first form that says the same
/// thing; `<` and `<=` are not, which `signed_compare_is_inverted` records.
#[test]
fn signed_compare_greater() {
    case(&all("arith"), "cmp_gt", |c| {
        c.has_any(&["6 <= ", ">= 6"]).times("sink1(", 1);
    });
    case(&all("arith"), "cmp_ge", |c| {
        c.has_any(&["5 <= ", ">= 5"]).times("sink1(", 1);
    });
}

/// nan.xml: a self-comparison is a NaN test and has to survive as one.
///
/// AArch64 only, for the same reason as `promotecompare`.
#[test]
fn nan() {
    case(&arch("arith", "a64"), "nanfn", |c| {
        c.has("__isnan");
    });
}

/// floatconv.xml: an integer converted to floating point, scaled, and returned.
/// The subtraction has to stay on the integer side of the conversion.
#[test]
fn floatconv() {
    case(&all("arith"), "i2d", |c| {
        c.has("(double)").has_any(&["- 16", "+ -16"]);
    });
}

/// mixfloatint.xml: a prototype that alternates integer and floating point
/// arguments. Ghidra recovers the source order; we recover the register
/// classes, so the property is that four integer arguments and two floating
/// point ones are found and neither kind is read as the other.
#[test]
fn mixfloatint() {
    case(&all("arith"), "dldlll", |c| {
        c.has("arg3").has("farg0").has("farg1").lacks("farg2");
    });
}

// --- memory shapes ----------------------------------------------------------

/// twodim.xml: a two dimensional global array read and written at one row.
///
/// Ghidra prints `myarray[globindex][valin]` and asserts there is no ` * ` left.
/// Without a type for the global we cannot name the dimensions, so the property
/// is the one that survives: the row address is computed once from the global
/// index and both the load and the store are taken from it.
#[test]
fn twodim() {
    case(&all("memory"), "twodim", |c| {
        c.has("+ 10").at_least("<< 2", 1);
    });
}

/// threedim.xml: the same with one more dimension.
#[test]
fn threedim() {
    case(&all("memory"), "threedim", |c| {
        c.has("+ 3").at_least("<< 2", 1);
    });
}

/// nestedoffset.xml: an array inside a structure, indexed through a pointer, so
/// the field's offset lands inside the index expression. The decompiler has to
/// distribute the element scale to see it: the index stays `a + b` and the
/// twelve-byte offset stays a separate addend.
#[test]
fn nestedoffset() {
    case(&all("memory"), "nestedoffset", |c| {
        c.has("+ 12").has("<< 2");
    });
}

/// offsetarray.xml: an array indexed with a negative adjustment, which folds
/// the field offset and the index offset into one constant in the machine code.
/// The index must come back scaled and on its own, not merged with the
/// structure's first field.
#[test]
fn offsetarray() {
    case(&all("memory"), "offsetarray", |c| {
        c.has("(uint32_t)arg0 << 2");
    });
}

/// wayoffarray.xml: the same, with an adjustment big enough to pull the base
/// reference out of the mapped structure entirely.
#[test]
fn wayoffarray() {
    case(&all("memory"), "wayoffarray", |c| {
        c.has("(uint32_t)arg0 << 2");
    });
}

/// stackcorner.xml: a local array written through a computed index. The frame
/// has to survive an index the compiler masks rather than bounds.
///
/// O1 only: at O2 the initializing loop is unrolled and there is no loop left.
#[test]
fn stackcorner() {
    case(&opt("memory", "O1"), "arraybottom", |c| {
        c.has("while (").at_least("& 15", 2).has("100");
    });
}

/// dupptr.xml: two accesses that share an intermediate pointer. The base has to
/// be pushed past the shared part, so the read and the write go through one
/// computed address and the arithmetic between them is not repeated.
#[test]
fn dupptr() {
    case(&all("memory"), "dupptr", |c| {
        c.has(">> 3").has("& 15").has("+ 37");
    });
}

/// pointercmp.xml: a pointer walked one byte at a time until it reaches a
/// computed bound. The increment and the bound both have to be pointers.
#[test]
fn pointercmp() {
    case(&all("memory"), "pointercmp", |c| {
        c.has("while (").has("+ 1");
    });
}

/// offcut.xml: three references into one global, two of them into its interior.
/// Each has to keep its own address: the field at offset 4 of the inner
/// structure and the array element twenty bytes past it are different places.
#[test]
fn offcut() {
    case(&all("memory"), "offcut", |c| {
        c.times("sink1(", 1).times("sink2(", 1).times("sink3(", 1);
    });
}

/// condconst.xml, the global half: four constants stored to four globals.
#[test]
fn globalconst() {
    case(&all("memory"), "globalconst", |c| {
        c.times("= 10", 2).has("= 0");
    });
}

/// stackstring.xml: a string a compiler stores as immediates rather than as
/// data, which is what makes it invisible to a string scan.
///
/// Ghidra reassembles the immediates into `builtin_strncpy(buf, "hello world")`.
/// We do not, so the property is that the packed characters reach the output as
/// the one store the machine makes, which is what such a pass would read.
///
/// O1 and the x86-64 O2 build: AArch64 at O2 spreads the same bytes over
/// registers the store no longer names.
#[test]
fn stackstring() {
    let mut builds = opt("memory", "O1");
    builds.push("dt-memory.x64.O2".to_string());
    case(&builds, "stackstring", |c| {
        c.has("0x6f77206f6c6c6568");
    });
}

/// heapstring.xml: the same store pattern, to memory the function does not own.
///
/// x86-64 only: the AArch64 build ends the run with a `strb` of a register,
/// whose value `byte_register_operand_reads_a_flag` records as lost.
#[test]
fn heapstring() {
    case(&arch("memory", "x64"), "heapstring", |c| {
        c.has("0x3a6567617373654d");
    });
}

/// varcross.xml: two stores to one address with a call between them. Neither
/// may be merged into the other, because the call can read what is there.
#[test]
fn varcross() {
    case(&all("memory"), "varcross", |c| {
        c.has("source()").has("sink1(").at_least("0x", 2);
    });
}

/// revisit.xml: two accesses of different widths to one global, where the
/// narrower one forces the wider one's definition to be reconsidered. The
/// two-byte write has to stay two bytes wide.
#[test]
fn revisit() {
    case(&all("memory"), "revisit", |c| {
        c.has("(uint16_t)").has("110");
    });
}

/// wraprange.xml: a stack range written from high addresses to low ones, so the
/// frame offsets run through zero. The four writes and four reads have to fold
/// to the sum they add up to, which is three times the first argument plus the
/// second.
///
/// AArch64 only: the x86-64 build loses one of the four slots.
#[test]
fn wraprange() {
    case(&arch("memory", "a64"), "wraprange", |c| {
        c.has("<< 1");
    });
}

// --- calls and prototypes ---------------------------------------------------

/// indproto.xml: two indirect calls through two fields of one structure. Each
/// has to keep the field it came from, or both collapse onto the same target.
#[test]
fn indproto() {
    case(&all("calls"), "indproto", |c| {
        c.times("__callind", 2).has("field_0").has("field_8");
    });
}

/// retspecial.xml: a structure too big for registers, returned through the
/// hidden pointer the caller supplies. The three fields have to be written
/// through that pointer at their own offsets.
#[test]
fn retspecial() {
    case(&all("calls"), "returnbig", |c| {
        c.has_any(&["+ 8", "field_8"])
            .has_any(&["+ 16", "field_10"])
            .at_least(" = ", 3);
    });
}

/// stackspill.xml: more integer arguments than there are argument registers, so
/// the tail of the list arrives on the stack and has to be found there.
#[test]
fn stackspill() {
    case(&all("calls"), "manyargs", |c| {
        c.has("arg_s");
    });
}

/// stackcorner.xml, the parameter half: a function whose last argument is past
/// the register set, beside six that are not.
#[test]
fn paramnodirect() {
    case(&all("calls"), "paramnodirect", |c| {
        c.has("sink(").has("arg5").has_any(&["arg6", "arg_s"]);
    });
}

/// inline.xml: a callee small enough that a decompiler is tempted to inline it,
/// called twice with different arguments. Both calls have to stay calls.
///
/// Three occurrences, not two: the caller's own name ends in the callee's, so
/// its signature matches as well as its two calls. The second of those is a
/// tail call, and it was missing from the output until a branch out of the
/// function was recognized as the call it is.
#[test]
fn inline() {
    case(&all("calls"), "callsadd50", |c| {
        c.times("add50(", 3);
    });
}

// --- what our decompiler gets wrong -----------------------------------------
//
// Each of these is a Ghidra datatest that fails here, kept and named after the
// defect rather than deleted. They are the list of what to fix.

/// switchind.xml, switchmask.xml, switchloop.xml, switchmulti.xml,
/// switchhide.xml, ifswitch.xml: a jump table is a `switch`.
///
/// `decompile_program` hands the structurer its tables keyed by the block the
/// indirect branch ends, not by the branch's own address, so the lookup
/// matches and the arms come out as cases rather than as a page of labels.
///
/// Only the x86-64 builds are asserted on: the AArch64 compiler turns this
/// same source into a ladder of compares with no table in it, so there is
/// nothing there for a switch to be recovered from.
///
/// The out-of-range arm is the `else` of the compare that guards the table
/// rather than a `default:` label, because that is where the machine puts it:
/// the indirect branch itself has no successor outside the table.
#[test]
fn switchind() {
    case(&arch("control", "x64"), "switchind", |c| {
        c.has("switch (")
            .at_least("case ", 10)
            .has("0xffffffff")
            .lacks("__indirect_branch");
    });
}

/// switchind.xml on x86-64: the table is not recovered at all. The function is
/// reported incomplete, so it does not reach the decompiler, and the arms are
/// never disassembled. AArch64 recovers the same source's table.
#[test]
fn switchind_x86_64() {
    case(&arch("control", "x64"), "switchind", |c| {
        c.at_least("0x", 1);
    });
}

/// Nested counted loops: both loops survive, with the call inside the inner
/// one.
///
/// The outer loop has no test at its top, so its header is a branch like any
/// other and both of its arms have to be structured. Following only the first
/// successor used to drop every block the other arm reached, which here is the
/// whole inner loop.
#[test]
fn nested_loops() {
    case(&all("control"), "nested", |c| {
        c.at_least("while (", 2).has("sink(");
    });
}

/// forloop_varused.xml: a loop whose body is guarded by a test. The guarded
/// block and the call under it stay inside the loop, which is the same
/// property `nested_loops` pins seen from a second angle: the loop header's
/// branch is structured rather than half-followed.
#[test]
fn forloop_varused() {
    case(&all("control"), "forloop_varused", |c| {
        c.has("while (").has("& 3").has("sink(");
    });
}

/// divopt.xml: division by a constant, which compilers turn into a multiply by
/// a magic reciprocal and a shift. Nothing turns it back, so `x / 81` reads as
/// `x * 0xca4587e7 >> 38`. Seventeen unsigned constants and seventeen signed
/// ones in the original; three of each here.
#[test]
fn divopt() {
    for (f, by) in [
        ("divu81", "/ 81"),
        ("divu99", "/ 99"),
        ("divu125", "/ 125"),
        ("divs81", "/ 81"),
        ("divs99", "/ 99"),
        ("divs125", "/ 125"),
    ] {
        case(&all("arith"), f, |c| {
            c.has(by);
        });
    }
}

/// divopt.xml, the signed power-of-two case: `x / 8` on a signed value is a
/// rounding correction and a shift, and the correction comes out as a
/// `__borrow` of the value against zero rather than as a sign test.
#[test]
fn divopt_signed_power_of_two() {
    case(&all("arith"), "divs8", |c| {
        c.lacks("__borrow");
    });
}

/// modulo.xml and modulo2.xml: the remainder forms built on the same
/// reciprocal, which are not folded either.
#[test]
#[ignore = "reciprocal remainder is not folded back into a modulo"]
fn modulo() {
    for (f, by) in [
        ("modu10", "% 10"),
        ("modu100", "% 100"),
        ("mods3", "% 3"),
        ("mods7", "% 7"),
    ] {
        case(&all("arith"), f, |c| {
            c.has(by);
        });
    }
}

/// statuscmp.xml: all four signed relations reach the output meaning what the
/// branch tests.
///
/// `x != y && y <= x` is `y < x`, and the rewrite that recognizes it used to
/// emit `x < y`, so every `<` and `<=` in a source program came out as its
/// complement. Nothing caught it: the output still compiled, and the
/// interpreter runs the flag algebra rather than this rewrite.
#[test]
fn signed_compare_keeps_its_relation() {
    case(&all("arith"), "cmp_lt", |c| {
        c.has_any(&["<= 4", "4 >= "]);
    });
    case(&all("arith"), "cmp_le", |c| {
        c.has_any(&["<= 5", "5 >= "]);
    });
}

/// lzcount.xml and promotecompare.xml on x86-64: a comparison whose answer is
/// moved out by `setcc` into the low byte of a zeroed register loses the
/// `setcc`, so `return x == 0` decompiles to `return 0`. Four instructions in,
/// a constant out.
#[test]
fn setcc_result_is_dropped() {
    case(&arch("arith", "x64"), "iszero", |c| {
        c.has("== 0");
    });
    case(&arch("arith", "x64"), "promotecompare", |c| {
        c.has("57");
    });
}

/// sbyte.xml, the ordering test: the two equality tests against the loaded byte
/// come out right, and the `>` against 0x61 reads an uninitialized `flag0`
/// instead of the byte. An eight-bit read of a register resolves to a flag
/// varnode rather than to the register's low byte, on both architectures.
///
/// The same defect on the store side loses the value of an AArch64 `strb` of a
/// register, which is why `heapstring` is checked on x86-64 only.
#[test]
fn byte_register_operand_reads_a_flag() {
    case(&all("arith"), "sbyte", |c| {
        c.lacks("flag0");
    });
}

/// nan.xml on x86-64: neither the NaN test nor the ordinary comparison beside
/// it survives; both calls receive the constant zero. The comparison is an
/// `ucomisd` whose answer leaves through `setnp` and `setae`, so this is the
/// floating point face of `setcc_result_is_dropped`.
#[test]
fn nan_x86_64() {
    case(&arch("arith", "x64"), "nanfn", |c| {
        c.has("__isnan");
    });
}

/// floatprint.xml: a `float` constant prints as a decimal with three hundred
/// digits of mantissa, because the 32-bit pattern is widened as if it were a
/// double. Ghidra asks for `0.33333334`; we produce
/// `0.000000...00015460065587`.
#[test]
fn floatprint() {
    case(&all("arith"), "i2f", |c| {
        c.lacks("0.0000000000000000000000000000000");
    });
}

/// floatcast.xml: a `float` widened to `double`, computed on, and narrowed
/// back. The arguments arrive as `(double)(uint32_t)__bits(farg0)`, which reads
/// the bit pattern of the float as an integer and then converts it, so the
/// value is wrong rather than merely ugly.
#[test]
#[ignore = "a float argument is read through its bit pattern instead of its value"]
fn floatcast() {
    case(&all("arith"), "floatcast", |c| {
        c.lacks("(uint32_t)__bits");
    });
}

/// convert.xml: a negative constant prints as an unsigned hexadecimal, so
/// `recv_signed(-512)` reads as `sink2(0xfffffe00)`. Ghidra decides the base
/// and the signedness from the parameter's declared type; we have no type for
/// the parameter, but the narrower fact that a 32-bit constant with the top bit
/// set is more often a small negative number than four billion is still
/// available and unused.
#[test]
#[ignore = "a negative constant prints as an unsigned hexadecimal"]
fn convert() {
    case(&all("arith"), "convert", |c| {
        c.has("-512").has("-3000");
    });
}

/// deindirect.xml and indproto.xml, the argument half: an indirect call comes
/// out as `__callind(target)` with no arguments at all, so `f(b + 3)` loses the
/// `b + 3`. The two calls here also share a target that is a single global
/// holding one function, which Ghidra collapses to a direct call to it.
#[test]
#[ignore = "an indirect call is emitted without its arguments and is never devirtualized"]
fn deindirect() {
    case(&all("calls"), "deindirect", |c| {
        c.has("realfunc").has("+ 3").has("+ 5");
    });
}

/// retstruct.xml: a structure returned in two registers. The two fields are
/// packed into one 64-bit constant expression, `(x * 100) | 0x1e00000000`, so
/// the second field is a bit pattern rather than the value 30.
#[test]
#[ignore = "a structure returned in registers is packed into one integer"]
fn retstruct() {
    case(&all("calls"), "retpair", |c| {
        c.lacks("0x1e00000000");
    });
}

/// switchreturn.xml in the portable form it has here: a function whose last act
/// is a tail call says so. A branch whose target is no block of this function
/// is the callee returning on this function's behalf, and the emitter writes
/// it out as the call and the return it stands for. Nothing marks it in the
/// IR, and a branch is not otherwise a statement, so both used to vanish and
/// the body came out empty.
#[test]
fn tailcall() {
    case(&all("calls"), "tailcall", |c| {
        c.has("realfunc");
    });
}

// --- structuring covers the graph -------------------------------------------

/// Every reachable block of every function of every fixture reaches the output.
///
/// Code that disappears between the control flow graph and the text is the
/// worst thing the structurer can do, because nothing downstream can tell: the
/// output still compiles, still reads as a function, and does less than the
/// function does. `nested_loops`, `forloop_varused` and `tailcall` above are
/// three shapes that lost blocks; this is the check that finds the fourth
/// rather than waiting for someone to notice it.
#[test]
fn no_block_is_lost() {
    let Some(dir) = build_dir() else { return };
    let mut names: Vec<String> = std::fs::read_dir(&dir)
        .into_iter()
        .flatten()
        .flatten()
        .filter(|e| e.file_type().is_ok_and(|t| t.is_file()))
        .map(|e| e.file_name().to_string_lossy().into_owned())
        .collect();
    names.sort();

    let mut lost = 0usize;
    let mut where_from: Vec<String> = Vec::new();
    let mut checked = 0usize;
    for name in names {
        let Some(p) = open(&name) else { continue };
        let targets: Vec<&r12e_analysis::Function> = p
            .functions_by_address()
            .filter(|f| f.is_complete())
            .collect();
        if targets.is_empty() {
            continue;
        }
        for d in r12e_api::decompile_program(&p, &targets).functions {
            checked += 1;
            if d.lost > 0 {
                lost += d.lost;
                where_from.push(format!("{name} {}: {} block(s)", d.name, d.lost));
            }
        }
    }
    assert!(
        lost == 0,
        "{lost} block(s) missing from the output of {checked} functions:\n{}",
        where_from.join("\n")
    );
}
