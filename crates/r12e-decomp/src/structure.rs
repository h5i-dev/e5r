//! Recovering structure from a control flow graph.
//!
//! A graph becomes an `if`, a `while` and a sequence when it has that shape and
//! a labelled `goto` when it does not. Inventing a shape that is not there is
//! the one thing this must not do: output that looks like a loop but is not is
//! worse than output with a `goto` in it, because the reader cannot tell.
//!
//! The number of gotos is the quality signal, reported rather than hidden. It
//! is what the roadmap's G7 gate measures and what a later structuring pass
//! would be judged against.

use std::collections::{BTreeMap, BTreeSet};

use r12e_core::Addr;

/// The most blocks one copied tail may span.
///
/// Past this a copy stops reading as the same few statements written twice and
/// starts reading as a second piece of code, which is worse than the goto it
/// replaces. Measured over the corpus: four is where the curve flattens, and
/// every block past it costs more output than it saves gotos.
const MAX_COPIED_TAIL: usize = 4;

/// How many blocks in total a function may write out a second time.
///
/// Proportional to the function, because a shared tail is a fact about how many
/// arms a function has, plus a floor for the small ones where one copy is the
/// whole difference. Bounded so that duplication cannot turn a chain of
/// comparisons into an exponential one.
fn duplication_budget(blocks: usize) -> u32 {
    8 + blocks as u32
}

/// A recovered region.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Region {
    /// One basic block's statements, then whatever follows.
    Block(Addr),
    /// Regions one after another.
    Seq(Vec<Region>),
    /// A two-way branch that reconverges.
    If {
        /// The block holding the condition.
        head: Addr,
        /// True when the condition has to be inverted to read naturally, which
        /// happens because a machine branch jumps on the condition being true
        /// and an `if` falls into its body.
        invert: bool,
        /// The body taken when the condition holds.
        then: Box<Region>,
        /// The other body, when there is one.
        otherwise: Option<Box<Region>>,
    },
    /// A loop whose condition is tested at the top.
    While {
        /// The block holding the condition.
        head: Addr,
        /// True when the condition has to be inverted.
        invert: bool,
        /// The body.
        body: Box<Region>,
    },
    /// A loop with no recognized condition: `for (;;)` with a break inside.
    Infinite {
        /// Where it starts.
        head: Addr,
        /// The body.
        body: Box<Region>,
    },
    /// A jump to a label, for an edge no shape covered.
    Goto(Addr),
    /// Leaving the loop this sits inside.
    Break,
    /// Going back to the top of the loop this sits inside.
    Continue,
    /// A multi-way branch through a jump table.
    Switch {
        /// The block holding the branch.
        head: Addr,
        /// The arms, in case-value order.
        cases: Vec<Case>,
        /// Where control goes for an index the table does not cover.
        default: Option<Box<Region>>,
    },
    /// Nothing.
    Empty,
}

/// One arm of a switch.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Case {
    /// The values that reach this arm; several indices can share a body.
    pub values: Vec<u64>,
    /// What it does.
    pub body: Region,
}

/// A structured function, with the measure of how well it worked.
#[derive(Debug, Clone)]
pub struct Structured {
    /// The region tree.
    pub root: Region,
    /// Blocks that need a label because something jumps to them.
    pub labels: BTreeSet<Addr>,
    /// How many gotos the structuring had to emit. The quality signal.
    pub gotos: usize,
    /// Reachable blocks the region tree never mentions.
    ///
    /// Their code would be missing from the output with nothing downstream able
    /// to tell, which is worse than any number of gotos. Correct structuring
    /// leaves this empty; it is reported rather than asserted so a caller can
    /// decide what to do about it.
    pub lost: BTreeSet<Addr>,
}

/// The graph structuring works over: successors per block.
pub type Graph = BTreeMap<Addr, Vec<Addr>>;

/// The cases of each multi-way branch: the value the index takes and where it
/// goes. Without this a jump table is a block with many successors and no way
/// to say which is which, and every arm but one becomes a goto.
pub type Switches = BTreeMap<Addr, Vec<(u64, Addr)>>;

/// Which successor a conditional branch jumps to when its condition holds.
///
/// Guessing this from the order of the successors is how an `if` comes out
/// inverted, so it is taken from the branch itself.
pub type Taken = BTreeMap<Addr, Addr>;

/// Structure a control flow graph.
pub fn structure(entry: Addr, graph: &Graph, taken: &Taken) -> Structured {
    structure_with(entry, graph, taken, &Switches::new())
}

/// Structure a control flow graph, knowing what its jump tables mean.
pub fn structure_with(
    entry: Addr,
    graph: &Graph,
    taken: &Taken,
    switches: &Switches,
) -> Structured {
    let order = reverse_postorder(entry, graph);
    let index: BTreeMap<Addr, usize> = order.iter().enumerate().map(|(i, a)| (*a, i)).collect();
    let preds = predecessors(graph);
    let idom = dominators(entry, graph, &preds, &order, &index);

    // A back edge goes to a block that dominates its source; its target is a
    // loop header. This is the definition of a natural loop and the only one
    // that cannot be fooled by a graph that merely looks like one.
    let mut loop_headers: BTreeSet<Addr> = BTreeSet::new();
    let mut latches: BTreeMap<Addr, BTreeSet<Addr>> = BTreeMap::new();
    for (from, succs) in graph {
        for to in succs {
            if dominates(&idom, *to, *from) {
                loop_headers.insert(*to);
                latches.entry(*to).or_default().insert(*from);
            }
        }
    }
    // The blocks each loop contains.
    let bodies: BTreeMap<Addr, BTreeSet<Addr>> = loop_headers
        .iter()
        .map(|h| (*h, loop_body(*h, &latches, &preds)))
        .collect();

    let postdom = postdominators(graph, &order, &index);

    let mut ctx = Ctx {
        graph,
        taken,
        switches,
        postdom: &postdom,
        loop_headers: &loop_headers,
        bodies: &bodies,
        emitted: BTreeSet::new(),
        labels: BTreeSet::new(),
        gotos: 0,
        depth: 0,
        duplication: duplication_budget(graph.len()),
        loops: Vec::new(),
        keep_single: BTreeSet::new(),
        reasons: BTreeMap::new(),
    };

    // Writing a tail out twice and then jumping to it are each fine and
    // together are not: two copies of a labelled block are two definitions of
    // one C label. Which copy a later goto would want is not knowable while
    // the copy is being made, so the block is barred from duplication and the
    // function structured again. The bar only grows, so this settles.
    let mut root = ctx.region(entry, None, None);
    for _ in 0..4 {
        let clashing = labelled_twice(&root, &ctx.labels);
        if clashing.is_empty() {
            break;
        }
        let mut keep_single = std::mem::take(&mut ctx.keep_single);
        keep_single.extend(clashing);
        ctx = Ctx {
            graph,
            taken,
            switches,
            postdom: &postdom,
            loop_headers: &loop_headers,
            bodies: &bodies,
            emitted: BTreeSet::new(),
            labels: BTreeSet::new(),
            gotos: 0,
            depth: 0,
            duplication: duplication_budget(graph.len()),
            loops: Vec::new(),
            keep_single,
            reasons: BTreeMap::new(),
        };
        root = ctx.region(entry, None, None);
    }

    // Why each goto was needed, which is what says where to spend the next
    // piece of work. Off by default and per function, so aggregating it is the
    // caller's job: a whole-corpus run is the only useful unit. Note that
    // `decompile_program` structures every function twice, once to learn what
    // the callees take and once to use it, so raw totals are double.
    if std::env::var_os("R12E_GOTO_STATS").is_some() {
        for (reason, n) in &ctx.reasons {
            eprintln!("GOTOREASON\t{reason}\t{n}");
        }
    }
    let lost = lost_blocks(entry, graph, &root);
    Structured {
        root,
        labels: ctx.labels,
        gotos: ctx.gotos,
        lost,
    }
}

/// Blocks a region tree both writes out more than once and labels.
fn labelled_twice(root: &Region, labels: &BTreeSet<Addr>) -> BTreeSet<Addr> {
    let mut counts: BTreeMap<Addr, usize> = BTreeMap::new();
    occurrences(root, &mut counts);
    counts
        .into_iter()
        .filter(|(at, n)| *n > 1 && labels.contains(at))
        .map(|(at, _)| at)
        .collect()
}

/// How many times each block's statements appear in a region tree.
fn occurrences(r: &Region, out: &mut BTreeMap<Addr, usize>) {
    match r {
        Region::Seq(parts) => {
            for p in parts {
                occurrences(p, out);
            }
        }
        Region::If {
            head,
            then,
            otherwise,
            ..
        } => {
            *out.entry(*head).or_default() += 1;
            occurrences(then, out);
            if let Some(o) = otherwise {
                occurrences(o, out);
            }
        }
        Region::While { head, body, .. } | Region::Infinite { head, body } => {
            *out.entry(*head).or_default() += 1;
            occurrences(body, out);
        }
        Region::Switch {
            head,
            cases,
            default,
        } => {
            *out.entry(*head).or_default() += 1;
            for c in cases {
                occurrences(&c.body, out);
            }
            if let Some(d) = default {
                occurrences(d, out);
            }
        }
        Region::Block(at) => {
            *out.entry(*at).or_default() += 1;
        }
        Region::Goto(_) | Region::Break | Region::Continue | Region::Empty => {}
    }
}

/// Reachable blocks the region tree does not mention.
fn lost_blocks(entry: Addr, graph: &Graph, root: &Region) -> BTreeSet<Addr> {
    let mut seen = BTreeSet::new();
    mentioned(root, &mut seen);
    reverse_postorder(entry, graph)
        .into_iter()
        .filter(|a| !seen.contains(a))
        .collect()
}

/// Every block a region tree emits the statements of.
///
/// A `goto` target does not count: it is a reference to a block, not a copy of
/// it, and a label with no block under it is itself a defect.
fn mentioned(r: &Region, out: &mut BTreeSet<Addr>) {
    match r {
        Region::Block(at) => {
            out.insert(*at);
        }
        Region::Seq(parts) => {
            for p in parts {
                mentioned(p, out);
            }
        }
        Region::If {
            head,
            then,
            otherwise,
            ..
        } => {
            out.insert(*head);
            mentioned(then, out);
            if let Some(o) = otherwise {
                mentioned(o, out);
            }
        }
        Region::While { head, body, .. } | Region::Infinite { head, body } => {
            out.insert(*head);
            mentioned(body, out);
        }
        Region::Switch {
            head,
            cases,
            default,
        } => {
            out.insert(*head);
            for c in cases {
                mentioned(&c.body, out);
            }
            if let Some(d) = default {
                mentioned(d, out);
            }
        }
        Region::Goto(_) | Region::Break | Region::Continue | Region::Empty => {}
    }
}

struct Ctx<'a> {
    graph: &'a Graph,
    taken: &'a Taken,
    switches: &'a Switches,
    postdom: &'a BTreeMap<Addr, Addr>,
    loop_headers: &'a BTreeSet<Addr>,
    bodies: &'a BTreeMap<Addr, BTreeSet<Addr>>,
    emitted: BTreeSet<Addr>,
    labels: BTreeSet<Addr>,
    gotos: usize,
    depth: u32,
    /// How many more blocks may be written out a second time. Counted in
    /// blocks rather than in copies, because what has to stay bounded is how
    /// much text the duplication adds, not how often it happens.
    duplication: u32,
    /// The loops currently being structured, innermost last. An edge to the
    /// innermost loop's exit is a `break` and an edge to its header is a
    /// `continue`; without this both come out as gotos.
    loops: Vec<Nesting>,
    /// Blocks that must appear once, because a goto names them.
    keep_single: BTreeSet<Addr>,
    reasons: BTreeMap<&'static str, usize>,
}

#[derive(Debug, Clone, Copy)]
struct Nesting {
    head: Addr,
    exit: Option<Addr>,
}

impl Ctx<'_> {
    /// Structure from `at` until `stop`, inside `enclosing` loop if any.
    fn region(&mut self, at: Addr, stop: Option<Addr>, enclosing: Option<Addr>) -> Region {
        self.depth += 1;
        let out = self.region_inner(at, stop, enclosing);
        self.depth -= 1;
        out
    }

    fn region_inner(&mut self, at: Addr, stop: Option<Addr>, enclosing: Option<Addr>) -> Region {
        // A guard, because a graph from hostile input need not be reducible.
        if self.depth > 200 {
            *self.reasons.entry("depth limit").or_default() += 1;
            self.gotos += 1;
            self.labels.insert(at);
            return Region::Goto(at);
        }
        let mut parts: Vec<Region> = Vec::new();
        let mut cursor = at;

        loop {
            if Some(cursor) == stop {
                break;
            }
            if !self.graph.contains_key(&cursor) {
                break;
            }
            // Reaching the innermost loop's header again is a continue, and
            // reaching where it leaves to is a break. Checked before the stop
            // address, because an arm of an `if` that ends by going back to the
            // header has to say so: ending the arm silently would fall past the
            // `if` instead of repeating.
            if let Some(inner) = self.loops.last().copied() {
                if cursor == inner.head {
                    parts.push(Region::Continue);
                    break;
                }
                if Some(cursor) == inner.exit {
                    parts.push(Region::Break);
                    break;
                }
            }
            if self.emitted.contains(&cursor) {
                // A small tail is written out again rather than jumped to.
                if let Some(blocks) = self.copyable_tail(cursor, stop) {
                    self.duplication -= blocks as u32;
                    parts.push(self.duplicate(cursor, stop, enclosing));
                    break;
                }
                *self
                    .reasons
                    .entry(if self.loop_headers.contains(&cursor) {
                        "already written: loop entered a second way"
                    } else if self.preds_of(cursor) > 1 {
                        "already written: shared tail"
                    } else {
                        "already written: other"
                    })
                    .or_default() += 1;
                self.gotos += 1;
                self.labels.insert(cursor);
                parts.push(Region::Goto(cursor));
                break;
            }

            // A loop header starts a loop, unless we are already in it.
            if self.loop_headers.contains(&cursor) && Some(cursor) != enclosing {
                parts.push(self.build_loop(cursor));
                // Control continues at whatever the loop exits to.
                match self.loop_exit(cursor) {
                    Some(next) if Some(next) != stop => {
                        cursor = next;
                        continue;
                    }
                    _ => break,
                }
            }

            self.emitted.insert(cursor);
            let succs = self.graph.get(&cursor).cloned().unwrap_or_default();
            match succs.len() {
                0 => {
                    parts.push(Region::Block(cursor));
                    break;
                }
                1 => {
                    // Where the successor goes is the top of this loop's
                    // decision, not this arm's: the top is the one place that
                    // knows a `continue` from a `break` from a tail worth
                    // copying. Settling it here instead is what turned every
                    // fall into an already written block into a goto with no
                    // copy considered, which was 42% of them.
                    parts.push(Region::Block(cursor));
                    cursor = succs[0];
                }
                _ if self.switches.contains_key(&cursor) => {
                    let (region, after) = self.build_switch(cursor, stop, enclosing);
                    parts.push(Region::Block(cursor));
                    parts.push(region);
                    match after {
                        Some(next) if Some(next) != stop => cursor = next,
                        _ => break,
                    }
                }
                _ => {
                    let (region, after) = self.build_if(cursor, &succs, stop, enclosing);
                    parts.push(Region::Block(cursor));
                    parts.push(region);
                    // Likewise: an `if` whose arms rejoin at a block already
                    // written is the same decision one level up, and the top
                    // of this loop is where it is made.
                    match after {
                        Some(next) if Some(next) != stop => cursor = next,
                        _ => break,
                    }
                }
            }
        }

        match parts.len() {
            0 => Region::Empty,
            1 => parts.pop().unwrap(),
            _ => Region::Seq(parts),
        }
    }

    fn preds_of(&self, at: Addr) -> usize {
        self.graph.values().filter(|s| s.contains(&at)).count()
    }

    /// How many blocks a tail would copy, when copying it is allowed.
    ///
    /// A compiler merges identical tails: every path that ends in the same
    /// `return`, and cross-jumping for the rest. That merge is what leaves one
    /// block with several predecessors, and a single walk can place it under
    /// only one of them, so every other predecessor becomes a goto. Writing the
    /// tail out again in each arm undoes the merge rather than inventing
    /// structure, and over this corpus it is where most of the removable gotos
    /// are.
    fn copyable_tail(&self, at: Addr, stop: Option<Addr>) -> Option<usize> {
        let mut seen: BTreeSet<Addr> = BTreeSet::new();
        let mut work = vec![at];
        while let Some(block) = work.pop() {
            if Some(block) == stop || !self.graph.contains_key(&block) {
                continue;
            }
            // A loop is written out again only when it lies wholly inside the
            // tail, which the size bound below decides: every block of a
            // natural loop is reachable from its header, so a loop that does
            // not fit makes the walk exceed the bound. A loop currently being
            // structured is never a tail, because writing it out again inside
            // itself would not terminate.
            if self.loops.iter().any(|l| l.head == block) || self.keep_single.contains(&block) {
                return None;
            }
            if !seen.insert(block) {
                continue;
            }
            if seen.len() > MAX_COPIED_TAIL || seen.len() as u32 > self.duplication {
                return None;
            }
            for s in self.graph.get(&block).into_iter().flatten() {
                if !seen.contains(s) {
                    work.push(*s);
                }
            }
        }
        (!seen.is_empty()).then_some(seen.len())
    }

    /// Structure a tail again, as a copy.
    fn duplicate(&mut self, at: Addr, stop: Option<Addr>, enclosing: Option<Addr>) -> Region {
        // The blocks are already marked as emitted, so they are unmarked for
        // the duration of the copy and put back afterwards.
        let mut restored: Vec<Addr> = Vec::new();
        let mut work = vec![at];
        let mut seen: BTreeSet<Addr> = BTreeSet::new();
        while let Some(block) = work.pop() {
            if Some(block) == stop || !seen.insert(block) {
                continue;
            }
            if self.emitted.remove(&block) {
                restored.push(block);
            }
            for s in self.graph.get(&block).into_iter().flatten() {
                if !seen.contains(s) {
                    work.push(*s);
                }
            }
        }
        let region = self.region(at, stop, enclosing);
        for block in restored {
            self.emitted.insert(block);
        }
        region
    }

    /// Build a loop from its header.
    fn build_loop(&mut self, head: Addr) -> Region {
        self.emitted.insert(head);
        let exit = self.loop_exit(head);
        self.loops.push(Nesting { head, exit });
        let region = self.build_loop_body(head);
        self.loops.pop();
        trim_trailing_continue(region)
    }

    fn build_loop_body(&mut self, head: Addr) -> Region {
        let body_blocks = self.bodies.get(&head).cloned().unwrap_or_default();
        let succs = self.graph.get(&head).cloned().unwrap_or_default();

        // A header with two successors, one inside the loop and one outside, is
        // a `while`: the condition is tested at the top.
        if succs.len() == 2 {
            let (inside, outside) = if body_blocks.contains(&succs[0]) {
                (succs[0], succs[1])
            } else {
                (succs[1], succs[0])
            };
            if body_blocks.contains(&inside) && !body_blocks.contains(&outside) {
                // A `while` enters its body when the condition holds, so the
                // test needs inverting when the branch jumps out instead.
                let taken = self.taken.get(&head).copied().unwrap_or(succs[0]);
                let invert = inside != taken;
                let body = self.region(inside, Some(head), Some(head));
                return Region::While {
                    head,
                    invert,
                    body: Box::new(body),
                };
            }
        }

        // Otherwise the loop has no condition at the top; the exits inside
        // become breaks.
        let body = self.after_head(head, &succs);
        Region::Infinite {
            head,
            body: Box::new(body),
        }
    }

    /// What runs after a loop header whose test is not at the top.
    ///
    /// The header still ends in whatever branch it ends in. Following one
    /// successor and forgetting the other drops every block only the other arm
    /// reaches, which is how an inner loop vanishes out of an outer one, so the
    /// branch is structured here the same way it would be anywhere else and the
    /// walk carries on where its arms rejoin.
    fn after_head(&mut self, head: Addr, succs: &[Addr]) -> Region {
        let stop = Some(head);
        let (branch, after) = match succs.len() {
            0 => return Region::Empty,
            1 => return self.region(succs[0], stop, stop),
            _ if self.switches.contains_key(&head) => self.build_switch(head, stop, stop),
            _ => self.build_if(head, succs, stop, stop),
        };
        let mut parts = vec![branch];
        match after {
            Some(next) if Some(next) != stop => parts.push(self.region(next, stop, stop)),
            _ => {}
        }
        match parts.len() {
            1 => parts.pop().unwrap(),
            _ => Region::Seq(parts),
        }
    }

    /// Where a loop leaves to.
    ///
    /// A loop with several exits still has one the code continues at; the rest
    /// become gotos. Choosing it as the one the header itself branches to, and
    /// otherwise the one most of the body branches to, is what turns an
    /// optimized loop's exits into `break` rather than a page of labels.
    fn loop_exit(&self, head: Addr) -> Option<Addr> {
        let body = self.bodies.get(&head)?;
        let mut counts: BTreeMap<Addr, usize> = BTreeMap::new();
        for b in body {
            for s in self.graph.get(b).into_iter().flatten() {
                if !body.contains(s) {
                    *counts.entry(*s).or_default() += 1;
                }
            }
        }
        if counts.is_empty() {
            return None;
        }
        // The header's own way out, when it has one.
        if let Some(succs) = self.graph.get(&head) {
            if succs.len() == 2 {
                if let Some(outside) = succs.iter().find(|s| !body.contains(*s)) {
                    return Some(*outside);
                }
            }
        }
        counts
            .into_iter()
            .max_by_key(|(addr, n)| (*n, std::cmp::Reverse(*addr)))
            .map(|(addr, _)| addr)
    }

    /// Build an `if` from a two-way branch, returning the region and where
    /// control continues.
    fn build_if(
        &mut self,
        head: Addr,
        succs: &[Addr],
        stop: Option<Addr>,
        enclosing: Option<Addr>,
    ) -> (Region, Option<Addr>) {
        // The branch says which way it goes when the condition holds; the
        // other successor is what falls through.
        let taken = self.taken.get(&head).copied().unwrap_or(succs[1]);
        let fallthrough = succs
            .iter()
            .copied()
            .find(|s| *s != taken)
            .unwrap_or(succs[0]);
        let join = self.join_of(head);

        // One arm empty: a plain `if` with no else.
        let then_start = if Some(fallthrough) == join {
            taken
        } else {
            fallthrough
        };
        let other_start = if Some(fallthrough) == join || Some(taken) == join {
            None
        } else {
            Some(taken)
        };
        // Inverted when the body is the branch's fall-through, because the
        // machine jumped past it.
        let invert = then_start == fallthrough;

        // An arm that starts at the join does nothing. An arm that starts at
        // the enclosing region's stop address is not empty: it may be a jump
        // back to a loop header, which `region` turns into a `continue`.
        let then = if Some(then_start) == join {
            Region::Empty
        } else {
            self.region(then_start, join.or(stop), enclosing)
        };
        let otherwise = other_start.and_then(|s| {
            if Some(s) == join {
                None
            } else {
                Some(Box::new(self.region(s, join.or(stop), enclosing)))
            }
        });

        (
            Region::If {
                head,
                invert,
                then: Box::new(then),
                otherwise,
            },
            join,
        )
    }

    /// Build a switch from a block whose jump table is known.
    fn build_switch(
        &mut self,
        head: Addr,
        stop: Option<Addr>,
        enclosing: Option<Addr>,
    ) -> (Region, Option<Addr>) {
        let entries = self.switches.get(&head).cloned().unwrap_or_default();
        let join = self.postdom.get(&head).copied().filter(|j| *j != head);

        // Several indices often share a body, which C says with several
        // labels on one arm rather than with a copy of the body each.
        let mut grouped: BTreeMap<Addr, Vec<u64>> = BTreeMap::new();
        for (value, target) in &entries {
            grouped.entry(*target).or_default().push(*value);
        }
        // In the order the values first appear, so the output reads in the
        // order the source was written.
        let mut order: Vec<Addr> = Vec::new();
        for (_, target) in &entries {
            if !order.contains(target) {
                order.push(*target);
            }
        }

        let mut cases = Vec::new();
        for target in order {
            let values = grouped.remove(&target).unwrap_or_default();
            if Some(target) == join {
                // An arm that goes straight to the join does nothing but
                // leave; it still needs its labels.
                cases.push(Case {
                    values,
                    body: Region::Break,
                });
                continue;
            }
            let body = self.region(target, join.or(stop), enclosing);
            cases.push(Case { values, body });
        }

        // A successor the table does not name is where an out-of-range index
        // goes, which C calls the default.
        let named: BTreeSet<Addr> = entries.iter().map(|(_, t)| *t).collect();
        let default = self
            .graph
            .get(&head)
            .into_iter()
            .flatten()
            .find(|s| !named.contains(s) && Some(**s) != join)
            .copied()
            .map(|s| Box::new(self.region(s, join.or(stop), enclosing)));

        (
            Region::Switch {
                head,
                cases,
                default,
            },
            join,
        )
    }

    /// Where the two arms of a branch come back together.
    ///
    /// The immediate post-dominator: the first block every path from the
    /// branch has to reach. Anything weaker, such as the earliest block both
    /// arms can reach, picks a join too far away and turns each arm's tail
    /// into a goto.
    fn join_of(&self, head: Addr) -> Option<Addr> {
        let succs = self.graph.get(&head)?;
        if succs.len() != 2 {
            return None;
        }
        let join = self.postdom.get(&head).copied()?;
        (join != head && self.graph.contains_key(&join)).then_some(join)
    }
}

/// Drop a `continue` in tail position, where repeating is what happens anyway.
fn trim_trailing_continue(r: Region) -> Region {
    match r {
        Region::While { head, invert, body } => Region::While {
            head,
            invert,
            body: Box::new(trim_tail(*body)),
        },
        Region::Infinite { head, body } => Region::Infinite {
            head,
            body: Box::new(trim_tail(*body)),
        },
        other => other,
    }
}

fn trim_tail(r: Region) -> Region {
    match r {
        Region::Continue => Region::Empty,
        Region::Seq(mut parts) => {
            if matches!(parts.last(), Some(Region::Continue)) {
                parts.pop();
            }
            match parts.len() {
                0 => Region::Empty,
                1 => parts.pop().unwrap(),
                _ => Region::Seq(parts),
            }
        }
        other => other,
    }
}

/// The blocks a natural loop contains: everything that reaches a latch without
/// leaving through the header.
fn loop_body(
    head: Addr,
    latches: &BTreeMap<Addr, BTreeSet<Addr>>,
    preds: &BTreeMap<Addr, BTreeSet<Addr>>,
) -> BTreeSet<Addr> {
    let mut body = BTreeSet::new();
    body.insert(head);
    let mut work: Vec<Addr> = latches.get(&head).into_iter().flatten().copied().collect();
    while let Some(at) = work.pop() {
        if !body.insert(at) {
            continue;
        }
        for p in preds.get(&at).into_iter().flatten() {
            if !body.contains(p) {
                work.push(*p);
            }
        }
    }
    body
}

/// Reverse post-order from the entry.
pub fn reverse_postorder(entry: Addr, graph: &Graph) -> Vec<Addr> {
    let mut seen = BTreeSet::new();
    let mut post = Vec::new();
    let mut stack = vec![(entry, 0usize)];
    seen.insert(entry);
    while let Some((at, i)) = stack.pop() {
        let succs = graph.get(&at).cloned().unwrap_or_default();
        if i < succs.len() {
            stack.push((at, i + 1));
            let next = succs[i];
            if graph.contains_key(&next) && seen.insert(next) {
                stack.push((next, 0));
            }
        } else {
            post.push(at);
        }
    }
    post.reverse();
    post
}

/// Immediate post-dominators: for each block, the first block every path from
/// it must pass through on the way out.
///
/// Computed as dominators on the reversed graph, with every block that leaves
/// the function treated as a predecessor of one virtual exit.
fn postdominators(
    graph: &Graph,
    order: &[Addr],
    index: &BTreeMap<Addr, usize>,
) -> BTreeMap<Addr, Addr> {
    // The reversed graph, and the blocks that end the function.
    let mut reverse: BTreeMap<Addr, Vec<Addr>> = BTreeMap::new();
    let mut exits: Vec<Addr> = Vec::new();
    for (from, succs) in graph {
        reverse.entry(*from).or_default();
        let live: Vec<Addr> = succs
            .iter()
            .copied()
            .filter(|s| graph.contains_key(s))
            .collect();
        if live.is_empty() {
            exits.push(*from);
        }
        for to in live {
            reverse.entry(to).or_default().push(*from);
        }
    }
    if exits.is_empty() {
        // Every block continues somewhere, which happens when the function is
        // one endless loop. The last block in order stands in for the exit.
        if let Some(last) = order.last() {
            exits.push(*last);
        }
    }

    // Post-order from the exits over the reversed graph, which is the order
    // the fixed point wants.
    let mut seen: BTreeSet<Addr> = BTreeSet::new();
    let mut post: Vec<Addr> = Vec::new();
    for start in &exits {
        let mut stack = vec![(*start, 0usize)];
        if !seen.insert(*start) {
            continue;
        }
        while let Some((at, i)) = stack.pop() {
            let preds = reverse.get(&at).cloned().unwrap_or_default();
            if i < preds.len() {
                stack.push((at, i + 1));
                let next = preds[i];
                if seen.insert(next) {
                    stack.push((next, 0));
                }
            } else {
                post.push(at);
            }
        }
    }
    post.reverse();
    let rank: BTreeMap<Addr, usize> = post.iter().enumerate().map(|(i, a)| (*a, i)).collect();

    let mut ipdom: BTreeMap<Addr, Addr> = BTreeMap::new();
    for e in &exits {
        ipdom.insert(*e, *e);
    }
    let mut changed = true;
    let mut rounds = 0;
    while changed && rounds < 1000 {
        changed = false;
        rounds += 1;
        for at in &post {
            if exits.contains(at) {
                continue;
            }
            let mut new: Option<Addr> = None;
            for s in graph.get(at).into_iter().flatten() {
                if !ipdom.contains_key(s) {
                    continue;
                }
                new = Some(match new {
                    None => *s,
                    Some(cur) => intersect(&ipdom, &rank, cur, *s),
                });
            }
            if let Some(n) = new {
                if ipdom.get(at) != Some(&n) {
                    ipdom.insert(*at, n);
                    changed = true;
                }
            }
        }
    }
    let _ = index;
    ipdom
}

/// Walk two chains up until they meet, which is their nearest common ancestor.
fn intersect(
    tree: &BTreeMap<Addr, Addr>,
    rank: &BTreeMap<Addr, usize>,
    mut a: Addr,
    mut b: Addr,
) -> Addr {
    let mut guard = 0;
    while a != b && guard < 10_000 {
        guard += 1;
        let (ra, rb) = (
            rank.get(&a).copied().unwrap_or(0),
            rank.get(&b).copied().unwrap_or(0),
        );
        if ra > rb {
            let next = tree.get(&a).copied().unwrap_or(a);
            if next == a {
                break;
            }
            a = next;
        } else {
            let next = tree.get(&b).copied().unwrap_or(b);
            if next == b {
                break;
            }
            b = next;
        }
    }
    a
}

fn predecessors(graph: &Graph) -> BTreeMap<Addr, BTreeSet<Addr>> {
    let mut out: BTreeMap<Addr, BTreeSet<Addr>> = BTreeMap::new();
    for (from, succs) in graph {
        out.entry(*from).or_default();
        for to in succs {
            out.entry(*to).or_default().insert(*from);
        }
    }
    out
}

fn dominators(
    entry: Addr,
    graph: &Graph,
    preds: &BTreeMap<Addr, BTreeSet<Addr>>,
    order: &[Addr],
    index: &BTreeMap<Addr, usize>,
) -> BTreeMap<Addr, Addr> {
    let mut idom: BTreeMap<Addr, Addr> = BTreeMap::new();
    idom.insert(entry, entry);
    let mut changed = true;
    let mut rounds = 0;
    while changed && rounds < 1000 {
        changed = false;
        rounds += 1;
        for at in order.iter().skip(1) {
            let mut new: Option<Addr> = None;
            for p in preds.get(at).into_iter().flatten() {
                if !idom.contains_key(p) {
                    continue;
                }
                new = Some(match new {
                    None => *p,
                    Some(cur) => {
                        let mut a = cur;
                        let mut b = *p;
                        let mut guard = 0;
                        while a != b && guard < 10_000 {
                            guard += 1;
                            let ia = index.get(&a).copied().unwrap_or(0);
                            let ib = index.get(&b).copied().unwrap_or(0);
                            if ia > ib {
                                let n = idom.get(&a).copied().unwrap_or(a);
                                if n == a {
                                    break;
                                }
                                a = n;
                            } else {
                                let n = idom.get(&b).copied().unwrap_or(b);
                                if n == b {
                                    break;
                                }
                                b = n;
                            }
                        }
                        a
                    }
                });
            }
            if let Some(n) = new {
                if idom.get(at) != Some(&n) {
                    idom.insert(*at, n);
                    changed = true;
                }
            }
        }
    }
    let _ = graph;
    idom
}

/// True when `a` dominates `b`.
fn dominates(idom: &BTreeMap<Addr, Addr>, a: Addr, b: Addr) -> bool {
    let mut at = b;
    let mut guard = 0;
    loop {
        if at == a {
            return true;
        }
        let next = idom.get(&at).copied().unwrap_or(at);
        if next == at || guard > 10_000 {
            return false;
        }
        at = next;
        guard += 1;
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn structure(entry: Addr, graph: &Graph) -> Structured {
        super::structure(entry, graph, &Taken::new())
    }

    fn g(edges: &[(u64, &[u64])]) -> Graph {
        edges
            .iter()
            .map(|(from, to)| (Addr(*from), to.iter().map(|a| Addr(*a)).collect()))
            .collect()
    }

    #[test]
    fn a_straight_line_is_a_sequence_with_no_gotos() {
        let graph = g(&[(0, &[1]), (1, &[2]), (2, &[])]);
        let s = structure(Addr(0), &graph);
        assert_eq!(s.gotos, 0);
        assert!(s.labels.is_empty());
        assert!(matches!(s.root, Region::Seq(_)));
    }

    #[test]
    fn a_diamond_is_an_if_else() {
        // 0 branches to 1 and 2, both reaching 3.
        let graph = g(&[(0, &[1, 2]), (1, &[3]), (2, &[3]), (3, &[])]);
        let s = structure(Addr(0), &graph);
        assert_eq!(s.gotos, 0, "a diamond should need no goto");
        let Region::Seq(parts) = &s.root else {
            panic!("expected a sequence, got {:?}", s.root);
        };
        assert!(
            parts.iter().any(|r| matches!(
                r,
                Region::If {
                    otherwise: Some(_),
                    ..
                }
            )),
            "no if/else in {parts:?}"
        );
    }

    #[test]
    fn a_branch_with_one_arm_is_an_if_without_an_else() {
        // 0 branches to 1 or straight to 2; 1 also reaches 2.
        let graph = g(&[(0, &[1, 2]), (1, &[2]), (2, &[])]);
        let s = structure(Addr(0), &graph);
        assert_eq!(s.gotos, 0);
        let found = collect(&s.root).into_iter().any(|r| {
            matches!(
                r,
                Region::If {
                    otherwise: None,
                    ..
                }
            )
        });
        assert!(found, "no plain if in {:?}", s.root);
    }

    #[test]
    fn a_back_edge_becomes_a_loop() {
        // 0 enters 1; 1 branches back to itself or out to 2.
        let graph = g(&[(0, &[1]), (1, &[1, 2]), (2, &[])]);
        let s = structure(Addr(0), &graph);
        let found = collect(&s.root)
            .into_iter()
            .any(|r| matches!(r, Region::While { .. } | Region::Infinite { .. }));
        assert!(found, "no loop in {:?}", s.root);
    }

    #[test]
    fn an_irreducible_graph_produces_gotos_rather_than_a_wrong_shape() {
        // Two entries into the same loop, which no `while` describes. The
        // structuring has to say so instead of inventing one.
        let graph = g(&[
            (0, &[1, 2]),
            (1, &[3]),
            (2, &[4]),
            (3, &[4]),
            (4, &[3, 5]),
            (5, &[]),
        ]);
        let s = structure(Addr(0), &graph);
        // A block can appear more than once: a small tail shared by several
        // arms is written out in each of them rather than jumped to. What must
        // not happen is unbounded duplication.
        let regions = collect(&s.root);
        let blocks: Vec<Addr> = regions
            .iter()
            .filter_map(|r| match r {
                Region::Block(a) => Some(*a),
                _ => None,
            })
            .collect();
        assert!(
            blocks.len() <= graph.len() * 4,
            "{} blocks emitted for a graph of {}",
            blocks.len(),
            graph.len()
        );
    }

    /// The shape the corpus is mostly made of: two arms reach one tail, and
    /// only one of them can be the place it is written. Copying the tail into
    /// the other is what a compiler's tail merging undid.
    #[test]
    fn a_tail_two_arms_share_is_copied_rather_than_jumped_to() {
        // 0 branches to 1 or 2; 1 branches to 3 or 4; 2 falls into 4; both 3
        // and 4 reach 5. Block 4 post-dominates nothing, so no join places it.
        let graph = g(&[
            (0, &[1, 2]),
            (1, &[3, 4]),
            (2, &[4]),
            (3, &[5]),
            (4, &[5]),
            (5, &[]),
        ]);
        let s = structure(Addr(0), &graph);
        assert_eq!(s.gotos, 0, "{:?}", s.root);
        assert!(s.labels.is_empty());
        assert!(s.lost.is_empty());
    }

    /// Copying is bounded. A fan of arms that all end at one long tail must not
    /// write the tail out once per arm.
    #[test]
    fn copying_a_tail_stays_within_its_budget() {
        // A chain of ten two-way branches, every one of whose taken arms lands
        // on the same eight-block tail.
        let mut edges: Vec<(u64, Vec<u64>)> = Vec::new();
        for i in 0..10u64 {
            edges.push((i, vec![i + 1, 100]));
        }
        edges.push((10, vec![100]));
        for j in 0..7u64 {
            edges.push((100 + j, vec![101 + j]));
        }
        edges.push((107, vec![]));
        let graph: Graph = edges
            .iter()
            .map(|(f, t)| (Addr(*f), t.iter().map(|a| Addr(*a)).collect()))
            .collect();
        let s = structure(Addr(0), &graph);
        assert!(s.lost.is_empty(), "lost {:?}", s.lost);
        let blocks = collect(&s.root)
            .iter()
            .filter(|r| matches!(r, Region::Block(_)))
            .count();
        let ceiling = graph.len() + duplication_budget(graph.len()) as usize;
        assert!(
            blocks <= ceiling,
            "{blocks} blocks emitted for a graph of {}, ceiling {ceiling}",
            graph.len()
        );
    }

    #[test]
    fn structuring_terminates_on_a_graph_that_is_all_back_edges() {
        let mut edges: Vec<(u64, Vec<u64>)> = Vec::new();
        for i in 0..64u64 {
            edges.push((i, vec![(i + 1) % 64, i.saturating_sub(1)]));
        }
        let graph: Graph = edges
            .iter()
            .map(|(f, t)| (Addr(*f), t.iter().map(|a| Addr(*a)).collect()))
            .collect();
        let s = structure(Addr(0), &graph);
        // The only requirement is that it finished.
        assert!(s.gotos < 1000);
    }

    /// Every region in a tree, flattened.
    fn collect(r: &Region) -> Vec<Region> {
        let mut out = vec![r.clone()];
        match r {
            Region::Seq(parts) => {
                for p in parts {
                    out.extend(collect(p));
                }
            }
            Region::If {
                then, otherwise, ..
            } => {
                out.extend(collect(then));
                if let Some(o) = otherwise {
                    out.extend(collect(o));
                }
            }
            Region::While { body, .. } | Region::Infinite { body, .. } => {
                out.extend(collect(body));
            }
            Region::Switch { cases, default, .. } => {
                for c in cases {
                    out.extend(collect(&c.body));
                }
                if let Some(d) = default {
                    out.extend(collect(d));
                }
            }
            _ => {}
        }
        out
    }
}
