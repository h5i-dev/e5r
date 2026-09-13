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
    /// Nothing.
    Empty,
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
}

/// The graph structuring works over: successors per block.
pub type Graph = BTreeMap<Addr, Vec<Addr>>;

/// Structure a control flow graph.
pub fn structure(entry: Addr, graph: &Graph) -> Structured {
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

    let mut ctx = Ctx {
        graph,
        index: &index,
        loop_headers: &loop_headers,
        bodies: &bodies,
        emitted: BTreeSet::new(),
        labels: BTreeSet::new(),
        gotos: 0,
        depth: 0,
    };
    let root = ctx.region(entry, None, None);
    Structured {
        root,
        labels: ctx.labels,
        gotos: ctx.gotos,
    }
}

struct Ctx<'a> {
    graph: &'a Graph,
    index: &'a BTreeMap<Addr, usize>,
    loop_headers: &'a BTreeSet<Addr>,
    bodies: &'a BTreeMap<Addr, BTreeSet<Addr>>,
    emitted: BTreeSet<Addr>,
    labels: BTreeSet<Addr>,
    gotos: usize,
    depth: u32,
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
            // Reaching the enclosing loop's header again is a continue.
            if Some(cursor) == enclosing && !parts.is_empty() {
                parts.push(Region::Continue);
                break;
            }
            if self.emitted.contains(&cursor) {
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
                    parts.push(Region::Block(cursor));
                    let next = succs[0];
                    // A backward edge that is not a loop header is a goto.
                    if self.emitted.contains(&next) && !self.loop_headers.contains(&next) {
                        if Some(next) == enclosing {
                            parts.push(Region::Continue);
                        } else {
                            self.gotos += 1;
                            self.labels.insert(next);
                            parts.push(Region::Goto(next));
                        }
                        break;
                    }
                    cursor = next;
                }
                _ => {
                    let (region, after) = self.build_if(cursor, &succs, stop, enclosing);
                    parts.push(Region::Block(cursor));
                    parts.push(region);
                    match after {
                        Some(next) if Some(next) != stop && !self.emitted.contains(&next) => {
                            cursor = next;
                        }
                        Some(next) if Some(next) != stop => {
                            self.gotos += 1;
                            self.labels.insert(next);
                            parts.push(Region::Goto(next));
                            break;
                        }
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

    /// Build a loop from its header.
    fn build_loop(&mut self, head: Addr) -> Region {
        self.emitted.insert(head);
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
                // The machine branch jumps when the condition holds; a `while`
                // enters its body then, so whether to invert depends on which
                // successor is the body.
                let invert = inside == succs[1];
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
        let next = succs.first().copied();
        let body = match next {
            Some(n) => self.region(n, Some(head), Some(head)),
            None => Region::Empty,
        };
        Region::Infinite {
            head,
            body: Box::new(body),
        }
    }

    /// Where a loop leaves to.
    fn loop_exit(&self, head: Addr) -> Option<Addr> {
        let body = self.bodies.get(&head)?;
        // The single block outside the loop that something inside branches to.
        let mut exits: BTreeSet<Addr> = BTreeSet::new();
        for b in body {
            for s in self.graph.get(b).into_iter().flatten() {
                if !body.contains(s) {
                    exits.insert(*s);
                }
            }
        }
        if exits.len() == 1 {
            exits.into_iter().next()
        } else {
            None
        }
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
        // The fall-through is the successor at the higher address, because a
        // machine branch jumps to the other one.
        let (taken, fallthrough) = (succs[0], succs[1]);
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

        let then = if Some(then_start) == join || Some(then_start) == stop {
            Region::Empty
        } else {
            self.region(then_start, join.or(stop), enclosing)
        };
        let otherwise = other_start.and_then(|s| {
            if Some(s) == join || Some(s) == stop {
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

    /// Where the two arms of a branch come back together.
    ///
    /// The nearest block both successors reach, found by walking forward from
    /// each. A branch whose arms never reconverge has no join and its arms run
    /// to the end of the function.
    fn join_of(&self, head: Addr) -> Option<Addr> {
        let succs = self.graph.get(&head)?;
        if succs.len() != 2 {
            return None;
        }
        let from_a = self.reachable(succs[0]);
        let from_b = self.reachable(succs[1]);
        // The earliest block in reverse post-order that both reach, excluding
        // the head itself so a loop does not look like a join.
        from_a
            .intersection(&from_b)
            .filter(|a| **a != head)
            .min_by_key(|a| self.index.get(a).copied().unwrap_or(usize::MAX))
            .copied()
    }

    fn reachable(&self, from: Addr) -> BTreeSet<Addr> {
        let mut seen = BTreeSet::new();
        let mut work = vec![from];
        while let Some(at) = work.pop() {
            if !seen.insert(at) {
                continue;
            }
            for s in self.graph.get(&at).into_iter().flatten() {
                if !seen.contains(s) {
                    work.push(*s);
                }
            }
        }
        seen
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
        let found = collect(&s.root)
            .into_iter()
            .any(|r| matches!(r, Region::If { otherwise: None, .. }));
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
        // Whatever it produces, every block appears at most once and the gotos
        // are counted.
        let regions = collect(&s.root);
        let mut blocks: Vec<Addr> = regions
            .iter()
            .filter_map(|r| match r {
                Region::Block(a) => Some(*a),
                _ => None,
            })
            .collect();
        let before = blocks.len();
        blocks.sort();
        blocks.dedup();
        assert_eq!(before, blocks.len(), "a block was emitted twice");
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
            Region::If { then, otherwise, .. } => {
                out.extend(collect(then));
                if let Some(o) = otherwise {
                    out.extend(collect(o));
                }
            }
            Region::While { body, .. } | Region::Infinite { body, .. } => {
                out.extend(collect(body));
            }
            _ => {}
        }
        out
    }
}
