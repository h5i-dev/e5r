/-
  The (untrusted) analyzer that produces abstract-interpretation certificates.

  It explores the binary with exactly the transfer function the checker uses
  (`E5R.AI.absExec`), so whatever it emits either checks or is rejected.
  Nothing it decides is trusted: splitting, unrolling, widening and the
  choice of G only affect whether the certificate is precise enough.
-/
import Theories.Absint
import Std.Data.HashMap
open E5R E5R.AI

namespace Analyze

def unroll : Nat := 96
def widenAfter : Nat := 4
def nodeLimit : Nat := 400000

/-- G joined with a state's static facts. A guarded fact survives if the
    state has it (or an unconditional version), or knows its guard is false;
    one that has become no better than the unconditional fact is dropped. -/
def joinCells (a b : List Cell) : List Cell :=
  let joined := a.filterMap fun c =>
    match c.guard with
    | none => (plain b c.base c.addr c.w).map fun v => { c with v := c.v.join v }
    | some g =>
      let same := b.find? fun d => d.base == c.base && d.addr == c.addr && d.w == c.w && d.guard == some g
      let off := match plain b .abs g.1 g.2.1 with
        | some x => x.leq (.vals [g.2.2])
        | none => false
      match same with
      | some d => some { c with v := c.v.join d.v }
      | none =>
        if off then some c else
        (plain b c.base c.addr c.w).map fun v => { c with v := c.v.join v }
  -- Guarded facts only `b` states are kept when `a` implies them.
  let fromB := b.filter fun c => c.guard.isSome &&
    !(joined.any fun d => d.base == c.base && d.addr == c.addr && d.w == c.w && d.guard == c.guard) &&
    Cell.leqIn a c
  -- A guarded fact whose value admits the guard's null is useless.
  let r := (joined ++ fromB).filter fun c => match c.guard, c.v with
    | some _, .vals l => !(0 ∈ l)
    | some _, _ => false
    | none, _ => true
  -- `lookup` uses the first fact that applies, so guarded (sharper) facts go first.
  r.filter (·.guard.isSome) ++ r.filter (·.guard.isNone)

def ajoin (a b : AState) : AState :=
  { a with
    regs := List.zipWith AV.join a.regs b.regs
    mem := joinCells a.mem b.mem
    mie := a.mie.join b.mie, mpie := a.mpie.join b.mpie
    mpp := norm (a.mpp ++ b.mpp)
    mieReg := a.mieReg.join b.mieReg, mtvec := a.mtvec.join b.mtvec, mepc := a.mepc.join b.mepc
    mcause := a.mcause.join b.mcause, mscratch := a.mscratch.join b.mscratch }

/-- Join, then send ranges that are still growing to `top`. Value sets are
    bounded by `maxVals` already, so only ranges need widening. -/
def wv (o n : AV) : AV :=
  if n.leq o then o else
  match n with
  | .rng _ _ => .top
  | _ => n

def awiden (old new : AState) : AState :=
  let j := ajoin old new
  { j with
    regs := List.zipWith wv old.regs j.regs
    mem := j.mem.map fun c =>
      match old.mem.find? fun d => d.base == c.base && d.addr == c.addr && d.w == c.w && d.guard == c.guard with
      | some d => { c with v := wv d.v c.v } | none => c
    mieReg := wv old.mieReg j.mieReg, mtvec := wv old.mtvec j.mtvec, mepc := wv old.mepc j.mepc
    mcause := wv old.mcause j.mcause, mscratch := wv old.mscratch j.mscratch }

def nullable (v : AV) : Bool :=
  match v with | .vals l => 0 ∈ l && l.length ≥ 2 | _ => false

/-- Propose guards: a nullable fact may be non-null whenever a nearby
    nullable cell is non-null (an `Option`'s niche, or a future's state
    discriminant). The next rounds keep only the proposals that hold. -/
def proposeGuards (G : List Cell) : List Cell :=
  let cands := G.filter fun c => c.guard.isNone && nullable c.v
  let P := cands.flatMap fun x => (cands.filter fun y =>
      y.addr != x.addr && y.addr + 64 ≥ x.addr && y.addr ≤ x.addr + 64).filterMap fun y =>
    match x.v with
    | .vals l =>
      let c : Cell := { x with v := .vals (l.filter (· ≠ 0)), guard := some (y.addr, y.w, 0) }
      if G.contains c then none else some c
    | _ => none
  -- Guarded facts first: `lookup` takes the first fact that applies.
  P ++ G

/-- Partitioning choices (all untrusted; they only change which nodes exist). -/
structure Opts where
  /-- Split an edge on the base register of the next memory access when it
      holds a few values, so the address and what is loaded through it stay
      related (a task pointer and its poll function). -/
  addrSplit : Bool := false
  /-- How many split values a node remembers. A node's partition is the
      split values still held exactly by some register; partitions are part
      of the context key, so a merge never mixes them. -/
  tagDepth : Nat := 0
  /-- Keep every handler-proof static fact across interrupts, not only
      the ones that rule out a null. -/
  keepAll : Bool := false
  /-- Debugging: when G loses a guarded fact at this address, log the chain
      of nodes that led to the state. -/
  traceLoss : Option Nat := none
  tracePc : Option Nat := none
  /-- Keep only facts about cells G has a guarded fact for (saved pointers). -/
  keepGuarded : Bool := false
  deriving Repr

structure Setup where
  cfg : Config
  boot : AState
  opts : Opts := {}

structure St where
  log : Array String := #[]
  nodes : Array AState := #[]
  /-- The node whose successor created each node (debugging). -/
  pred : Array Nat := #[]
  /-- The node being processed. -/
  cur : Nat := 0
  /-- Each node's partition (see `Opts.tagDepth`). -/
  tags : Array (List Nat) := #[]
  edges : Array (List Edge) := #[]
  index : Std.HashMap String (Array Nat) := {}
  joins : Array Nat := #[]
  work : Array Nat := #[]
  G : Option (List Cell) := none
  restart : Bool := false
  handlers : List (Nat × Nat) := []
  errors : Array String := #[]
  opts : Opts := {}
  /-- The kept intervals the run used. -/
  keep : List (Nat × Nat) := []

abbrev M := StateM St

def emptyState : AState :=
  ⟨0, [], [], .no, .no, [], .top, .top, .top, .top, .top, false⟩

instance : Inhabited AState := ⟨emptyState⟩

def isCode (cfg : Config) (a : Nat) : Bool :=
  cfg.img.any fun s => s.exec && s.base ≤ a && a < s.base + s.bytes.length

/-- Call-context key: stack pointer, return address and the code addresses
    saved on the stack. States with different keys are never merged. -/
def ctxKey (cfg : Config) (s : AState) : String :=
  let code (v : AV) : Option Nat := match v with
    | .vals [x] => if isCode cfg x then some x else none
    | .sym k o => if k = 32 then some (1000000000000 + o) else none
    | _ => none
  let saved := s.mem.filterMap fun c => (code c.v).map fun x => (c.base == .abs, c.addr, x)
  s!"{s.pc}|{s.hnd}|{repr (s.get 2)}|{code (s.get 1)}|{saved}"

/-- Make an interruptible main-thread state fit the handler summary. -/
def normalize (cfg : Config) (t : AState) : M AState := do
  if t.hnd || (irqCodesAbs t).isEmpty then return t
  let S := staticOf cfg t.mem
  let st ← get
  let G ← match st.G with
    | none => do set { st with G := some S }; pure S
    | some G =>
      if G.all (Cell.leqIn S) then pure G
      else do
        let G' := joinCells G S
        let lost := G.filter fun c => !(G'.any fun d => d.addr == c.addr && d.w == c.w && d.v == c.v && d.guard == c.guard)
        let why := (lost.filter (·.guard.isSome)).take 3 |>.map fun (c : Cell) =>
          let g := c.guard.getD (0, .w, 0)
          s!"[{c.addr} if {g.1}≠{g.2.2}: S plain {(plain S c.base c.addr c.w).map reprStr} guard-cell {(plain S .abs g.1 g.2.1).map reprStr}]"
        let chain : List String := match st.opts.traceLoss with
          | some a =>
            if !(lost.any fun c => c.addr == a && c.guard.isSome) then [] else
            let rec go (j : Nat) : Nat → List String
              | 0 => []
              | k+1 =>
                let n := st.nodes[j]!
                let v := n.mem.filter (·.addr == a) |>.map fun c => s!"{reprStr c.v}{if c.guard.isSome then "?" else ""}"
                s!"{j}@{n.pc}:{v}" :: (if j == 0 then [] else go (st.pred[j]!) k)
            s!"t {(t.mem.filter (·.addr == a)).map fun c => reprStr c.v}" :: go st.cur 120
          | none => []
        set { st with G := some G', restart := true,
                      log := st.log.push s!"pc {t.pc} (G {G.length} -> {G'.length}) {why} chain {chain}: G weakens {lost.map fun (c : Cell) => (c.addr, reprStr c.v, (lookup S c.base c.addr c.w).map reprStr)}" }
        pure G'
  let sp := match t.get 2 with | .vals [sp] => sp | _ => 0
  let stack := t.mem.filter fun c => c.base == .abs && c.guard.isNone && !cfg.isStatic c.addr c.w.bytes &&
    sp ≤ c.addr && cfg.isStack c.addr c.w.bytes
  -- Facts the handler cannot change survive the interrupt.
  -- Only a fact that rules out a null G allows is worth a separate node.
  let keepAll := (← get).opts.keepAll
  let keepGuarded := (← get).opts.keepGuarded
  let useful (c : Cell) : Bool := keepAll ||
    (c.guard.isNone && match plain G c.base c.addr c.w, c.v with
      | some g, .vals l => nullable g && !(0 ∈ l) && c.v.leq g &&
        -- `keepGuarded`: only pointers G already knows non-null under some guard.
        (!keepGuarded || G.any fun d => d.addr == c.addr && d.w == c.w && d.guard.isSome)
      | _, _ => false)
  -- With `keepGuarded`, a saved pointer G only knows non-null under a guard
  -- is read the way a load would (through a guard that holds now) and kept
  -- as a plain fact; `Cell.leqIn` accepts it the same way.
  let derived : List Cell := if !keepGuarded then [] else
    ((G.filter (·.guard.isSome)).map fun d => (d.addr, d.w)).eraseDups.filterMap fun (a, wd) =>
      match lookup t.mem .abs a wd with
      | some v => some ⟨.abs, a, wd, v, none⟩
      | none => none
  let kept := ((staticOf cfg t.mem ++ derived).filter fun c =>
    Cell.kept cfg c && !G.contains c && useful c).eraseDups
  if let some a := (← get).opts.traceLoss then
    if (← get).opts.tracePc == some t.pc then
      let cs := (staticOf cfg t.mem ++ derived).filter (·.addr == a)
      modify fun st => { st with log := st.log.push s!"norm pc {t.pc}: {cs.map fun c => (reprStr c.v, c.guard.isSome, Cell.kept cfg c, G.contains c, useful c)} G-guarded {G.any fun d => d.addr == a && d.guard.isSome}" }
  return { t with mem := G ++ kept ++ stack, mepc := .top, mcause := .top,
                  mpie := t.mpie.join .yes, mpp := norm (t.mpp ++ [0]) }

def newNode (key : String) (tag : List Nat) (t : AState) : M Nat := do
  let st ← get
  let j := st.nodes.size
  set { st with nodes := st.nodes.push t, tags := st.tags.push tag, pred := st.pred.push st.cur, edges := st.edges.push [], joins := st.joins.push 0,
                work := st.work.push j,
                index := st.index.insert key ((st.index.getD key #[]).push j) }
  return j

/-- Debug aid: the guarded fact `E5R_TRACE=addr:guardaddr` names. -/
def traceSpec : Option (Nat × Nat) := none

def traceFact (s : AState) : Bool :=
  match traceSpec with
  | some (a, g) => s.mem.any fun c => c.addr == a && (c.guard.map (·.1)) == some g
  | none => false

def grow (j : Nat) (t : AState) : M Unit := do
  let st ← get
  let old := st.nodes[j]!
  let k := st.joins[j]!
  let new := if k < widenAfter then ajoin old t else awiden old t
  if traceFact old && !traceFact new then
    modify fun st => { st with log := st.log.push s!"grow node {j} pc {old.pc} hnd {old.hnd} loses the traced fact: incoming has it {traceFact t}; joins {k}" }
  let st ← get
  set { st with nodes := st.nodes.set! j new, joins := st.joins.set! j (k+1),
                work := st.work.push j }

/-- The node that covers `t`, creating or growing one. -/
def resolve (cfg : Config) (tag : List Nat) (t : AState) : M Nat := do
  let t ← normalize cfg t
  -- A partition lasts while some register still holds its value exactly.
  let tag := tag.filter fun v => t.regs.any (· == .vals [v])
  let key := s!"{ctxKey cfg t}|{tag}"
  let st ← get
  let cands := st.index.getD key #[]
  match cands.find? fun j => t.leq st.nodes[j]! with
  | some j => return j
  | none =>
    -- A state that subsumes an existing node replaces it rather than using
    -- up the budget: an ascending chain of value sets is one node, not many.
    match cands.find? fun j => st.nodes[j]!.leq t with
    | some j => grow j t; return j
    | none =>
    if cands.size < unroll then newNode key tag t
    else
      let j := cands.back!
      grow j t
      return j

def loadDest : Instr → Option Reg
  | .load _ _ rd _ _ => some rd
  | .lr rd _ => some rd
  | .amo _ rd _ _ => some rd
  | _ => none

/-- The base register of a memory access. -/
def addrReg : Instr → Option Reg
  | .load _ _ _ rs1 _ => some rs1
  | .store _ rs1 _ _ => some rs1
  | .lr _ rs1 => some rs1
  | .sc _ rs1 _ => some rs1
  | .amo _ _ rs1 _ => some rs1
  | _ => none

def splittable (v : AV) : Option (List Nat) :=
  match v with
  | .vals l => if 2 ≤ l.length ∧ l.length ≤ 8 then some l else none
  | _ => none

def edgeFor (cfg : Config) (tag : List Nat) (s : AState) (i : Instr) (t : AState) : M Edge := do
  let opts := (← get).opts
  let sub (v : Nat) : List Nat := (v :: tag.erase v).take opts.tagDepth
  -- Split a freshly loaded small value set, so that later arithmetic on it
  -- is exact per value (this is what keeps wrap-around indices in range).
  -- A word loaded from an exact address is pinned in memory as well, which
  -- is what lets a guard on it apply.
  let pinAt : Option (Nat × Width) := match i with
    | .load wd signed _ rs1 off =>
      if signed && wd != .w then none else
      match addC (s.get rs1) off.toNat with
      | .vals [a] =>
        if classify cfg a wd == some .ram && (!s.hnd || cfg.isStatic a wd.bytes) then some (a, wd) else none
      | _ => none
    | _ => none
  let single : M Edge := do return { nodes := [← resolve cfg tag t], split := none, pin := false }
  -- Otherwise split on the next access's base register.
  let byAddr : M Edge := do
    if !opts.addrSplit then single else
    match successors.fetchDecode' cfg.img t.pc with
    | some (ni, _) =>
      match addrReg ni with
      | some r =>
        match splittable (t.get r) with
        | some l =>
          if r.val = 0 then single else
          let js ← l.mapM fun v => resolve cfg (sub v) (t.set r (.vals [v]))
          return { nodes := js, split := some r.val, pin := false }
        | none => single
      | none => single
    | none => single
  match loadDest i with
  | some rd =>
    match t.get rd with
    | .vals l =>
      -- With `keepGuarded`, a single loaded value is pinned too, so a pointer
      -- read through a guard becomes a plain fact that can be kept.
      if (2 ≤ l.length || (opts.keepGuarded && l.length == 1 && pinAt.isSome)) ∧ l.length ≤ 8 ∧ rd.val ≠ 0 then
        let js ← l.mapM fun v =>
          let t' := t.set rd (.vals [v])
          resolve cfg (sub v) (match pinAt with
            | some (a, wd) => { t' with mem := setPlain t'.mem a wd (.vals [v]) }
            | none => t')
        return { nodes := js, split := some rd.val, pin := pinAt.isSome }
      else byAddr
    | _ => byAddr
  | none => byAddr

def err (msg : String) : M Unit := modify fun st => { st with errors := st.errors.push msg }

def brief (s : AState) : String :=
  let rs := (List.range 31).filterMap fun k =>
    let v := s.regs.getD k .top
    if v == .top then none else some s!"x{k+1}={reprStr v}"
  let ms := s.mem.map fun c => s!"{if c.base == .abs then "" else "rel"}{c.addr}{reprStr c.w}={reprStr c.v}{match c.guard with | some g => s!"?{g.1}" | none => ""}"
  s!"hnd={s.hnd} mie={reprStr s.mie} regs {rs} mem {ms}"

def process (cfg : Config) (i : Nat) : M Unit := do
  modify fun st => { st with cur := i }
  let s := (← get).nodes[i]!
  match successors.fetchDecode' cfg.img s.pc with
  | none => err s!"node {i}: no instruction at {s.pc}"
  | some (.mret, _) =>
    let st ← get
    let G := st.G.getD []
    if !G.all (Cell.leqIn s.mem) then
      let G' := joinCells G (staticOf cfg s.mem)
      let lost := G.filter fun c => !(G'.any fun d => d.addr == c.addr && d.w == c.w && d.v == c.v && d.guard == c.guard)
      let S := s.mem
      let why := (lost.filter (·.guard.isSome)).take 4 |>.map fun (c : Cell) =>
          let g := c.guard.getD (0, .w, 0)
          s!"[{c.addr} if {g.1}≠{g.2.2}: S plain {(plain S c.base c.addr c.w).map reprStr} guard-cell {(plain S .abs g.1 g.2.1).map reprStr} same {(S.find? fun d => d.addr == c.addr && d.guard == c.guard).map (reprStr ·.v)}]"
      let msg := s!"mret node {i} {why}: G weakens {lost.map fun (c : Cell) => (c.addr, reprStr c.v, (lookup s.mem c.base c.addr c.w).map reprStr)}"
      set { st with G := some G', restart := true, log := st.log.push msg }
    if !mretOk cfg { nodes := [], G := (← get).G.getD [], sigma := [], handlers := [] } s then
      err s!"node {i}: mret does not restore the interrupted machine: {brief s}"
  | some (ins, len) =>
    -- A registered summary that accepts the state replaces the instruction.
    match cfg.sums.find? fun S => !s.hnd && S.pc == s.pc && S.accepts s && !(S.post s).hnd with
    | some S =>
      let e : Edge := { nodes := [← resolve cfg (← get).tags[i]! (S.post s)], split := none, pin := false }
      modify fun st => { st with edges := st.edges.set! i [e] }
    | none =>
    match absExec cfg s len ins with
    | none => err s!"node {i}: {reprStr ins} at {s.pc} may fault: {brief s}"
    | some ts =>
      let tag := (← get).tags[i]!
      let es ← ts.mapM (edgeFor cfg tag s ins)
      modify fun st => { st with edges := st.edges.set! i es }
  -- Interrupts.
  let codes := irqCodesAbs s
  if !codes.isEmpty then
    if s.hnd then err s!"node {i}: interrupt possible inside the handler"
    for code in codes do
      let G := (← get).G.getD []
      match handlerEntry G s code with
      | none => err s!"node {i}: unknown trap vector {repr s.mtvec}"
      | some e =>
        match (← get).handlers.lookup code with
        | some j => if !e.leq (← get).nodes[j]! then grow j e
        | none =>
          let j ← newNode s!"handler {code}" [] e
          modify fun st => { st with handlers := st.handlers ++ [(code, j)] }

partial def drain (cfg : Config) : M Unit := do
  let st ← get
  if st.nodes.size > nodeLimit then return
  match st.work.back? with
  | none => return
  | some i =>
    set { st with work := st.work.pop }
    process cfg i
    drain cfg

def runOnce (su : Setup) (G : Option (List Cell)) : St :=
  let act : M Unit := do
    let _ ← resolve su.cfg [] su.boot
    drain su.cfg
  (act.run { G := G, opts := su.opts }).2

partial def fixG (su : Setup) (G : Option (List Cell)) (round : Nat) (proposed : Bool) : IO St := do
  let st := runOnce su G
  IO.eprintln s!"round {round}: {st.nodes.size} nodes, {st.errors.size} errors, restart {st.restart}, G {(st.G.getD []).length} cells"
  if (← IO.getEnv "E5R_ANALYZE_DEBUG").isSome then
    for l in st.log do IO.eprintln s!"  {l}"
    IO.eprintln s!"  G: {(st.G.getD []).map fun c => (c.addr, reprStr c.w, reprStr c.v, c.guard.isSome)}"
    let gs := (st.G.getD []).filter (·.guard.isSome)
    IO.eprintln s!"  guarded: {gs.map fun c => (c.addr, reprStr c.v, c.guard.map fun g => (g.1, reprStr g.2.1, g.2.2))}"
  -- Debug aid: `E5R_DUMP_PC=<pc>` prints that pc's nodes after every round.
  if let some pcs ← IO.getEnv "E5R_DUMP_PC" then
    for pc in (pcs.splitOn ",").filterMap String.toNat? do
      for s in st.nodes.toList.filter (·.pc == pc) do IO.eprintln s!"dump round {round}: {brief s}"
  if round ≥ 60 then return st
  if st.restart then fixG su st.G (round+1) proposed
  else if !proposed && st.errors.size > 0 then
    match st.G with
    | some G =>
      let P := proposeGuards G
      IO.eprintln s!"  proposed {P.length - G.length} guarded facts"
      fixG su (some P) (round+1) true
    | none => return st
  else return st

/-! ## What the handler leaves alone -/

/-- Bytes a handler node's store may write, or `none` if unbounded. Stores
    relative to the interrupted sp are the handler's own frame. -/
def storeBytes (cfg : Config) (s : AState) : Option (List Nat) :=
  let at_ (v : AV) (n : Nat) : Option (List Nat) := match v with
    | .vals l => some (l.flatMap fun a => (List.range n).map (a + ·))
    | .rng lo hi => some ((List.range (hi + n - lo)).map (lo + ·))
    | .sym 2 _ => some []
    | _ => none
  match successors.fetchDecode' cfg.img s.pc with
  | some (.store wd rs1 _ off, _) => at_ (addC (s.get rs1) off.toNat) wd.bytes
  | some (.amo _ _ rs1 _, _) => at_ (s.get rs1) 4
  | some (.sc _ rs1 _, _) => at_ (s.get rs1) 4
  | _ => some []

/-- The handler's static footprint over a run, or `none` if unbounded. -/
def footprint (cfg : Config) (st : St) : Option (List Nat) :=
  st.nodes.toList.filter (·.hnd) |>.foldlM (init := []) fun acc s =>
    (storeBytes cfg s).map (acc ++ ·)

/-- Static RAM minus `fp`, as maximal intervals. -/
def keepOf (cfg : Config) (fp : List Nat) : List (Nat × Nat) := Id.run do
  let fp := Std.HashSet.ofList fp
  let mut out : Array (Nat × Nat) := #[]
  for (lo, hi) in [(cfg.board.ramBase, cfg.stackLow), (cfg.pinLow, cfg.ramEnd)] do
    let mut start : Option Nat := none
    for a in [lo:hi] do
      if fp.contains a then
        if let some b := start then out := out.push (b, a)
        start := none
      else if start.isNone then start := some a
    if let some b := start then out := out.push (b, hi)
  return out.toList

/-- Analyze until the kept intervals the run assumed are ones its handler
    leaves alone. Each round only shrinks them. -/
partial def analyzeKeep (su : Setup) (fp : List Nat) (round : Nat := 0) : IO St := do
  -- Round 0 keeps nothing, so that the whole handler is explored.
  let keep := if round = 0 then [] else keepOf su.cfg fp
  IO.eprintln s!"keep round {round}: {keep.length} intervals, footprint {fp.length} bytes"
  let st ← fixG { su with cfg := { su.cfg with hkeep := keep } } none 0 false
  match footprint su.cfg st with
  | none =>
    IO.eprintln "handler footprint unbounded: nothing is kept"
    if keep.isEmpty then return st
    fixG { su with cfg := { su.cfg with hkeep := [] } } none 0 false
  | some fp' =>
    let fresh := (fp'.filter (!fp.contains ·)).eraseDups
    IO.eprintln s!"  keep {keep.map fun (a, b) => (String.ofList (Nat.toDigits 16 a), b - a)}; new footprint {(fresh.take 40).map fun a => String.ofList (Nat.toDigits 16 a)}"
    if (round > 0 && fresh.isEmpty) || round ≥ 8 then return { st with keep := keep }
    analyzeKeep su (fp ++ fresh) (round + 1)

/-! ## Output -/

def avStr : AV → String
  | .top => "T"
  | .vals l => s!"(V {l})"
  | .rng lo hi => s!"(R {lo} {hi})"
  | .sym s o => s!"(S {s} {o})"

def wStr : Width → String
  | .b => ".b" | .h => ".h" | .w => ".w"

def cellStr (c : Cell) : String :=
  let g := match c.guard with | none => "none" | some (a, gw, v) => s!"some ({a}, {wStr gw}, {v})"
  s!"⟨{if c.base == .abs then ".abs" else ".rel"}, {c.addr}, {wStr c.w}, {avStr c.v}, {g}⟩"

def triStr : Tri → String
  | .no => ".no" | .yes => ".yes" | .any => ".any"

def listStr (l : List String) : String := "[" ++ ", ".intercalate l ++ "]"

def stateStr (s : AState) : String :=
  s!"⟨{s.pc}, {listStr (s.regs.map avStr)}, {listStr (s.mem.map cellStr)}, {triStr s.mie}, " ++
  s!"{triStr s.mpie}, {s.mpp}, {avStr s.mieReg}, {avStr s.mtvec}, {avStr s.mepc}, " ++
  s!"{avStr s.mcause}, {avStr s.mscratch}, {s.hnd}⟩"

def edgeStr (e : Edge) : String :=
  s!"⟨{e.nodes}, {match e.split with | none => "none" | some r => s!"some {r}"}, {e.pin}⟩"

/-- One declaration per chunk of nodes keeps elaboration linear. -/
def certSource (ns : String) (st : St) (sigma : List Nat) : String := Id.run do
  let chunk := 64
  let n := st.nodes.size
  let mut out := s!"-- Generated by tools/Analyze.lean; regenerate, do not edit.\n" ++
    "import Theories.Absint\nset_option maxRecDepth 100000\n" ++
    s!"namespace {ns}\nopen E5R E5R.AI\n" ++
    "local notation \"T\" => AV.top\nlocal notation \"V\" => AV.vals\n" ++
    "local notation \"R\" => AV.rng\nlocal notation \"S\" => AV.sym\n"
  let mut parts : Array String := #[]
  for c in [0:(n + chunk - 1) / chunk] do
    let lo := c * chunk
    let hi := min n (lo + chunk)
    let items := (List.range (hi - lo)).map fun k =>
      let j := lo + k
      s!"  ⟨{stateStr st.nodes[j]!}, {listStr (st.edges[j]!.map edgeStr)}⟩"
    out := out ++ s!"def part{c} : List Node := [\n" ++ ",\n".intercalate items ++ "]\n"
    parts := parts.push s!"part{c}"
  out := out ++ s!"def G : List Cell := {listStr ((st.G.getD []).map cellStr)}\n"
  let joined := " ++ ".intercalate parts.toList
  out := out ++ s!"def cert : Cert where\n  nodes := {joined}\n"
  out := out ++ s!"  G := G\n  sigma := {sigma}\n  handlers := {st.handlers}\n  hkeep := {st.keep}\n"
  out := out ++ s!"end {ns}\n"
  return out

end Analyze
