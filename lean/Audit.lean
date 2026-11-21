import Examples
import Demo
import Lean

/-
`lake build nocompiler-audit && lake exe nocompiler-audit` (from lean/): the checks that tie
the proofs to the binaries, and the axiom audit.

At run time, `main`
* reads each committed ELF file with the Lean reader in NoCompiler/Elf.lean
  and checks that its `.text` is word for word the image the proofs are
  about, and every data section byte for byte the exported segment;
* checks each module against the ELF it is linked into (layout, `Module.Ok`,
  `Module.link`, data);
* audits the axioms of EVERY declaration of every module under NoCompiler/,
  Examples/ and Demo/ (found from the source tree, not from a list;
  `Audit.audit` below): standard, the bv_decide tier (printed), or forbidden
  (fails), and fails if a source file's module was not built;
* fails if committed source turns on `nocompiler_auto`'s debugging option, which
  closes goals with `sorry`;
* fails on a theorem under `Examples.` that concludes `RefinesRel`, a
  refinement without A's run (`Audit.bareRefinesRel`).
-/
/-
The axiom audit (docs/isa/trust.md, "The audit"): every declaration of every
module of the project, found from the source tree, not from a list.

Each declaration's transitive axioms are classified:

* **standard**: only `propext`, `Classical.choice`, `Quot.sound`;
* **bv_decide tier**: the standard three plus axioms of native computation
  (`Lean.ofReduceBool`, `Lean.trustCompiler`, and the per-theorem
  `<thm>._native.*` axioms Lean 4.35 generates for `bv_decide` and
  `native_decide`), at least one of them. Such a theorem rests on the compiled
  evaluation of a certificate checker as well as on the kernel;
* **forbidden**: anything else, `sorryAx` included, and any axiom the project
  declares itself.

The audit fails on a forbidden declaration and prints the bv_decide tier.
-/
namespace Audit
open Lean

def standardAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]

/-- An axiom of native computation. -/
def isNativeAxiom (n : Name) : Bool :=
  n == `Lean.ofReduceBool || n == `Lean.trustCompiler || n.components.any (· == `_native)

inductive Tier | standard | bvDecide | forbidden
  deriving DecidableEq, Repr

def classify (axs : Array Name) : Tier :=
  if axs.all standardAxioms.contains then .standard
  else if axs.all (fun a => standardAxioms.contains a || isNativeAxiom a) then .bvDecide
  else .forbidden

/-- The axioms a constant depends on, memoised across constants. -/
partial def axiomsOf (env : Environment) (n : Name) :
    StateM (Std.HashMap Name (Array Name)) (Array Name) := do
  if let some r := (← get)[n]? then return r
  -- Mark first: a recursive or mutual group refers back to itself.
  modify (·.insert n #[])
  let some ci := env.find? n | return #[]
  let r ← match ci with
    | .axiomInfo _ => pure #[n]
    | _ =>
      let mut acc : Std.HashSet Name := {}
      for c in ci.getUsedConstantsAsSet do
        if c != n then
          for a in ← axiomsOf env c do acc := acc.insert a
      pure acc.toArray
  modify (·.insert n r)
  return r

structure Report where
  checked : Nat
  bvTier : Array Name
  forbidden : Array (Name × Array Name)

/-- Audit every constant whose module is one of `mods`. -/
def audit (env : Environment) (mods : Std.HashSet Name) : Report := Id.run do
  let mut cache : Std.HashMap Name (Array Name) := {}
  let mut checked := 0
  let mut bv := #[]
  let mut bad := #[]
  for (n, _) in env.constants.map₁.toList do
    let some idx := env.getModuleIdxFor? n | continue
    let some m := env.header.moduleNames[idx.toNat]? | continue
    unless mods.contains m do continue
    let (axs, c) := (axiomsOf env n).run cache
    cache := c
    checked := checked + 1
    match classify axs with
    | .standard => pure ()
    | .bvDecide => if !n.isInternal then bv := bv.push n
    | .forbidden => bad := bad.push (n, axs)
  return { checked, bvTier := bv.qsort (·.toString < ·.toString),
           forbidden := bad.qsort (·.1.toString < ·.1.toString) }

/-- A type's conclusion: under its `∀`s and `→`s. -/
partial def conclusion : Expr → Expr
  | .forallE _ _ b _ => conclusion b
  | .mdata _ e => conclusion e
  | e => e

/-- The conjuncts of a proposition. -/
partial def conjuncts (e : Expr) : List Expr :=
  if e.isAppOfArity ``And 2 then conjuncts e.appFn!.appArg! ++ conjuncts e.appArg! else [e]

/-- A's arguments (the type, the spec, `cA`, `DA`, `eA`) of `c` applied in `e`. -/
def aArgs (c : Name) (e : Expr) : Option (Array Expr) :=
  if e.isAppOf c && e.getAppNumArgs ≥ 5 then some (e.getAppArgs.extract 0 5) else none

/-- Decision 2026-11-21 (3): a refinement is stated as `Refines`, which carries
    A's run (`ARuns`); `RefinesRel` alone is conditional on A's run and holds
    vacuously of an A that never runs. So every theorem under `Examples.` that
    concludes `RefinesRel` (or a conjunction with it) is reported, unless the
    project also proves `¬ ARuns` of the same A, the same closed arguments:
    then it is a demonstration that the relation alone is vacuous (a control),
    not a claimed refinement. -/
def bareRefinesRel (env : Environment) (mods : Std.HashSet Name) : Array Name := Id.run do
  let mut noRuns : Array (Array Expr) := #[]
  let mut rels : Array (Name × Array Expr) := #[]
  for (n, ci) in env.constants.map₁.toList do
    let some idx := env.getModuleIdxFor? n | continue
    let some m := env.header.moduleNames[idx.toNat]? | continue
    unless mods.contains m do continue
    let .thmInfo t := ci | continue
    for c in conjuncts (conclusion t.type) do
      if c.isAppOfArity ``Not 1 then
        if let some a := aArgs `NoCompiler.ARuns c.appArg! then
          if !a.any (·.hasLooseBVars) then noRuns := noRuns.push a
      if (`Examples).isPrefixOf n then
        if let some a := aArgs `NoCompiler.RefinesRel c then rels := rels.push (n, a)
  let bad := rels.filterMap fun (n, a) =>
    if !a.any (·.hasLooseBVars) && noRuns.any (· == a) then none else some n
  return bad.qsort (·.toString < ·.toString)

/-- The modules of the project: every `.lean` file under the given roots
    (`NoCompiler`, `Examples`, `Demo`, and their root files), as module names. -/
partial def sourceModules (lean : System.FilePath) (roots : List String) : IO (Array Name) := do
  let mut out := #[]
  for r in roots do
    if ← (lean / s!"{r}.lean").pathExists then out := out.push (Name.mkSimple r)
    let dir := lean / r
    if ← dir.isDir then
      for p in ← dir.walkDir do
        if p.extension == some "lean" then
          let cs := (p.toString.toList.drop (lean.toString.length + 1))
          let rel := String.ofList (cs.take (cs.length - 5))
          out := out.push ((rel.splitOn "/").foldl (fun n c => .str n c) .anonymous)
  return out.qsort (·.toString < ·.toString)

/-- Lines of committed source that turn on `nocompiler_auto`'s debugging option
    (`set_option nocompiler.auto.debugKernel true`), which closes what the tactic
    leaves with `sorry`: none may exist. -/
def debugOptionUses (lean : System.FilePath) (mods : Array Name) : IO (Array String) := do
  let mut out := #[]
  for m in mods do
    let p := (m.components.foldl (fun p c => p / c.toString) lean).addExtension "lean"
    let src ← IO.FS.readFile p
    for (l, i) in (src.splitOn "\n").zipIdx do
      let words := (l.splitOn " ").filter (· ≠ "")
      if words.take 3 == ["set_option", "nocompiler.auto.debugKernel", "true"] then
        out := out.push s!"{p}:{i + 1}: {l}"
  return out

end Audit

open NoCompiler


-- The Lean checker rejects what breaks the rules: `sum` without its tree
-- (its branches then have no structured target), with the loop recorded as a
-- block, and `write_all` claimed one instruction longer (falling into hello).
example : Struct.check Examples.Sum.Image.code ⟨0x11190#64, 9, []⟩ Examples.Sum.Image.entries = false := by
  decide
example : Struct.check Examples.Sum.Image.code
    ⟨0x11190#64, 9, [⟨.block, 0x11194#64, 0x111ac#64⟩, ⟨.block, 0x11198#64, 0x111ac#64⟩]⟩
    Examples.Sum.Image.entries = false := by decide
example : Struct.check Examples.Hello.Image.code
    { Examples.Hello.Image.write_all_func with len := 12 } Examples.Hello.Image.entries = false := by
  decide
-- `sum2` with no function entries known: its calls go nowhere allowed.
example : Struct.check Examples.Sum.Image.code Examples.Sum.Image.sum2_func [] = false := by decide




/-- Each committed binary (relative to the repository root), and the code
    image and data segments its proofs use. -/
def images : List (String × Code × List Segment) :=
  [("examples/elf/sum.elf", Examples.Sum.Image.code, Examples.Sum.Image.segments),
   ("examples/elf/hello.elf", Examples.Hello.Image.code, Examples.Hello.Image.segments),
   ("examples/demo/elf/sum.b.elf", Demo.Sum.ImageB.code, Demo.Sum.ImageB.segments),
   ("examples/demo/elf/cobs.b.elf", Demo.Cobs.ImageB.code, Demo.Cobs.ImageB.segments),
   ("examples/elf/sum.link1.elf", Examples.Link.Img1.code, Examples.Link.Img1.segments),
   ("examples/elf/sum.link2.elf", Examples.Link.Img2.code, Examples.Link.Img2.segments),
   ("examples/elf/refine-sum-a.elf", Examples.Refine.Diff.ImgA.code, Examples.Refine.Diff.ImgA.segments),
   ("examples/elf/refine-sum-b.elf", Examples.Refine.Diff.ImgB.code, Examples.Refine.Diff.ImgB.segments),
   ("examples/elf/refine-sum-c.elf", Examples.Refine.Diff.ImgC.code, Examples.Refine.Diff.ImgC.segments),
   ("examples/elf/refine-sum-d.elf", Examples.Refine.Diff.ImgD.code, Examples.Refine.Diff.ImgD.segments),
   -- The same binaries in `--format chunks` (NoCompiler/Image.lean, "Code in chunks").
   ("examples/elf/hello.elf", Examples.Chunks.HelloImage.code, Examples.Chunks.HelloImage.segments),
   ("examples/demo/elf/cobs.b.elf", Examples.Chunks.CobsImage.code, Examples.Chunks.CobsImage.segments),
   ("examples/demo/elf/sum.b.elf", Examples.Chunks.SumBImage.code, Examples.Chunks.SumBImage.segments)]

/-- Modules and the layouts their theorems are instantiated at, with the ELF
    each layout is read from (docs/isa/v1.md, criterion 3). -/
def modules : List (String × Module × Layout) :=
  [("examples/elf/sum.link1.elf", Examples.Link.One.module, Examples.Link.One.layout),
   ("examples/elf/sum.link2.elf", Examples.Link.Two.module, Examples.Link.Two.layout)]

/-- The compressed binaries of the demo and their halfword images. Their
    proofs read no data section, so only `.text` is compared. -/
def imagesC : List (String × CCode) :=
  [("examples/demo/elf/sum.a.elf", Demo.Sum.ImageA.code), ("examples/demo/elf/cobs.a.elf", Demo.Cobs.ImageA.code)]

def checkImageC (root : System.FilePath) (path : String) (c : CCode) : IO Bool := do
  let b ← IO.FS.readBinFile (root / path)
  match Elf.sections b with
  | .error e => IO.println s!"FAIL {path}: {e}"; return false
  | .ok secs =>
    let some t := secs.find? (·.name == ".text") | IO.println s!"FAIL {path}: no .text"; return false
    if t.offset + t.size > b.size || t.size % 2 != 0 then
      IO.println s!"FAIL {path}: .text is not whole halfwords inside the file"; return false
    let halves := (List.range (t.size / 2)).map fun i =>
      BitVec.ofNat 16 ((b.get! (t.offset + 2 * i)).toNat + 256 * (b.get! (t.offset + 2 * i + 1)).toNat)
    if BitVec.ofNat 64 t.addr != c.base || halves.toArray != c.halves then
      IO.println s!"FAIL {path}: .text differs from the image"; return false
    IO.println s!"ok   {path}: {c.halves.size} halfwords at {c.base.toNat} match the compressed image"
    return true

def checkImage (root : System.FilePath) (path : String) (c : Code) (segs : List Segment) :
    IO Bool := do
  let bytes ← IO.FS.readBinFile (root / path)
  match Elf.text bytes, Elf.segments bytes with
  | .error e, _ | _, .error e => IO.println s!"FAIL {path}: {e}"; return false
  | .ok t, .ok ds =>
    if t.base != c.base then
      IO.println s!"FAIL {path}: .text at {t.base.toNat}, image at {c.base.toNat}"; return false
    if t.words != c.words then
      IO.println s!"FAIL {path}: .text differs from the image ({t.words.size} words, image {c.words.size})"
      return false
    if ds.map (·.name) != segs.map (·.name) then
      IO.println s!"FAIL {path}: data sections {ds.map (·.name)}, image {segs.map (·.name)}"
      return false
    for (d, g) in ds.zip segs do
      if d != g then
        IO.println s!"FAIL {path}: {d.name} differs from the image (address, size, contents or writability)"
        return false
    let n := (segs.map (·.bytes.size)).foldl (· + ·) 0
    IO.println s!"ok   {path}: {c.words.size} words at {c.base.toNat} and {segs.length} data sections ({n} bytes) match the image"
    return true

/-- The layout an ELF file has: every function symbol's address, every
    section's, and the extent of `.text`. -/
def elfLayout (b : ByteArray) : Except String Layout := do
  let fs ← Elf.funcSymbols b
  let secs ← Elf.sections b
  let t ← Elf.text b
  let addr (s : String) : Word :=
    match fs.find? (·.1 == s) with
    | some (_, v) => BitVec.ofNat 64 v
    | none => match secs.find? (·.name == s) with
      | some sec => BitVec.ofNat 64 sec.addr
      | none => 0
  return { addr, base := t.base, size := t.words.size }

/-- A module and the layout its proofs are instantiated at, against an ELF:
    the layout is the ELF's, the module can be linked there, and linking it
    gives the ELF's `.text` and data, byte for byte. -/
def checkModule (root : System.FilePath) (path : String) (M : Module) (L : Layout) : IO Bool := do
  let b ← IO.FS.readBinFile (root / path)
  match elfLayout b, Elf.text b, Elf.segments b with
  | .error e, _, _ | _, .error e, _ | _, _, .error e => IO.println s!"FAIL {path}: {e}"; return false
  | .ok L₀, .ok t, .ok ds =>
    let syms := M.funcs.map (·.name) ++ M.data.map (·.name)
    if L.base != L₀.base || L.size != L₀.size || syms.any (fun s => L.addr s != L₀.addr s) then
      IO.println s!"FAIL {path}: the layout is not the ELF's"; return false
    if !decide (M.Ok L₀) then
      IO.println s!"FAIL {path}: the module cannot be linked at the ELF's layout (Module.Ok)"; return false
    let c := M.link L₀
    if c.base != t.base || c.words != t.words then
      IO.println s!"FAIL {path}: the module linked at the ELF's layout is not its .text"; return false
    if M.segments L₀ != ds then
      IO.println s!"FAIL {path}: the module's data at the ELF's layout is not its data sections"; return false
    IO.println s!"ok   {path}: the module ({M.funcs.length} functions, {M.data.length} data) linked at the ELF's layout is its .text and data"
    return true

/-- The source roots whose every module the axiom audit covers. -/
def auditRoots : List String := ["NoCompiler", "Examples", "Demo"]

/-- The axiom audit over every module under `auditRoots` (`Audit.audit`). -/
def axiomAudit (root : System.FilePath) : IO Bool := do
  let lean := root / "lean"
  unless ← (lean / "lean-toolchain").pathExists do
    -- A root with binaries only (scripts/core/check-audit-controls.sh's copies).
    IO.println s!"skip axiom audit: {root} has no lean/ source tree (the binaries were checked)"
    return true
  let mods ← Audit.sourceModules lean auditRoots
  let mut ok := true
  for u in ← Audit.debugOptionUses lean mods do
    IO.println s!"FAIL debugging option turned on (it closes goals with sorry): {u}"
    ok := false
  -- The sysroot of the toolchain lean/lean-toolchain names: ask `lean` from
  -- inside lean/ (elan picks the toolchain by directory; outside, it would pick
  -- its default, or none).
  let out ← IO.Process.output { cmd := "lean", args := #["--print-prefix"], cwd := lean }
  if out.exitCode != 0 then
    IO.println s!"FAIL axiom audit: `lean --print-prefix` in {lean}: {out.stderr}"
    return false
  Lean.initSearchPath (System.FilePath.mk (out.stdout.trimAscii.toString))
    [lean / ".lake" / "build" / "lib" / "lean"]
  let env ← try
      Lean.importModules (mods.map ({ module := · })) {}
    catch e =>
      IO.println s!"FAIL axiom audit: a module of the source tree could not be imported (not built?): {e}"
      return false
  let r := Audit.audit env (Std.HashSet.ofArray mods)
  let rels := Audit.bareRefinesRel env (Std.HashSet.ofArray mods)
  for n in rels do
    IO.println s!"FAIL {n} concludes RefinesRel, a refinement without A's run (state it as Refines; decision 3)"
  ok := ok && rels.isEmpty
  for (n, axs) in r.forbidden do
    IO.println s!"FAIL {n} depends on {axs.toList}"
  if r.forbidden.isEmpty then
    IO.println s!"ok   axiom audit: {r.checked} declarations in {mods.size} modules; {r.bvTier.size} in the bv_decide tier, the rest standard"
  IO.println s!"bv_decide tier ({r.bvTier.size} theorems; they rest on native evaluation too, docs/isa/trust.md):"
  for t in r.bvTier do
    IO.println s!"  {t}"
  return ok && r.forbidden.isEmpty

def main (args : List String) : IO UInt32 := do
  let root : System.FilePath := args.headD ".."
  let mut ok := true
  for (p, c, segs) in images do
    ok := (← checkImage root p c segs) && ok
  for (p, c) in imagesC do
    ok := (← checkImageC root p c) && ok
  for (p, M, L) in modules do
    ok := (← checkModule root p M L) && ok
  ok := (← axiomAudit root) && ok
  return if ok then 0 else 1
