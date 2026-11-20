import Examples
import Demo

/-
`lake build nocompiler-audit && lake exe nocompiler-audit` (from lean/): the checks that tie
the proofs to the binaries.

At build time, `#assert_standard_axioms` fails the build if a listed theorem
depends on any axiom beyond Lean's three standard ones (propext,
Classical.choice, Quot.sound): no `sorry`, no `native_decide`, no
`ofReduceBool`, no axiom of our own. At run time, `main` reads each committed ELF file with the
Lean reader in NoCompiler/Elf.lean and checks that its `.text` is word for word the
image the proofs are about, and that every data section (`.rodata`, `.data`,
`.bss`, ...) is byte for byte the exported segment.
-/
open NoCompiler

open Lean Elab Command in
/-- Fail unless the theorem depends on no axiom beyond Lean's standard three. -/
elab "#assert_standard_axioms " id:ident : command => do
  let n ← liftCoreM (realizeGlobalConstNoOverload id)
  let axs ← liftCoreM (Lean.collectAxioms n)
  let bad := axs.filter (fun a => !([``propext, ``Classical.choice, ``Quot.sound].contains a))
  unless bad.isEmpty do throwError "{n} depends on {bad.toList}"

-- The adequacy theorems and the program-logic rules every proof builds on.
#assert_standard_axioms NoCompiler.Exec.hw_safe
#assert_standard_axioms NoCompiler.Exec.hw_final
#assert_standard_axioms NoCompiler.Exec.hw_terminates
#assert_standard_axioms NoCompiler.Reach.bind
#assert_standard_axioms NoCompiler.Reach.loop
#assert_standard_axioms NoCompiler.Reach.exec_step
#assert_standard_axioms NoCompiler.Reach.sys_step
#assert_standard_axioms NoCompiler.Reach.frame
#assert_standard_axioms NoCompiler.VerifiedImg.call
#assert_standard_axioms NoCompiler.VerifiedImg.frame
#assert_standard_axioms NoCompiler.VerifiedImg.hw
-- The structural checker in Lean, and its theorem.
#assert_standard_axioms NoCompiler.Struct.cfi
#assert_standard_axioms NoCompiler.Struct.inv_entry
#assert_standard_axioms Examples.Sum.Image.sum_checked
#assert_standard_axioms Examples.Sum.Image.sum2_checked
#assert_standard_axioms Examples.Hello.Image.write_all_checked
#assert_standard_axioms Examples.Hello.Image.hello_checked

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

-- The examples.
#assert_standard_axioms Examples.Sum.sum_verified
#assert_standard_axioms Examples.Sum.sum_hw
#assert_standard_axioms Examples.Sum2.sum2_verified
#assert_standard_axioms Examples.Hello.write_all_verified
#assert_standard_axioms Examples.Hello.hello_verified
-- Relocation (docs/isa/v1.md): the translation theorem, and sum at every layout and at two.
#assert_standard_axioms NoCompiler.VerifiedImg.shift
#assert_standard_axioms NoCompiler.Verified.of_leaf
#assert_standard_axioms NoCompiler.Module.fetch_link
#assert_standard_axioms NoCompiler.Verified.mono
#assert_standard_axioms Examples.Link.sum_in_any_program
#assert_standard_axioms Examples.Link.same_module
#assert_standard_axioms Examples.Link.sum_relocatable
#assert_standard_axioms Examples.Link.sum_link1
#assert_standard_axioms Examples.Link.sum_link2

-- The demo (demo/README.md): each function on the nocompiler build (B, `VerifiedImg`)
-- and on the ordinary rv64gc build (A, `VerifiedC`, NoCompiler/Ext/Rvc.lean).
#assert_standard_axioms Demo.Sum.sum_b
#assert_standard_axioms Demo.Sum.sum_a
#assert_standard_axioms Demo.Cobs.cobs_b
#assert_standard_axioms Demo.Cobs.cobs_a
#assert_standard_axioms Demo.Sum.ImageB.sum_checked
#assert_standard_axioms Demo.Cobs.ImageB.cobs_decode_checked

/-- Each committed binary (relative to the repository root), and the code
    image and data segments its proofs use. -/
def images : List (String × Code × List Segment) :=
  [("examples/elf/sum.elf", Examples.Sum.Image.code, Examples.Sum.Image.segments),
   ("examples/elf/hello.elf", Examples.Hello.Image.code, Examples.Hello.Image.segments),
   ("examples/demo/elf/sum.b.elf", Demo.Sum.ImageB.code, Demo.Sum.ImageB.segments),
   ("examples/demo/elf/cobs.b.elf", Demo.Cobs.ImageB.code, Demo.Cobs.ImageB.segments)]

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

def main (args : List String) : IO UInt32 := do
  let root : System.FilePath := args.headD ".."
  let mut ok := true
  for (p, c, segs) in images do
    ok := (← checkImage root p c segs) && ok
  for (p, c) in imagesC do
    ok := (← checkImageC root p c) && ok
  for (p, M, L) in modules do
    ok := (← checkModule root p M L) && ok
  return if ok then 0 else 1
